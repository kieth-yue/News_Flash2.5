#!/usr/bin/env python3
"""
港股新聞監控系統 v2 (終極優化版)
- GitHub Actions 長駐掃描 + Gemma 4 31B 聯網 + 飛書卡片推送
- 板塊消息每 session 首輪推送，後續只掃個股
- 去重：個股按「代號+日期」，板塊按「主題關鍵詞+日期」
- 週末機制：FORCE_RUN 一律從上週五 16:00 開始掃
"""
import os
import sys
import json
import time
import random
import re
import base64
import hashlib
import hmac
from datetime import datetime, timedelta, timezone
from pathlib import Path
import yaml
from google import genai
from google.genai import types
import requests
from urllib.parse import urlparse
from opencc import OpenCC
# ============================================================
# 簡體→繁體（香港）轉換器
# ============================================================
_cc = OpenCC('s2hk')
def to_traditional(text):
    """將所有文字統一轉為繁體中文（香港用字），確保飛書輸出一致"""
    if not text:
        return text
    return _cc.convert(text)
# 常量
# ============================================================
HKT = timezone(timedelta(hours=8))
SCRIPT_DIR = Path(__file__).parent
CONFIG_PATH = SCRIPT_DIR / "config.yaml"
LOCK_FILE = SCRIPT_DIR / "run.lock"
WEEKDAY_CN = ["星期一", "星期二", "星期三", "星期四", "星期五", "星期六", "星期日"]
WEEKDAY_EN = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"]
# 板塊標題去重停用詞
MACRO_STOP_WORDS = set(
    "的了在是及與和等將於為對由有個中年月日上下不亦都而但又或被向從"
    "令可能該其這那之以較更最再已正將會要把讓給據稱道表示預計料帶動"
    "受惠影響板塊消息新聞發布時間來源連結摘要利好邏輯股票香港港股恆指"
    "今日昨日當前目前市場資金政策宏觀數據顯示預期維持持續進一步"
    "a the of to in on for and or with is are was were be been has have"
)
# 時間欄位禁止詞（出現即丟棄該條）
TIME_FORBIDDEN_WORDS = [
    "估計", "未詳", "約定", "不詳", "預計時間", "暫定", "待定",
    "未提供", "未給出", "暫未", "不確定", "unknown",
]
# ============================================================
# 配置加載
# ============================================================
DEFAULT_CONFIG = {
    "gemini": {
        "model": "gemma-4-31b-it",
        "timeout_sec": 500,
        "max_retries": 3,
        "retry_wait_sec": 60,
    },
    "sessions": {
        "morning": {"start": "07:00", "end": "10:00", "news_after": "last_trading_day_close"},
        "midday": {"start": "11:00", "end": "13:00", "news_after": "today_06:00"},
        "evening": {"start": "21:30", "end": "03:00", "news_after": "today_16:00"},
    },
    "grace_minutes": 30,
    "scan": {"interval_min_min": 4, "interval_min_max": 7},
    "filters": {
        "max_stock_news": 5,
    },
    "dedup": {"cache_file": "push_cache.json", "expire_days": 2},
    "feishu": {"card_title": "📊 港股新聞監控快訊", "card_color": "wathet"},
}
def load_config():
    """加載 config.yaml，缺失欄位用默認值補齊"""
    cfg = json.loads(json.dumps(DEFAULT_CONFIG))  # deep copy
    if CONFIG_PATH.exists():
        try:
            with open(CONFIG_PATH, "r", encoding="utf-8") as f:
                user_cfg = yaml.safe_load(f) or {}
            for key, val in user_cfg.items():
                if isinstance(val, dict) and isinstance(cfg.get(key), dict):
                    cfg[key].update(val)
                else:
                    cfg[key] = val
        except Exception as e:
            print(f"⚠️ 讀取 config.yaml 失敗，使用默認配置: {e}")
    else:
        print(f"⚠️ 找不到 config.yaml，使用默認配置")
    return cfg
# ============================================================
# 時間工具
# ============================================================
def get_hkt_now():
    return datetime.now(HKT)
def is_weekend(hkt=None):
    hkt = hkt or get_hkt_now()
    return hkt.weekday() >= 5
def get_last_trading_close(hkt):
    """返回最近一個交易日嘅 16:00 HKT。
    週一 → 上週五（3 日前）
    週二至週五 → 尋日（1 日前）
    週六 → 上週五（1 日前）
    週日 → 上週五（2 日前）
    """
    wd = hkt.weekday()
    if wd == 0:    # 週一
        days_back = 3
    elif wd == 6:  # 週日
        days_back = 2
    elif wd == 5:  # 週六
        days_back = 1
    else:          # 週二至週五
        days_back = 1
    base_date = (hkt - timedelta(days=days_back)).date()
    return datetime(base_date.year, base_date.month, base_date.day, 16, 0, tzinfo=HKT)
def get_session(hkt, config):
    grace = config.get("grace_minutes", 30)
    # 第一輪：精確匹配（喺 session 實際時間範圍內）
    for name, s in config["sessions"].items():
        sh, sm = map(int, s["start"].split(":"))
        eh, em = map(int, s["end"].split(":"))
        start_dt = hkt.replace(hour=sh, minute=sm, second=0, microsecond=0)
        end_dt = hkt.replace(hour=eh, minute=em, second=0, microsecond=0)
        if eh <= sh:  # 跨午夜
            if hkt >= start_dt or hkt <= end_dt:
                return name
        else:
            if start_dt <= hkt <= end_dt:
                return name
    # 第二輪：grace 寬限期匹配
    for name, s in config["sessions"].items():
        sh, sm = map(int, s["start"].split(":"))
        eh, em = map(int, s["end"].split(":"))
        start_dt = hkt.replace(hour=sh, minute=sm, second=0, microsecond=0)
        end_dt = hkt.replace(hour=eh, minute=em, second=0, microsecond=0)
        grace_end = end_dt + timedelta(minutes=grace)
        if eh <= sh:  # 跨午夜
            if hkt >= start_dt or hkt <= grace_end:
                return name
        else:
            if start_dt <= hkt <= grace_end:
                return name
    return None
def is_session_over(session_name, hkt, config):
    s = config["sessions"].get(session_name)
    if not s:
        return True
    sh, sm = map(int, s["start"].split(":"))
    eh, em = map(int, s["end"].split(":"))
    end_dt = hkt.replace(hour=eh, minute=em, second=0, microsecond=0)
    if eh <= sh:  # 跨午夜 session（如 21:30-03:00）
        if hkt.hour >= sh:
            # 晚間時段（21:00-23:59），session 剛開始，未結束
            return False
        # 凌晨時段：過咗 end 時間就結束
        return hkt >= end_dt
    else:
        # 普通 session
        if hkt.hour < sh:
            return True
        return hkt >= end_dt
def get_force_run_session(hkt):
    """FORCE_RUN 模式：根據當前時間推斷 session。
    週末一律當 morning（用 last_trading_day_close → 上週五 16:00）。
    """
    if hkt.weekday() >= 5:
        return "morning"
    h, m = hkt.hour, hkt.minute
    t = h * 60 + m
    if t < 3 * 60:         # 00:00 - 03:00 → 晚間延續（新聞從尋日16:00開始）
        return "evening"
    elif t < 10 * 60:      # 03:00 - 10:00 → 早市規則
        return "morning"
    elif t < 16 * 60:      # 10:00 - 16:00 → 午市規則
        return "midday"
    else:                  # 16:00 - 24:00 → 晚間規則
        return "evening"
def calc_news_after(session_name, hkt, config):
    """計算新聞有效起始時間。
    週末（星期六/日）一律從上週五 16:00 開始，無論邊個 session。
    """
    if session_name is None:
        session_name = get_force_run_session(hkt)
    # 週末：一律由上週五收市開始
    if hkt.weekday() >= 5:
        return get_last_trading_close(hkt)
    na_type = config["sessions"][session_name]["news_after"]
    if na_type == "last_trading_day_close":
        return get_last_trading_close(hkt)
    # 支援 today_HH:MM 通用格式，例如 today_11:00、today_09:30
    m = re.match(r'^today_(\d{1,2}):(\d{2})$', str(na_type))
    if m:
        news_after = hkt.replace(hour=int(m.group(1)), minute=int(m.group(2)),
                                 second=0, microsecond=0)
        # 跨午夜修正：如果目標時間喺未來（例如 01:00 問 today_16:00），減一日
        if news_after > hkt:
            news_after -= timedelta(days=1)
        return news_after
    else:
        return hkt - timedelta(hours=24)
def format_hkt(dt):
    return dt.strftime("%Y-%m-%d %H:%M HKT")
def get_time_injection(now_hkt, news_after, session_name):
    wd_cn = WEEKDAY_CN[now_hkt.weekday()]
    is_wknd = now_hkt.weekday() >= 5
    if is_wknd:
        s_name = "週末掃描（上週五收市後至今）"
    else:
        session_names = {"morning": "早市時段（06:00-11:00）",
                         "midday": "午市時段（11:00-15:00）",
                         "evening": "晚間時段（21:30-03:00）"}
        s_name = session_names.get(session_name, "測試模式")
    return (
        f"\n---\n"
        f"【當前香港時間】{now_hkt.strftime('%Y-%m-%d')}（{wd_cn}）{now_hkt.strftime('%H:%M')} HKT\n"
        f"【新聞有效時間範圍】{format_hkt(news_after)} 至 {format_hkt(now_hkt)}\n"
        f"【掃描時段】{s_name}\n"
        f"\n"
        f"⚠️ 時效鐵律（必須嚴格遵守）：\n"
        f"- 只輸出在上述「新聞有效時間範圍」內發布嘅新聞\n"
        f"- 早於範圍嘅消息視為已消化，禁止輸出\n"
        + ("- 而家係週末，請掃描上週五收市後至現在嘅所有重大消息\n" if is_wknd else "")
        + f"- ⏰ 發布時間必須係從聯網搜尋結果確認嘅真實時間\n"
        f"- 禁止使用「估計」「未詳」「約定時間」「待定」等不確定表述\n"
        f"- 時間無法確定嘅新聞直接捨棄，不要輸出\n"
    )
# ============================================================
# 飛書推送
# ============================================================
def gen_feishu_sign(timestamp, secret):
    string_to_sign = f"{timestamp}\n{secret}"
    hmac_code = hmac.new(string_to_sign.encode("utf-8"), digestmod=hashlib.sha256).digest()
    return base64.b64encode(hmac_code).decode("utf-8")
def send_feishu(raw_text, config):
    fs = config["feishu"]
    webhook = os.getenv("FEISHU_WEBHOOK", "")
    secret = os.getenv("FEISHU_SECRET", "")
    now_hkt = get_hkt_now()
    date_str = now_hkt.strftime("%Y-%m-%d")
    time_str = now_hkt.strftime("%Y-%m-%d %H:%M HKT")
    if not webhook:
        print("❌ FEISHU_WEBHOOK 未設置，跳過推送")
        return -1
    payload = {
        "msg_type": "interactive",
        "card": {
            "config": {"wide_screen_mode": True},
            "header": {
                "title": {"tag": "plain_text", "content": f"{fs['card_title']} | {date_str}"},
                "template": fs["card_color"],
            },
            "elements": [
                {"tag": "div", "text": {"tag": "lark_md", "content": raw_text}},
                {"tag": "hr"},
                {"tag": "note", "elements": [
                    {"tag": "plain_text", "content": f"⏰ 推送時間：{time_str}"}
                ]},
            ],
        },
    }
    if secret:
        ts = str(int(time.time()))
        payload["timestamp"] = ts
        payload["sign"] = gen_feishu_sign(ts, secret)
    for attempt in range(3):
        try:
            r = requests.post(webhook, json=payload, timeout=30)
            resp = r.json()
            if r.status_code == 200 and resp.get("code", 0) == 0:
                print(f"✅ 飛書推送成功 (attempt {attempt + 1})")
                return 200
            else:
                print(f"❌ 飛書推送失敗: status={r.status_code}, resp={resp}")
        except Exception as e:
            print(f"❌ 飛書推送異常 (attempt {attempt + 1}): {e}")
        if attempt < 2:
            time.sleep(3)
    return -1
# ============================================================
# 文本處理
# ============================================================
def normalize_stock_codes(text):
    text = re.sub(r'HK\.(\d{1,5})(?!\d)', lambda m: f"{m.group(1).zfill(5)}.HK", text)
    text = re.sub(r'(?<!\d)(\d{1,5})\.HK(?!\d)', lambda m: f"{m.group(1).zfill(5)}.HK", text)
    return text
def format_links(text):
    def link_replacer(m):
        urls = re.findall(r'https?://[^\s\)\]]+', m.group(0))
        if urls:
            return f"🔗 連結：[點擊查看]({urls[0]})"
        return ""
    pattern = r'🔗 連結：[\s\S]*?(?=\n[💡🏷️📰⏰📌]|\n===|\Z)'
    text = re.sub(pattern, link_replacer, text)
    def raw_url_replacer(m):
        return f"[點擊查看]({m.group(0)})"
    text = re.sub(r'(?<![\(\]])https?://[^\s\)\]]+', raw_url_replacer, text)
    text = re.sub(r'\n{3,}', '\n\n', text)
    return text.strip()
# ============================================================
# 快取與去重
# ============================================================
def cache_path(config):
    return SCRIPT_DIR / config["dedup"]["cache_file"]
def load_cache(config):
    path = cache_path(config)
    if not path.exists():
        try:
            with open(path, "w", encoding="utf-8") as f:
                json.dump({"stock": {}, "macro": {}}, f, ensure_ascii=False, indent=2)
        except Exception:
            pass
        return {"stock": {}, "macro": {}}
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
            if "stock" not in data: data["stock"] = {}
            if "macro" not in data: data["macro"] = {}
            return data
    except Exception:
        return {"stock": {}, "macro": {}}
def save_cache(cache, config):
    try:
        with open(cache_path(config), "w", encoding="utf-8") as f:
            json.dump(cache, f, ensure_ascii=False, indent=2)
    except Exception as e:
        print(f"⚠️ 寫入快取失敗: {e}")
def cleanup_cache(cache, config):
    expire_days = config["dedup"]["expire_days"]
    cutoff = (get_hkt_now() - timedelta(days=expire_days)).strftime("%Y-%m-%d")
    total_expired = 0
    expired = [k for k in cache["stock"] if k.split("|")[-1] < cutoff]
    for k in expired: del cache["stock"][k]
    total_expired += len(expired)
    expired = [k for k in cache["macro"] if k < cutoff]
    for k in expired: del cache["macro"][k]
    total_expired += len(expired)
    if total_expired:
        print(f"🧹 清除 {total_expired} 條過期快取")
MACRO_TOPIC_GROUPS = [
    {"油價", "原油", "布油", "美油", "石油", "霍爾木茲", "中東", "地緣", "停火", "美伊", "以色列", "伊朗", "也門", "海峽", "煉油", "天然氣"},
    {"加息", "減息", "降準", "利率", "美聯儲", "聯儲", "央行", "逆回購", "流動性", "通脹", "通膨", "CPI", "PPI", "寬鬆", "貨幣政策"},
    {"內房", "地產", "房企", "樓市", "房地產", "住房", "物業"},
    {"人工智能", "芯片", "半導體", "晶圓", "算力", "大模型", "AI", "GPU", "英偉達", "輝達", "NVIDIA"},
    {"新能源車", "電動車", "比亞迪", "充電", "鋰電", "光伏"},
    {"關稅", "貿易戰", "制裁", "出口管制", "貿易壁壘"},
]
def extract_keywords(text):
    cleaned = re.sub(r'[^\w\u4e00-\u9fff]', ' ', text)
    keywords = set()
    for w in re.findall(r'[a-zA-Z]{2,}', cleaned):
        wl = w.lower()
        if wl not in MACRO_STOP_WORDS: keywords.add(wl)
    for segment in re.findall(r'[\u4e00-\u9fff]+', cleaned):
        for i in range(len(segment) - 1):
            bg = segment[i:i + 2]
            if bg not in MACRO_STOP_WORDS: keywords.add(bg)
    return keywords
def _topic_group(text):
    for i, group in enumerate(MACRO_TOPIC_GROUPS):
        if any(kw in text for kw in group): return i
    return -1
def is_duplicate_macro(title, macro_cache, date_str):
    new_kw = extract_keywords(title)
    if not new_kw: return False
    new_topic = _topic_group(title)
    existing = macro_cache.get(date_str, [])
    for old_kw_list in existing:
        old_kw = set(old_kw_list)
        if not old_kw: continue
        overlap = new_kw & old_kw
        min_len = min(len(new_kw), len(old_kw))
        ratio = len(overlap) / min_len if min_len > 0 else 0
        if new_topic >= 0 and len(overlap) >= 2: return True
        if len(overlap) >= 3 and ratio >= 0.35: return True
    return False
def add_macro_keyword(title, macro_cache, date_str):
    kw = list(extract_keywords(title))
    if kw: macro_cache.setdefault(date_str, []).append(kw)
# ============================================================
# 個股標題去重（防止同一單新聞被不同媒體轉載時重複推送）
# ============================================================
def normalize_stock_title(title):
    """標準化標題：去除代號、括號、標點、空白，用於相似度比對"""
    t = re.sub(r'[\(（]\d{4,5}[\)）]', '', title)
    t = re.sub(r'\d{5}\.HK', '', t, flags=re.IGNORECASE)
    t = re.sub(r'[^\w\u4e00-\u9fff]', '', t)
    return t.lower()
def is_duplicate_stock_title(title, code, pushed_titles):
    """檢查同一隻股票嘅標題是否同已推送嘅相似"""
    norm = normalize_stock_title(title)
    if len(norm) < 6: return False
    for old_code, old_norm in pushed_titles:
        if old_code != code: continue
        if norm in old_norm or old_norm in norm: return True
        if len(norm) >= 8 and len(old_norm) >= 8:
            shorter = min(len(norm), len(old_norm))
            common = sum(1 for a, b in zip(norm, old_norm) if a == b)
            if common / shorter >= 0.75: return True
    return False
# ============================================================
# 進程鎖
# ============================================================
def acquire_lock():
    now_ts = time.time()
    if LOCK_FILE.exists():
        try:
            ts = float(LOCK_FILE.read_text().strip())
            if (now_ts - ts) > 30 * 60:
                LOCK_FILE.unlink()
            else:
                return False
        except Exception:
            try: LOCK_FILE.unlink()
            except Exception: pass
    try:
        LOCK_FILE.write_text(str(now_ts))
        return True
    except Exception:
        return False
def release_lock():
    try:
        if LOCK_FILE.exists(): LOCK_FILE.unlink()
    except Exception: pass
# ============================================================
# Gemini 調用
# ============================================================
def is_retryable_error(e):
    err = str(e).lower()
    return any(kw in err for kw in [
        "429", "rate limit", "rate_limit", "resource exhausted", "quota",
        "timeout", "timed out", "deadline exceeded", "503", "502", "500", "unavailable",
        "server disconnected", "remoteprotocolerror", "connection reset", "connection error"
    ])
def is_daily_quota_exhausted(e):
    return "exceeded your current quota" in str(e).lower()
def extract_grounding_urls(response):
    urls = []
    try:
        if not response.candidates: return urls
        meta = getattr(response.candidates[0], "grounding_metadata", None)
        if not meta: return urls
        chunks = getattr(meta, "grounding_chunks", None)
        if not chunks: return urls
        for chunk in chunks:
            web = getattr(chunk, "web", None)
            if web:
                uri = getattr(web, "uri", "")
                title = getattr(web, "title", "來源")
                if uri: urls.append((title, uri))
    except Exception as e:
        print(f"⚠️ 提取 grounding URL 失敗: {e}")
    return urls
def count_source_domains(grounding_urls):
    domains = set()
    vertex_count = 0
    for _, uri in grounding_urls:
        try:
            parsed = urlparse(uri)
            domain = parsed.netloc.lower().replace("www.", "")
            if not domain: continue
            if "vertexaisearch" in domain: vertex_count += 1
            elif "google.com" not in domain: domains.add(domain)
        except Exception: continue
    return sorted(domains), vertex_count
SYSTEM_INSTRUCTION = (
    "你係港股新聞分析員。你必須嚴格按照用戶指定嘅格式輸出，"
    "所有內容（包括新聞標題、摘要、來源名稱）必須一律使用繁體中文（香港用字），"
    "即使新聞原文係簡體中文，都必須轉換為繁體中文先可以輸出。"
    "禁止使用 Markdown 標題（**文字**）、項目符號（* 或 -）、編號列表、英文分析散文。"
    "你嘅回應只能包含指定嘅 section 標記（=== 【...】 ===）同 📰 新聞條目，"
    "或者「當前時段無符合條件」聲明，不得有任何前言、分析、解釋、後語。"
)
_gemini_client = None
def get_gemini_client(config):
    global _gemini_client
    if _gemini_client is None:
        gcfg = config["gemini"]
        _gemini_client = genai.Client(
            api_key=os.getenv("GEMINI_API_KEY", ""),
            http_options=types.HttpOptions(timeout=gcfg["timeout_sec"] * 1000),
        )
    return _gemini_client
def gemini_call(prompt, config, chat=None):
    gcfg = config["gemini"]
    client = get_gemini_client(config)
    gen_config = types.GenerateContentConfig(
        temperature=0.2,
        system_instruction=SYSTEM_INSTRUCTION,
        tools=[types.Tool(google_search=types.GoogleSearch())],
    )
    quota_429_streak = 0
    for attempt in range(gcfg["max_retries"]):
        try:
            if chat is None:
                chat = client.chats.create(model=gcfg["model"], config=gen_config)
            response = chat.send_message(prompt)
            grounding = extract_grounding_urls(response)
            return response.text or "", grounding, chat, False
        except Exception as e:
            if is_daily_quota_exhausted(e):
                quota_429_streak += 1
                if quota_429_streak >= 2:
                    print(f"🚫 確認 RPD 已用盡: {str(e)[:200]}")
                    return "", [], chat, True
                wait = gcfg["retry_wait_sec"]
                print(f"⚠️ Gemini 配額 429 可能係 RPM 限制，{wait}s 後重試: {str(e)[:150]}")
                time.sleep(wait)
                continue
            quota_429_streak = 0
            if is_retryable_error(e) and attempt < gcfg["max_retries"] - 1:
                wait = gcfg["retry_wait_sec"] * (attempt + 1)
                print(f"⚠️ Gemini 調用失敗，{wait}s 後重試: {str(e)[:150]}")
                time.sleep(wait)
            else:
                print(f"❌ Gemini 調用最終失敗: {str(e)[:200]}")
                return None, [], chat, False
    return None, [], chat, False
# ============================================================
# 新聞解析
# ============================================================
def split_sections(text):
    macro_text = stock_text = ""
    macro_marker = "=== 【板塊宏觀消息】 ==="
    if "=== 【個股重大利好】 ===" in text:
        stock_marker = "=== 【個股重大利好】 ==="
    else:
        stock_marker = "=== 【個股重大利好/異動】 ==="
    if stock_marker in text and macro_marker in text:
        parts = text.split(stock_marker)
        stock_text = parts[1] if len(parts) > 1 else ""
        macro_parts = parts[0].split(macro_marker)
        macro_text = macro_parts[1] if len(macro_parts) > 1 else ""
    elif stock_marker in text:
        parts = text.split(stock_marker)
        stock_text = parts[1] if len(parts) > 1 else ""
    elif macro_marker in text:
        parts = text.split(macro_marker)
        macro_text = parts[1] if len(parts) > 1 else ""
    return macro_text.strip(), stock_text.strip()
def parse_entries(section_text):
    if not section_text or "📰" not in section_text: return []
    raw_entries = re.split(r'(?=📰)', section_text)
    return [e.strip() for e in raw_entries if e.strip() and "📰" in e]
def extract_field(entry, emoji):
    m = re.search(rf'{emoji}\s*[^\n：:]*[：:]\s*([^\n]*)', entry)
    return m.group(1).strip() if m else ""
def extract_url_from_entry(entry):
    urls = re.findall(r'https?://[^\s\)\]]+', entry)
    return urls[0] if urls else ""
def parse_entry_time(entry):
    m = re.search(r'⏰[^\n]*', entry)
    if not m: return None, False
    time_line = m.group(0)
    for word in TIME_FORBIDDEN_WORDS:
        if word in time_line: return None, False
    dt_match = re.search(r'(\d{4})-(\d{1,2})-(\d{1,2})\s+(\d{1,2}):(\d{2})', time_line)
    if dt_match:
        try:
            y, mo, d, h, mi = map(int, dt_match.groups())
            return datetime(y, mo, d, h, mi, tzinfo=HKT), True
        except ValueError: return None, False
    return None, False
def is_no_news(text):
    markers = ["無符合條件", "冇符合條件", "无符合条件", "無具催化力", "无具催化力",
               "沒有符合條件", "無重大", "无重大", "冇重大"]
    return any(kw in text for kw in markers)
# ============================================================
# 核心掃描
# ============================================================
def scan_once(session_name, turn_count, macro_pushed, stock_pushed, config, prompts):
    macro_prompt, stock_prompt = prompts
    now_hkt = get_hkt_now()
    date_str = now_hkt.strftime("%Y-%m-%d")
    news_after = calc_news_after(session_name, now_hkt, config)
    cache = load_cache(config)
    cleanup_cache(cache, config)
    time_info = get_time_injection(now_hkt, news_after, session_name)
    format_reminder = (
        "\n⚠️ 最終格式檢查（違反即不合格）：\n"
        "- 回應只能包含「=== 【板塊宏觀消息】 ===」同「=== 【個股重大利好】 ===」區塊\n"
        "- 每條新聞必須以 📰 開頭，逐行使用 📰🏷️⏰📌🔗💡 欄位\n"
        "- 禁止 Markdown 標題、項目符號、編號列表、英文分析散文\n"
        "- 無新聞時直接輸出「當前時段無符合條件之板塊消息」或「當前時段無符合條件之重大利好」\n"
        "- 🚨 股票配對規則（極其重要）：🏷️ 股票嘅名稱同代號必須係新聞嘅主角，"
        "並且必須喺新聞標題或正文中明確出現。嚴禁將一篇講述多隻股票嘅大市摘要/新聞合集"
        "（如「港股公告精選」「夜期低水」「早知道」等）拆分為多條個股新聞，"
        "除非該文章有獨立段落專門講述嗰隻股票並包含具體財務數據。"
        "如果一篇文章同時提及幾隻股票但冇逐一詳述，只能揀最相關嘅一隻，或者全部唔輸出。\n"
        "- 🚨 每條新聞嘅 🔗 連結必須指向該新聞嘅原始頁面，唔同新聞嚴禁共用同一個連結。"
    )
    if turn_count == 1 and macro_prompt:
        prompt = (f"{macro_prompt}\n\n---\n\n{stock_prompt}{time_info}"
                  f"\n【掃描模式】首輪掃描，請先輸出「=== 【板塊宏觀消息】 ===」，再輸出「=== 【個股重大利好】 ===」。{format_reminder}")
    else:
        prompt = (f"{stock_prompt}{time_info}"
                  f"\n【掃描模式】盤中輪詢掃描，只輸出「=== 【個股重大利好】 ===」。"
                  f"若盤中出現突發黑天鵝級宏觀事件，可在最前面輸出「=== 【板塊宏觀消息】 ===」緊急警報。{format_reminder}")
    # 強制觸發搜尋指令
    prompt += (
        f"\n\n🛑 【立即行動指令】：請你立刻使用 Google Search 工具，"
        f"搜尋 {now_hkt.strftime('%Y-%m-%d')} 嘅最新港股公告及宏觀新聞！"
        f"在未取得真實搜尋結果前，絕對禁止直接輸出「無符合條件」。請開始搜尋："
    )
    llm_result, grounding_urls, chat, quota_exhausted = gemini_call(prompt, config)
    if quota_exhausted: return "quota_exhausted"
    if llm_result is None:
        print("⏭️ 伺服器失敗，跳過本輪，等待下一輪")
        return False
    llm_result = to_traditional(llm_result)
    print(f"=== Gemini 回應 ({len(llm_result)} 字元) ===")
    print(llm_result[:2000])
    if grounding_urls:
        source_domains, vertex_count = count_source_domains(grounding_urls)
        total_sources = len(source_domains) + vertex_count
        print(f"🔗 Grounding 來源: {len(grounding_urls)} 個 URL，{total_sources} 個搜尋結果")
    else:
        text_urls = re.findall(r'https?://vertexaisearch\.cloud\.google\.com/[^\s\)\]]+', llm_result)
        grounding_urls = [("來源", u) for u in text_urls] if text_urls else []
        source_domains, vertex_count = [], len(text_urls)
        total_sources = vertex_count
    source_summary = (f"{len(source_domains)} 個新聞源：{', '.join(source_domains)}"
                      if source_domains else
                      (f"{vertex_count} 個 Google 搜尋結果" if vertex_count else ""))
    # 動態追問：冇搜尋就答無新聞 → 開新對話強制搜尋
    if total_sources == 0 and "📰" not in llm_result:
        print("⚠️ Gemini 冇使用搜尋工具就答無新聞，開新請求強制搜尋...")
        time.sleep(3)
        search_month = now_hkt.strftime("%Y年%m月")
        search_today = now_hkt.strftime("%Y年%m月%d日")
        followup = (
            f"{prompt}\n\n"
            f"🚨 警告：你剛才未能成功調用聯網搜尋。請你作為盡責嘅分析員，"
            f"立即呼叫 Google 搜尋工具，搜尋 {search_today} 嘅最新資訊。關鍵詞建議：\n"
            f"1. 港股 盈喜 {search_month}\n"
            f"2. 港股 業績 淨利潤 大增 {search_month}\n"
            f"3. site:cls.cn 港股 公告 {search_today}\n"
            f"搜尋後請嚴格按格式輸出結果。絕對禁止唔搜尋就答無新聞！"
        )
        llm_result, grounding_urls, chat, quota_exhausted = gemini_call(followup, config, chat=None)
        if quota_exhausted: return "quota_exhausted"
        if llm_result is None:
            print("⏭️ 重試都係失敗，跳過本輪")
            return False
        llm_result = to_traditional(llm_result)
        print(f"=== 重試回應 ({len(llm_result)} 字元) ===")
        print(llm_result[:2000])
        if grounding_urls:
            source_domains, vertex_count = count_source_domains(grounding_urls)
            source_summary = (f"{len(source_domains)} 個新聞源：{', '.join(source_domains)}"
                              if source_domains else f"{vertex_count} 個 Google 搜尋結果")
    if not ("【板塊宏觀消息】" in llm_result or "【個股重大利好" in llm_result) and "📰" not in llm_result:
        return False
    if is_no_news(llm_result) and "📰" not in llm_result:
        return False
    llm_result = normalize_stock_codes(llm_result)
    macro_text, stock_text = split_sections(llm_result)
    # 去重 URL，保持順序
    raw_urls = [uri for _, uri in grounding_urls if "vertexaisearch" not in uri] or [uri for _, uri in grounding_urls]
    real_urls = list(dict.fromkeys(raw_urls))
    url_idx = 0
    used_urls = set()
    def get_url_for_entry(entry_text):
        nonlocal url_idx
        url = extract_url_from_entry(entry_text)
        if url and "vertexaisearch" not in url and len(url) < 300 and url not in used_urls:
            used_urls.add(url)
            return url
        while url_idx < len(real_urls):
            u = real_urls[url_idx]
            url_idx += 1
            if u not in used_urls:
                used_urls.add(u)
                return u
        return url if url and "vertexaisearch" not in url else None
    # ---- 板塊消息處理 ----
    macro_entries = []
    for entry in parse_entries(macro_text):
        title = extract_field(entry, "📰 新聞標題") or entry[:60]
        news_time, valid = parse_entry_time(entry)
        if not valid or (news_time and (news_time < news_after or news_time > now_hkt + timedelta(minutes=10))): continue
        if is_duplicate_macro(title, cache["macro"], date_str) or title in macro_pushed: continue
        url = get_url_for_entry(entry)
        if url: entry = re.sub(r'🔗 連結：[\s\S]*?(?=\n[💡🏷️📰⏰📌]|\Z)', f"🔗 連結：{url}", entry, flags=re.MULTILINE)
        macro_entries.append(entry)
        macro_pushed.add(title)
        add_macro_keyword(title, cache["macro"], date_str)
    # ---- 個股消息處理 ----
    stock_entries = []
    stock_dedup_info = []  # (dedup_key, title, code, norm_title) 截斷後先寫入快取
    for entry in parse_entries(stock_text):
        title = extract_field(entry, "📰 新聞標題") or entry[:60]
        stock_field = extract_field(entry, "🏷️ 股票")
        code_match = re.search(r'(\d{5})\.HK', stock_field) or re.search(r'(\d{5})\.HK', entry)
        if not code_match: continue
        code = f"{code_match.group(1)}.HK"
        news_time, valid = parse_entry_time(entry)
        if not valid or (news_time and (news_time < news_after or news_time > now_hkt + timedelta(minutes=10))): continue
        news_date = news_time.strftime("%Y-%m-%d") if news_time else date_str
        dedup_key = f"{code}|{news_date}"
        # 三重去重：檔案快取 + 記憶體 set + 標題相似度
        if dedup_key in cache["stock"]: continue
        if dedup_key in stock_pushed["keys"]: continue
        if is_duplicate_stock_title(title, code, stock_pushed["titles"]): continue
        url = get_url_for_entry(entry)
        if url: entry = re.sub(r'🔗 連結：[\s\S]*?(?=\n[💡🏷️📰⏰📌]|\Z)', f"🔗 連結：{url}", entry, flags=re.MULTILINE)
        stock_entries.append(entry)
        stock_dedup_info.append((dedup_key, title[:100], code, normalize_stock_title(title)))
    if len(stock_entries) > config["filters"]["max_stock_news"]:
        stock_entries = stock_entries[:config["filters"]["max_stock_news"]]
        stock_dedup_info = stock_dedup_info[:config["filters"]["max_stock_news"]]
    # 只將實際推送嘅新聞寫入去重快取，被截斷嘅保留俾下一輪
    for dedup_key, short_title, code, norm_title in stock_dedup_info:
        cache["stock"][dedup_key] = short_title
        stock_pushed["keys"].add(dedup_key)
        stock_pushed["titles"].append((code, norm_title))
    if not macro_entries and not stock_entries:
        save_cache(cache, config)
        return False
    parts = []
    if macro_entries: parts.extend(["=== 【板塊宏觀消息】 ===", "\n\n".join(macro_entries)])
    if stock_entries: parts.extend(["=== 【個股重大利好】 ===", "\n\n".join(stock_entries)])
    final_text = format_links("\n\n".join(parts))
    if source_summary: final_text += f"\n\n---\n📡 本次搜尋咗 {source_summary}"
    send_feishu(final_text, config)
    save_cache(cache, config)
    return True
# ============================================================
# 主流程
# ============================================================
def main():
    config = load_config()
    now_hkt = get_hkt_now()
    force_run = os.getenv("FORCE_RUN", "false").lower() == "true"
    print("=" * 60)
    print(f"=== HKT 現在時間: {now_hkt.strftime('%Y-%m-%d %H:%M:%S')} {WEEKDAY_CN[now_hkt.weekday()]} ===")
    print("=" * 60)
    macro_prompt = os.getenv("HK_NEWS_PROMPT_MACRO", "").strip()
    stock_prompt = os.getenv("HK_NEWS_PROMPT_STOCK", "").strip()
    if not stock_prompt:
        print("❌ HK_NEWS_PROMPT_STOCK 未設置，請喺 GitHub Variables 配置")
        sys.exit(1)
    if force_run:
        session_name = get_force_run_session(now_hkt)
        news_after = calc_news_after(session_name, now_hkt, config)
        print(f"⚠️ FORCE_RUN 模式：模擬 {session_name} session，即時跑一次")
        print(f"=== 新聞有效範圍: {format_hkt(news_after)} ~ {format_hkt(now_hkt)} ===")
        run_mode = "one_shot"
    else:
        if is_weekend(now_hkt):
            print("ℹ️ 週末，自動退出（週末請用 FORCE_RUN 手動觸發）")
            return
        session_name = get_session(now_hkt, config)
        if not session_name:
            print("ℹ️ 唔在任何執行窗口，退出")
            return
        run_mode = "long_run"
        news_after = calc_news_after(session_name, now_hkt, config)
        s = config["sessions"][session_name]
        print(f"=== Session: {session_name} ({s['start']}-{s['end']}) ===")
        print(f"=== 新聞有效範圍: {format_hkt(news_after)} ~ {format_hkt(now_hkt)} ===")
    if not acquire_lock():
        print("⚠️ 已有另一個實例在執行，跳過")
        return
    try:
        if run_mode == "one_shot":
            try: scan_once(session_name, 1, set(), {"keys": set(), "titles": []}, config, (macro_prompt, stock_prompt))
            except Exception as e: print(f"❌ 掃描異常: {str(e)[:300]}")
        elif run_mode == "long_run":
            turn = 0
            macro_pushed = set()
            stock_pushed = {"keys": set(), "titles": []}
            while True:
                turn += 1
                turn_start = get_hkt_now()
                print(f"\n{'─' * 50}\n--- Turn {turn} | {turn_start.strftime('%H:%M:%S')} HKT ---\n{'─' * 50}")
                try:
                    result = scan_once(session_name, turn, macro_pushed, stock_pushed, config, (macro_prompt, stock_prompt))
                    if result == "quota_exhausted":
                        print("\n🚫 Gemini 每日配額已用盡，提早結束 session")
                        break
                except Exception as e:
                    print(f"❌ 本輪異常，跳過: {str(e)[:200]}")
                if is_session_over(session_name, get_hkt_now(), config):
                    print(f"\n🏁 已到 session 結束時間，退出迴圈")
                    break
                sleep_sec = random.randint(config["scan"]["interval_min_min"] * 60, config["scan"]["interval_min_max"] * 60)
                next_run = get_hkt_now() + timedelta(seconds=sleep_sec)
                print(f"💤 休眠 {sleep_sec // 60} 分 {sleep_sec % 60} 秒，下一輪約 {next_run.strftime('%H:%M')} HKT")
                time.sleep(sleep_sec)
    finally:
        release_lock()
if __name__ == "__main__":
    main()
