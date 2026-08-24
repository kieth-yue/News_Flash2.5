#!/usr/bin/env python3
"""
港股新聞監控系統 v2
- GitHub Actions 長駐掃描 + gemini-2.5-flash 聯網 + 飛書卡片推送
- 板塊消息每 session 首輪推送，後續只掃個股
- 去重：個股按「代號+日期」，板塊按「主題關鍵詞+日期」
- 所有格式規則由 GitHub Variables 嘅 prompt 控制
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
# ============================================================
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
        "evening": {"start": "21:30", "end": "23:00", "news_after": "today_16:00"},
    },
    "grace_minutes": 30,
    "scan": {"interval_min_min": 8, "interval_min_max": 10},
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
            # 淺層合併（兩層）
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
def get_session(hkt, config):
    """判斷當前屬於邊個 session，返回 session name 或 None（含 grace 容錯）"""
    grace = config.get("grace_minutes", 30)
    for name, s in config["sessions"].items():
        sh, sm = map(int, s["start"].split(":"))
        eh, em = map(int, s["end"].split(":"))
        start_dt = hkt.replace(hour=sh, minute=sm, second=0, microsecond=0)
        end_dt = hkt.replace(hour=eh, minute=em, second=0, microsecond=0)
        grace_end = end_dt + timedelta(minutes=grace)
        if start_dt <= hkt <= grace_end:
            return name
    return None
def is_session_over(session_name, hkt, config):
    """判斷 session 係咪到結束時間（唔計 grace）"""
    s = config["sessions"].get(session_name)
    if not s:
        return True
    eh, em = map(int, s["end"].split(":"))
    end_dt = hkt.replace(hour=eh, minute=em, second=0, microsecond=0)
    return hkt >= end_dt
def get_force_run_session(hkt):
    """FORCE_RUN 模式：根據當前時間推斷最接近嘅 session，用佢嘅新聞時間範圍"""
    h, m = hkt.hour, hkt.minute
    t = h * 60 + m
    if t < 10 * 60:        # 00:00 - 10:00 → 早市規則
        return "morning"
    elif t < 13 * 60:      # 10:00 - 13:00 → 午市規則
        return "midday"
    else:                  # 13:00 - 24:00 → 晚間規則
        return "evening"
def calc_news_after(session_name, hkt, config):
    """計算新聞有效起始時間"""
    if session_name is None:
        session_name = get_force_run_session(hkt)
    na_type = config["sessions"][session_name]["news_after"]
    if na_type == "last_trading_day_close":
        # 週一追溯至週五，其餘日子尋日
        days_back = 3 if hkt.weekday() == 0 else 1
        base_date = (hkt - timedelta(days=days_back)).date()
        return datetime(base_date.year, base_date.month, base_date.day, 16, 0, tzinfo=HKT)
    elif na_type == "today_06:00":
        return hkt.replace(hour=6, minute=0, second=0, microsecond=0)
    elif na_type == "today_16:00":
        return hkt.replace(hour=16, minute=0, second=0, microsecond=0)
    else:
        return hkt - timedelta(hours=24)
def format_hkt(dt):
    return dt.strftime("%Y-%m-%d %H:%M HKT")
def get_time_injection(now_hkt, news_after, session_name):
    """生成注入 prompt 嘅時間資訊"""
    wd_cn = WEEKDAY_CN[now_hkt.weekday()]
    wd_en = WEEKDAY_EN[now_hkt.weekday()]
    session_names = {"morning": "早市時段（07:00-10:00）",
                     "midday": "午市時段（11:00-13:00）",
                     "evening": "晚間時段（21:30-23:00）"}
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
        f"- ⏰ 發布時間必須係從聯網搜尋結果確認嘅真實時間\n"
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
    """將所有股票代號統一為 5 位數字格式 0xxxx.HK"""
    # HK.0xxxx → 0xxxx.HK
    text = re.sub(r'HK\.(\d{1,5})(?!\d)', lambda m: f"{m.group(1).zfill(5)}.HK", text)
    # 0xxxx.HK → 補零至 5 位
    text = re.sub(r'(?<!\d)(\d{1,5})\.HK(?!\d)', lambda m: f"{m.group(1).zfill(5)}.HK", text)
    return text
def format_links(text):
    """將 URL 轉為 [點擊查看](url)，空連結行移除"""
    # 先處理 🔗 連結：後跟 URL（可能跨行）
    def link_replacer(m):
        urls = re.findall(r'https?://[^\s\)\]]+', m.group(0))
        if urls:
            return f"🔗 連結：[點擊查看]({urls[0]})"
        return ""  # 冇 URL → 移除成行
    pattern = r'🔗 連結：[\s\S]*?(?=\n[💡🏷️📰⏰📌]|\n===|\Z)'
    text = re.sub(pattern, link_replacer, text)
    # 將殘留嘅 raw URL 都轉成 [點擊查看]
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
        except Exception as e:
            print(f"⚠️ 創建快取失敗: {e}")
        return {"stock": {}, "macro": {}}
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
            if "stock" not in data:
                data["stock"] = {}
            if "macro" not in data:
                data["macro"] = {}
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
    """清除過期記錄。
    stock key 格式係「CODE|YYYY-MM-DD」，要提取日期部分先比較；
    macro key 直接係「YYYY-MM-DD」。
    """
    expire_days = config["dedup"]["expire_days"]
    cutoff = (get_hkt_now() - timedelta(days=expire_days)).strftime("%Y-%m-%d")
    total_expired = 0
    # stock: key = "01091.HK|2026-08-19"，提取 | 後面嘅日期
    expired = [k for k in cache["stock"] if k.split("|")[-1] < cutoff]
    for k in expired:
        del cache["stock"][k]
    total_expired += len(expired)
    # macro: key = "2026-08-19"
    expired = [k for k in cache["macro"] if k < cutoff]
    for k in expired:
        del cache["macro"][k]
    total_expired += len(expired)
    if total_expired:
        print(f"🧹 清除 {total_expired} 條過期快取")
# 板塊主題關鍵詞組（同一組內嘅新聞視為相關主題）
MACRO_TOPIC_GROUPS = [
    {"油價", "原油", "布油", "美油", "石油", "霍爾木茲", "中東", "地緣",
     "停火", "美伊", "以色列", "伊朗", "也門", "海峽", "煉油", "天然氣"},
    {"加息", "減息", "降準", "利率", "美聯儲", "聯儲", "央行", "逆回購",
     "流動性", "通脹", "通膨", "CPI", "PPI", "寬鬆", "貨幣政策"},
    {"內房", "地產", "房企", "樓市", "房地產", "住房", "物業"},
    {"人工智能", "芯片", "半導體", "晶圓", "算力", "大模型", "AI",
     "GPU", "英偉達", "輝達", "NVIDIA"},
    {"新能源車", "電動車", "比亞迪", "充電", "鋰電", "光伏"},
    {"關稅", "貿易戰", "制裁", "出口管制", "貿易壁壘"},
]
def extract_keywords(text):
    """從標題提取關鍵詞（中文 bigram + 英文，用於板塊去重）"""
    cleaned = re.sub(r'[^\w\u4e00-\u9fff]', ' ', text)
    keywords = set()
    for w in re.findall(r'[a-zA-Z]{2,}', cleaned):
        wl = w.lower()
        if wl not in MACRO_STOP_WORDS:
            keywords.add(wl)
    for segment in re.findall(r'[\u4e00-\u9fff]+', cleaned):
        for i in range(len(segment) - 1):
            bg = segment[i:i + 2]
            if bg not in MACRO_STOP_WORDS:
                keywords.add(bg)
    return keywords
def _topic_group(text):
    """返回文本命中嘅主題組 index，無命中返回 -1"""
    for i, group in enumerate(MACRO_TOPIC_GROUPS):
        if any(kw in text for kw in group):
            return i
    return -1
def is_duplicate_macro(title, macro_cache, date_str):
    """檢查板塊消息係咪同一事件。
    - 同主題組：bigram 重疊 ≥ 2 → 視為同一事件
    - 唔同主題：bigram 重疊 ≥ 3 且比例 ≥ 35%
    """
    new_kw = extract_keywords(title)
    if not new_kw:
        return False
    new_topic = _topic_group(title)
    existing = macro_cache.get(date_str, [])
    for old_kw_list in existing:
        old_kw = set(old_kw_list)
        if not old_kw:
            continue
        overlap = new_kw & old_kw
        min_len = min(len(new_kw), len(old_kw))
        ratio = len(overlap) / min_len if min_len > 0 else 0
        # 同主題組：只要 2 個關鍵 bigram 重疊就當同一事件
        if new_topic >= 0 and len(overlap) >= 2:
            return True
        # 唔同主題：重疊 ≥ 3 個且比例 ≥ 35%
        if len(overlap) >= 3 and ratio >= 0.35:
            return True
    return False
def add_macro_keyword(title, macro_cache, date_str):
    kw = list(extract_keywords(title))
    if kw:
        macro_cache.setdefault(date_str, []).append(kw)
# ============================================================
# 進程鎖
# ============================================================
def acquire_lock():
    now_ts = time.time()
    if LOCK_FILE.exists():
        try:
            ts = float(LOCK_FILE.read_text().strip())
            if (now_ts - ts) > 30 * 60:  # 30 分鐘過期
                LOCK_FILE.unlink()
            else:
                return False
        except Exception:
            try:
                LOCK_FILE.unlink()
            except Exception:
                pass
    try:
        LOCK_FILE.write_text(str(now_ts))
        return True
    except Exception:
        return False
def release_lock():
    try:
        if LOCK_FILE.exists():
            LOCK_FILE.unlink()
    except Exception:
        pass
# ============================================================
# Gemini 調用
# ============================================================
def is_retryable_error(e):
    err = str(e).lower()
    return any(kw in err for kw in [
        "429", "rate limit", "rate_limit", "resource exhausted",
        "resource_exhausted", "quota", "too many requests",
        "timeout", "timed out", "deadline exceeded",
        "503", "502", "500", "unavailable",
        "server disconnected", "remoteprotocolerror",
        "connection reset", "connection aborted", "connection error",
        "network is unreachable", "eof occurred", "incomplete read",
    ])
def is_daily_quota_exhausted(e):
    """檢查係咪每日配額用盡（429 + exceeded your current quota）。
    注意：RPM 限制都會返回 RESOURCE_EXHAUSTED，但訊息係 'rate limit'，
    呢種可以等一陣重試，唔好當成每日配額用盡。"""
    err = str(e).lower()
    return "exceeded your current quota" in err
def extract_grounding_urls(response):
    """提取 grounding metadata 嘅真實來源 URL"""
    urls = []
    try:
        if not response.candidates:
            return urls
        meta = getattr(response.candidates[0], "grounding_metadata", None)
        if not meta:
            return urls
        chunks = getattr(meta, "grounding_chunks", None)
        if not chunks:
            return urls
        for chunk in chunks:
            web = getattr(chunk, "web", None)
            if web:
                uri = getattr(web, "uri", "")
                title = getattr(web, "title", "來源")
                if uri:
                    urls.append((title, uri))
    except Exception as e:
        print(f"⚠️ 提取 grounding URL 失敗: {e}")
    return urls
def count_source_domains(grounding_urls):
    """從 grounding URL 統計獨立新聞源。
    返回 (domains_list, vertex_count)：
    - domains_list：原始域名列表（過濾 Google 自己嘅域名）
    - vertex_count：vertexaisearch 導流連結數量（Gemma 可能返回呢類 URL）
    """
    domains = set()
    vertex_count = 0
    for _, uri in grounding_urls:
        try:
            parsed = urlparse(uri)
            domain = parsed.netloc.lower().replace("www.", "")
            if not domain:
                continue
            if "vertexaisearch" in domain:
                vertex_count += 1
            elif "google.com" not in domain:
                domains.add(domain)
        except Exception:
            continue
    return sorted(domains), vertex_count
SYSTEM_INSTRUCTION = (
    "你係港股新聞分析員。你必須嚴格按照用戶指定嘅格式輸出，使用繁體中文。"
    "禁止使用 Markdown 標題（**文字**）、項目符號（* 或 -）、編號列表、英文分析散文。"
    "你嘅回應只能包含指定嘅 section 標記（=== 【...】 ===）同 📰 新聞條目，"
    "或者「當前時段無符合條件」聲明，不得有任何前言、分析、解釋、後語。"
)
_gemini_client = None
def get_gemini_client(config):
    """複用同一個 client，避免 chat 引用嘅 client 被 GC 關閉"""
    global _gemini_client
    if _gemini_client is None:
        gcfg = config["gemini"]
        _gemini_client = genai.Client(
            api_key=os.getenv("GEMINI_API_KEY", ""),
            http_options=types.HttpOptions(timeout=gcfg["timeout_sec"] * 1000),
        )
    return _gemini_client
def gemini_call(prompt, config, chat=None):
    """調用 Gemini，返回 (text, grounding_urls, chat, quota_exhausted)。
    傳入 chat 可繼續同一對話（用於強制重試搜尋）。
    quota_exhausted=True 表示每日配額用盡，重試冇用。
    """
    gcfg = config["gemini"]
    client = get_gemini_client(config)
    gen_config = types.GenerateContentConfig(
        temperature=0.2,
        system_instruction=SYSTEM_INSTRUCTION,
        tools=[types.Tool(google_search=types.GoogleSearch())],
    )
    quota_429_streak = 0  # 連續收到 quota 429 嘅次數
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
                    # 連續 2 次都係 quota 429 → 真正 RPD 用盡
                    print(f"🚫 Gemini 連續 {quota_429_streak} 次配額用盡，"
                          f"確認 RPD 已用盡: {str(e)[:200]}")
                    return "", [], chat, True
                # 第一次 quota 429 → 可能係 RPM 限制，等 60 秒再試
                wait = gcfg["retry_wait_sec"]
                print(f"⚠️ Gemini 配額 429（第 {quota_429_streak} 次），"
                      f"可能係 RPM 限制，{wait}s 後重試: {str(e)[:150]}")
                time.sleep(wait)
                continue
            # 非配額錯誤 → 重置連續計數
            quota_429_streak = 0
            if is_retryable_error(e) and attempt < gcfg["max_retries"] - 1:
                wait = gcfg["retry_wait_sec"] * (attempt + 1)
                print(f"⚠️ Gemini 調用失敗，{wait}s 後重試 "
                      f"({attempt + 1}/{gcfg['max_retries']}): {str(e)[:150]}")
                time.sleep(wait)
            else:
                print(f"❌ Gemini 調用最終失敗（已重試 {gcfg['max_retries']} 次）: {str(e)[:200]}")
                return "", [], chat, False
    return "", [], chat, False
# ============================================================
# 新聞解析
# ============================================================
def split_sections(text):
    """將 Gemini 回應切分為 (macro_text, stock_text)"""
    macro_text = ""
    stock_text = ""
    macro_marker = "=== 【板塊宏觀消息】 ==="
    stock_marker = None
    for marker in ["=== 【個股重大利好】 ===", "=== 【個股重大利好/異動】 ==="]:
        if marker in text:
            stock_marker = marker
            break
    if stock_marker and macro_marker in text:
        parts = text.split(stock_marker)
        stock_text = parts[1] if len(parts) > 1 else ""
        macro_parts = parts[0].split(macro_marker)
        macro_text = macro_parts[1] if len(macro_parts) > 1 else ""
    elif stock_marker:
        parts = text.split(stock_marker)
        stock_text = parts[1] if len(parts) > 1 else ""
    elif macro_marker:
        parts = text.split(macro_marker)
        macro_text = parts[1] if len(parts) > 1 else ""
    return macro_text.strip(), stock_text.strip()
def parse_entries(section_text):
    """以 📰 為邊界切分逐條新聞"""
    if not section_text or "📰" not in section_text:
        return []
    raw_entries = re.split(r'(?=📰)', section_text)
    entries = []
    for e in raw_entries:
        e = e.strip()
        if e and "📰" in e:
            entries.append(e)
    return entries
def extract_field(entry, emoji):
    """提取某個 emoji 欄位嘅內容"""
    pattern = rf'{emoji}\s*[^\n：:]*[：:]\s*([^\n]*)'
    m = re.search(pattern, entry)
    return m.group(1).strip() if m else ""
def extract_url_from_entry(entry):
    """從條目入面提取 URL"""
    urls = re.findall(r'https?://[^\s\)\]]+', entry)
    return urls[0] if urls else ""
def parse_entry_time(entry):
    """
    解析 ⏰ 欄位嘅時間，返回 (datetime, is_valid)
    is_valid=False 表示時間含禁止詞或無法解析
    """
    time_line = ""
    m = re.search(r'⏰[^\n]*', entry)
    if m:
        time_line = m.group(0)
    # 檢查禁止詞
    for word in TIME_FORBIDDEN_WORDS:
        if word in time_line:
            return None, False
    # 提取日期時間
    dt_match = re.search(r'(\d{4})-(\d{1,2})-(\d{1,2})\s+(\d{1,2}):(\d{2})', time_line)
    if dt_match:
        try:
            y, mo, d, h, mi = map(int, dt_match.groups())
            return datetime(y, mo, d, h, mi, tzinfo=HKT), True
        except ValueError:
            return None, False
    return None, False
def is_no_news(text):
    """檢查回應係咪表示「無新聞」"""
    markers = [
        "無符合條件", "冇符合條件", "无符合条件",
        "無具催化力", "无具催化力",
        "沒有符合條件", "没有符合条件",
        "無重大", "无重大", "冇重大",
    ]
    return any(kw in text for kw in markers)
# ============================================================
# 核心掃描
# ============================================================
def scan_once(session_name, turn_count, macro_pushed, config, prompts):
    """
    執行一次掃描
    prompts: (macro_prompt, stock_prompt)
    返回 True 表示有推送，False 表示無，"quota_exhausted" 表示配額用盡
    """
    macro_prompt, stock_prompt = prompts
    now_hkt = get_hkt_now()
    date_str = now_hkt.strftime("%Y-%m-%d")
    news_after = calc_news_after(session_name, now_hkt, config)
    cache = load_cache(config)
    cleanup_cache(cache, config)
    # 組裝 prompt
    time_info = get_time_injection(now_hkt, news_after, session_name)
    format_reminder = (
        "\n⚠️ 最終格式檢查（違反即不合格）：\n"
        "- 回應只能包含「=== 【板塊宏觀消息】 ===」同「=== 【個股重大利好】 ===」區塊\n"
        "- 每條新聞必須以 📰 開頭，逐行使用 📰🏷️⏰📌🔗💡 欄位\n"
        "- 禁止 Markdown 標題（**text**）、項目符號（* 或 -）、編號列表\n"
        "- 禁止英文分析散文、禁止「Based on search results」等前言\n"
        "- 直接輸出格式內容，唔好有任何解釋、分析、思考過程\n"
        "- 無新聞時直接輸出「當前時段無符合條件之板塊消息」或「當前時段無符合條件之重大利好」"
    )
    if turn_count == 1 and macro_prompt:
        # 第一輪：板塊 + 個股
        prompt = (
            f"{macro_prompt}\n\n---\n\n{stock_prompt}"
            f"{time_info}"
            f"\n【掃描模式】首輪掃描，請先輸出「=== 【板塊宏觀消息】 ===」，"
            f"再輸出「=== 【個股重大利好】 ===」。"
            f"{format_reminder}"
        )
        print("📡 第一輪掃描（板塊+個股）")
    else:
        # 後續輪：只掃個股
        prompt = (
            f"{stock_prompt}"
            f"{time_info}"
            f"\n【掃描模式】盤中輪詢掃描，只輸出「=== 【個股重大利好】 ===」部分。"
            f"若盤中出現突發黑天鵝級宏觀事件（如突發戰爭、突發降準、重磅監管轉向），"
            f"可在最前面輸出「=== 【板塊宏觀消息】 ===」緊急警報；若無則不要輸出板塊區塊。"
            f"{format_reminder}"
        )
        print(f"📡 第 {turn_count} 輪掃描（只掃個股）")
    # 調用 Gemini
    llm_result, grounding_urls, chat, quota_exhausted = gemini_call(prompt, config)
    if quota_exhausted:
        return "quota_exhausted"
    print(f"=== Gemini 回應 ({len(llm_result)} 字元) ===")
    print(llm_result[:2000])
    if len(llm_result) > 2000:
        print(f"...（省略 {len(llm_result) - 2000} 字元）")
    if grounding_urls:
        source_domains, vertex_count = count_source_domains(grounding_urls)
        total_sources = len(source_domains) + vertex_count
        print(f"🔗 Grounding 來源: {len(grounding_urls)} 個 URL，{total_sources} 個搜尋結果")
        if source_domains:
            print(f"📡 新聞源: {', '.join(source_domains)}")
        elif vertex_count:
            print(f"📡 新聞源: {vertex_count} 個 Google 搜尋結果（導流連結）")
    else:
        # fallback：grounding metadata 為空時，從回應文本提取 vertexaisearch 連結
        text_urls = re.findall(r'https?://vertexaisearch\.cloud\.google\.com/[^\s\)\]]+', llm_result)
        if text_urls:
            grounding_urls = [("來源", u) for u in text_urls]
            source_domains = []
            vertex_count = len(text_urls)
            print(f"🔗 Grounding 來源（從文本提取）: {len(text_urls)} 個搜尋連結")
        else:
            source_domains = []
            vertex_count = 0
            print("⚠️ Gemini 冇返回任何 grounding URL（可能冇使用搜尋工具）")
    # 組合來源摘要文字
    total_sources = len(source_domains) + vertex_count
    if source_domains:
        source_summary = f"{len(source_domains)} 個新聞源：{', '.join(source_domains)}"
    elif vertex_count:
        source_summary = f"{vertex_count} 個 Google 搜尋結果"
    else:
        source_summary = ""
    # 冇 grounding URL 又話無新聞 → 可能冇搜尋，重試一次
    if total_sources == 0 and "📰" not in llm_result:
        print("⚠️ Gemini 冇使用搜尋工具就答無新聞，重試一次...")
        time.sleep(3)
        retry_prompt = (
            "🚨 你剛才冇使用 Google 搜尋工具！請立即使用 Google 搜尋工具，"
            "搜尋港股最新嘅盈喜、業績、回購、增持、上調目標價等重大利好消息，"
            "然後按照格式重新輸出。"
        )
        llm_result, grounding_urls, chat, quota_exhausted = gemini_call(retry_prompt, config, chat=chat)
        if quota_exhausted:
            return "quota_exhausted"
        print(f"=== 重試回應 ({len(llm_result)} 字元) ===")
        print(llm_result[:2000])
        # 重新統計來源
        if grounding_urls:
            source_domains, vertex_count = count_source_domains(grounding_urls)
            total_sources = len(source_domains) + vertex_count
            if source_domains:
                source_summary = f"{len(source_domains)} 個新聞源：{', '.join(source_domains)}"
                print(f"📡 新聞源: {', '.join(source_domains)}")
            elif vertex_count:
                source_summary = f"{vertex_count} 個 Google 搜尋結果"
                print(f"📡 新聞源: {vertex_count} 個 Google 搜尋結果（導流連結）")
        else:
            text_urls = re.findall(r'https?://vertexaisearch\.cloud\.google\.com/[^\s\)\]]+', llm_result)
            if text_urls:
                grounding_urls = [("來源", u) for u in text_urls]
                source_domains = []
                vertex_count = len(text_urls)
                total_sources = vertex_count
                source_summary = f"{vertex_count} 個 Google 搜尋結果"
                print(f"🔗 Grounding 來源（從文本提取）: {len(text_urls)} 個搜尋連結")
    # 檢查有冇實質內容
    has_section = "【板塊宏觀消息】" in llm_result or "【個股重大利好" in llm_result
    has_news_emoji = "📰" in llm_result
    if not has_section and not has_news_emoji:
        print("ℹ️ 無任何新聞內容，唔推送")
        return False
    if is_no_news(llm_result) and not has_news_emoji:
        print("ℹ️ 當前時段無符合條件之重大消息，唔推送")
        return False
    # 標準化股票代號
    llm_result = normalize_stock_codes(llm_result)
    # 切分區塊
    macro_text, stock_text = split_sections(llm_result)
    # 格式合規檢查：有 section 標記但冇 📰 → Gemini 冇跟格式
    if has_section and not has_news_emoji and not is_no_news(llm_result):
        print("⚠️ Gemini 回應有 section 標記但冇 📰 格式，可能冇跟從輸出格式！")
        print("⚠️ 首 500 字元：", llm_result[:500])
    # 準備真實來源 URL（grounding metadata）
    real_urls = [uri for _, uri in grounding_urls if "vertexaisearch" not in uri]
    if not real_urls:
        real_urls = [uri for _, uri in grounding_urls]
    url_idx = 0
    def get_url_for_entry(entry_text):
        """優先用文本入面嘅 URL，否則用 grounding URL"""
        nonlocal url_idx
        url = extract_url_from_entry(entry_text)
        # 如果係超長 redirect URL，優先用 grounding 真實 URL
        if url and "vertexaisearch" not in url and len(url) < 300:
            return url
        if url_idx < len(real_urls):
            u = real_urls[url_idx]
            url_idx += 1
            return u
        return url  # fallback
    # ---- 板塊消息處理 ----
    macro_entries = []
    macro_raw = parse_entries(macro_text)
    for entry in macro_raw:
        title = extract_field(entry, "📰 新聞標題") or entry[:60]
        # 時間驗證
        news_time, valid = parse_entry_time(entry)
        if not valid:
            print(f"🚫 板塊消息時間不明/含禁止詞，丟棄: {title[:40]}")
            continue
        if news_time and (news_time < news_after or news_time > now_hkt + timedelta(minutes=10)):
            print(f"🚫 板塊消息超出時間範圍，丟棄: {title[:40]} ({format_hkt(news_time)})")
            continue
        # 主題去重
        if is_duplicate_macro(title, cache["macro"], date_str):
            print(f"🔁 板塊消息主題重複，跳過: {title[:40]}")
            continue
        # 同時檢查 job 內去重
        if title in macro_pushed:
            print(f"🔁 板塊消息本 session 已推送，跳過: {title[:40]}")
            continue
        # 加入連結
        url = get_url_for_entry(entry)
        if url:
            entry = re.sub(
                r'🔗 連結：[\s\S]*?(?=\n[💡🏷️📰⏰📌]|\Z)',
                f"🔗 連結：{url}",
                entry,
                flags=re.MULTILINE,
            )
        macro_entries.append(entry)
        macro_pushed.add(title)
        add_macro_keyword(title, cache["macro"], date_str)
    # ---- 個股消息處理 ----
    stock_entries = []
    stock_raw = parse_entries(stock_text)
    filters = config["filters"]
    for entry in stock_raw:
        title = extract_field(entry, "📰 新聞標題") or entry[:60]
        stock_field = extract_field(entry, "🏷️ 股票")
        # 必須有股票代號
        code_match = re.search(r'(\d{5})\.HK', stock_field)
        if not code_match:
            # 嘗試從全文搵
            code_match = re.search(r'(\d{5})\.HK', entry)
        if not code_match:
            print(f"🚫 搵唔到股票代號，丟棄: {title[:40]}")
            continue
        code = f"{code_match.group(1)}.HK"
        # 時間驗證
        news_time, valid = parse_entry_time(entry)
        if not valid:
            print(f"🚫 {code} 時間不明/含禁止詞，丟棄: {title[:40]}")
            continue
        if news_time and (news_time < news_after or news_time > now_hkt + timedelta(minutes=10)):
            print(f"🚫 {code} 超出時間範圍，丟棄: {title[:40]} ({format_hkt(news_time)})")
            continue
        # 跨 job 去重：代號+新聞日期（唔係推送日期，防止跨 session 重推同一單聞）
        news_date = news_time.strftime("%Y-%m-%d") if news_time else date_str
        dedup_key = f"{code}|{news_date}"
        if dedup_key in cache["stock"]:
            print(f"🔁 {code} 新聞日期 {news_date} 已推送過，跳過: {title[:40]}")
            continue
        # 加入連結
        url = get_url_for_entry(entry)
        if url:
            entry = re.sub(
                r'🔗 連結：[\s\S]*?(?=\n[💡🏷️📰⏰📌]|\Z)',
                f"🔗 連結：{url}",
                entry,
                flags=re.MULTILINE,
            )
        stock_entries.append(entry)
        cache["stock"][dedup_key] = title[:100]
    # 硬上限
    max_news = filters["max_stock_news"]
    if len(stock_entries) > max_news:
        print(f"⚠️ 個股新聞 {len(stock_entries)} 條，截斷至 {max_news} 條")
        stock_entries = stock_entries[:max_news]
    macro_has = len(macro_entries) > 0
    stock_has = len(stock_entries) > 0
    print(f"📊 解析結果：板塊 {len(macro_entries)} 條，個股 {len(stock_entries)} 條")
    if not macro_has and not stock_has:
        print("ℹ️ 篩選後無新內容，唔推送")
        save_cache(cache, config)
        return False
    # 組裝
    parts = []
    if macro_has:
        parts.append("=== 【板塊宏觀消息】 ===")
        parts.append("\n\n".join(macro_entries))
    if stock_has:
        parts.append("=== 【個股重大利好】 ===")
        parts.append("\n\n".join(stock_entries))
    final_text = "\n\n".join(parts)
    final_text = format_links(final_text)
    # 附加搜尋來源統計
    if source_summary:
        final_text += f"\n\n---\n📡 本次搜尋咗 {source_summary}"
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
    print(f"=== HKT 現在時間: {now_hkt.strftime('%Y-%m-%d %H:%M:%S')} "
          f"{WEEKDAY_CN[now_hkt.weekday()]} ({WEEKDAY_EN[now_hkt.weekday()]}) ===")
    print("=" * 60)
    # 讀取 prompt variables
    macro_prompt = os.getenv("HK_NEWS_PROMPT_MACRO", "").strip()
    stock_prompt = os.getenv("HK_NEWS_PROMPT_STOCK", "").strip()
    if not stock_prompt:
        print("❌ HK_NEWS_PROMPT_STOCK 未設置，請喺 GitHub Variables 配置")
        sys.exit(1)
    if not macro_prompt:
        print("⚠️ HK_NEWS_PROMPT_MACRO 未設置，板塊消息將被跳過")
    if force_run:
        session_name = get_force_run_session(now_hkt)
        news_after = calc_news_after(session_name, now_hkt, config)
        print(f"⚠️ FORCE_RUN 模式：模擬 {session_name} session，即時跑一次")
        print(f"=== 新聞有效範圍: {format_hkt(news_after)} ~ {format_hkt(now_hkt)} ===")
        run_mode = "one_shot"
    else:
        if is_weekend(now_hkt):
            print("ℹ️ 週末，退出")
            return
        session_name = get_session(now_hkt, config)
        if not session_name:
            print("ℹ️ 唔在任何執行窗口，退出")
            return
        run_mode = "long_run"
        s = config["sessions"][session_name]
        news_after = calc_news_after(session_name, now_hkt, config)
        print(f"=== Session: {session_name} ({s['start']}-{s['end']}) ===")
        print(f"=== 新聞有效範圍: {format_hkt(news_after)} ~ {format_hkt(now_hkt)} ===")
    if not acquire_lock():
        print("⚠️ 已有另一個實例在執行，跳過")
        return
    try:
        if run_mode == "one_shot":
            try:
                scan_once(session_name, 1, set(), config, (macro_prompt, stock_prompt))
            except Exception as e:
                print(f"❌ 掃描異常（已捕获，唔會 crash）: {str(e)[:300]}")
        elif run_mode == "long_run":
            turn = 0
            macro_pushed = set()
            scan_cfg = config["scan"]
            while True:
                turn += 1
                turn_start = get_hkt_now()
                print(f"\n{'─' * 50}")
                print(f"--- Turn {turn} | {turn_start.strftime('%H:%M:%S')} HKT ---")
                print(f"{'─' * 50}")
                try:
                    result = scan_once(session_name, turn, macro_pushed, config,
                              (macro_prompt, stock_prompt))
                    if result == "quota_exhausted":
                        print("\n🚫 Gemini 每日配額已用盡，提早結束 session")
                        break
                except Exception as e:
                    print(f"❌ 本輪異常，跳過: {str(e)[:200]}")
                # 檢查係咪到結束時間
                now_check = get_hkt_now()
                if is_session_over(session_name, now_check, config):
                    print(f"\n🏁 已到 session 結束時間 "
                          f"({config['sessions'][session_name]['end']})，退出迴圈")
                    break
                # 隨機休眠
                sleep_sec = random.randint(
                    scan_cfg["interval_min_min"] * 60,
                    scan_cfg["interval_min_max"] * 60,
                )
                next_run = get_hkt_now() + timedelta(seconds=sleep_sec)
                print(f"💤 本輪完成，休眠 {sleep_sec // 60} 分 {sleep_sec % 60} 秒，"
                      f"下一輪約 {next_run.strftime('%H:%M')} HKT")
                time.sleep(sleep_sec)
    finally:
        release_lock()
if __name__ == "__main__":
    main()
