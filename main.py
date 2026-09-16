#!/usr/bin/env python3
"""
港股新聞監控系統 v2 (雙軌並行優化版)
- GitHub Actions 長駐掃描 + gemma-4-31b-it 聯網 + 飛書卡片推送
- 第一輪掃描：先獨立搜板塊，再獨立搜個股（保證命中率）
- 恢復 Gemini 錯誤日誌輸出，防止靜默卡死
- 恢復完整的解析過濾日誌 (🚫丟棄 / 🔁重複 / 📊統計)
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
    if not text:
        return text
    return _cc.convert(text)

# ============================================================
# 常量
# ============================================================
HKT = timezone(timedelta(hours=8))
SCRIPT_DIR = Path(__file__).parent
CONFIG_PATH = SCRIPT_DIR / "config.yaml"
LOCK_FILE = SCRIPT_DIR / "run.lock"

WEEKDAY_CN = ["星期一", "星期二", "星期三", "星期四", "星期五", "星期六", "星期日"]
WEEKDAY_EN = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"]

MACRO_STOP_WORDS = set(
    "的了在是及與和等將於為對由有個中年月日上下不亦都而但又或被向從"
    "令可能該其這那之以較更最再已正將會要把讓給據稱道表示預計料帶動"
    "受惠影響板塊消息新聞發布時間來源連結摘要利好邏輯股票香港港股恆指"
    "今日昨日當前目前市場資金政策宏觀數據顯示預期維持持續進一步"
    "a the of to in on for and or with is are was were be been has have"
)

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
        "timeout_sec": 180,
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
    cfg = json.loads(json.dumps(DEFAULT_CONFIG))
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
    wd = hkt.weekday()
    if wd == 0: days_back = 3
    elif wd == 6: days_back = 2
    else: days_back = 1
    base_date = (hkt - timedelta(days=days_back)).date()
    return datetime(base_date.year, base_date.month, base_date.day, 16, 0, tzinfo=HKT)

def get_session(hkt, config):
    grace = config.get("grace_minutes", 30)
    for name, s in config["sessions"].items():
        sh, sm = map(int, s["start"].split(":"))
        eh, em = map(int, s["end"].split(":"))
        start_dt = hkt.replace(hour=sh, minute=sm, second=0, microsecond=0)
        end_dt = hkt.replace(hour=eh, minute=em, second=0, microsecond=0)
        if eh <= sh:
            if hkt >= start_dt or hkt <= end_dt: return name
        else:
            if start_dt <= hkt <= end_dt: return name
    for name, s in config["sessions"].items():
        sh, sm = map(int, s["start"].split(":"))
        eh, em = map(int, s["end"].split(":"))
        start_dt = hkt.replace(hour=sh, minute=sm, second=0, microsecond=0)
        end_dt = hkt.replace(hour=eh, minute=em, second=0, microsecond=0)
        grace_end = end_dt + timedelta(minutes=grace)
        if eh <= sh:
            if hkt >= start_dt or hkt <= grace_end: return name
        else:
            if start_dt <= hkt <= grace_end: return name
    return None

def is_session_over(session_name, hkt, config):
    s = config["sessions"].get(session_name)
    if not s: return True
    sh, sm = map(int, s["start"].split(":"))
    eh, em = map(int, s["end"].split(":"))
    end_dt = hkt.replace(hour=eh, minute=em, second=0, microsecond=0)
    if eh <= sh:
        if hkt.hour >= sh: return False
        return hkt >= end_dt
    else:
        if hkt.hour < sh: return True
        return hkt >= end_dt

def get_force_run_session(hkt):
    if hkt.weekday() >= 5: return "morning"
    t = hkt.hour * 60 + hkt.minute
    if t < 3 * 60: return "evening"
    elif t < 10 * 60: return "morning"
    elif t < 16 * 60: return "midday"
    else: return "evening"

def calc_news_after(session_name, hkt, config):
    if session_name is None: session_name = get_force_run_session(hkt)
    if hkt.weekday() >= 5: return get_last_trading_close(hkt)
    
    na_type = config["sessions"][session_name]["news_after"]
    if na_type == "last_trading_day_close":
        return get_last_trading_close(hkt)
        
    m = re.match(r'^today_(\d{1,2}):(\d{2})$', str(na_type))
    if m:
        news_after = hkt.replace(hour=int(m.group(1)), minute=int(m.group(2)), second=0, microsecond=0)
        if news_after > hkt: news_after -= timedelta(days=1)
        return news_after
    return hkt - timedelta(hours=24)

def format_hkt(dt):
    return dt.strftime("%Y-%m-%d %H:%M HKT")

def get_time_injection(now_hkt, news_after, session_name):
    wd_cn = WEEKDAY_CN[now_hkt.weekday()]
    is_wknd = now_hkt.weekday() >= 5
    s_name = "週末掃描（上週五收市後至今）" if is_wknd else {"morning": "早市", "midday": "午市", "evening": "晚間"}.get(session_name, "測試模式")
    return (
        f"\n---\n"
        f"【當前香港時間】{now_hkt.strftime('%Y-%m-%d')}（{wd_cn}）{now_hkt.strftime('%H:%M')} HKT\n"
        f"【新聞有效時間範圍】{format_hkt(news_after)} 至 {format_hkt(now_hkt)}\n"
        f"【掃描時段】{s_name}\n\n"
        f"⚠️ 時效鐵律（必須嚴格遵守）：\n"
        f"- 只輸出在上述「新聞有效時間範圍」內發布嘅新聞\n"
        f"- ⏰ 發布時間必須係真實時間。時間不明直接捨棄。\n"
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
    if not webhook: return -1
    
    now_hkt = get_hkt_now()
    payload = {
        "msg_type": "interactive",
        "card": {
            "config": {"wide_screen_mode": True},
            "header": {
                "title": {"tag": "plain_text", "content": f"{fs['card_title']} | {now_hkt.strftime('%Y-%m-%d')}"},
                "template": fs["card_color"],
            },
            "elements": [
                {"tag": "div", "text": {"tag": "lark_md", "content": raw_text}},
                {"tag": "hr"},
                {"tag": "note", "elements": [{"tag": "plain_text", "content": f"⏰ 推送時間：{now_hkt.strftime('%Y-%m-%d %H:%M HKT')}"}]},
            ],
        },
    }
    if secret:
        ts = str(int(time.time()))
        payload["timestamp"] = ts
        payload["sign"] = gen_feishu_sign(ts, secret)
        
    for _ in range(3):
        try:
            r = requests.post(webhook, json=payload, timeout=30)
            if r.status_code == 200 and r.json().get("code", 0) == 0:
                print("✅ 飛書推送成功")
                return 200
        except Exception: pass
        time.sleep(3)
    return -1

# ============================================================
# 文本處理與 Regex修復
# ============================================================
def normalize_stock_codes(text):
    text = re.sub(r'HK\.(\d{1,5})(?!\d)', lambda m: f"{m.group(1).zfill(5)}.HK", text)
    text = re.sub(r'(?<!\d)(\d{1,5})\.HK(?!\d)', lambda m: f"{m.group(1).zfill(5)}.HK", text)
    return text

def format_links(text):
    def link_replacer(m):
        urls = re.findall(r'https?://[^\s\)\]]+', m.group(0))
        return f"🔗 連結：[點擊查看]({urls[0]})" if urls else ""
    pattern = r'🔗 連結：[\s\S]*?(?=\n[💡🏷️📰⏰📌]|\n===|\Z)'
    text = re.sub(pattern, link_replacer, text)
    
    def raw_url_replacer(m): return f"[點擊查看]({m.group(0)})"
    text = re.sub(r'(?<![\(\]])https?://[^\s\)\]]+', raw_url_replacer, text)
    return re.sub(r'\n{3,}', '\n\n', text).strip()

def normalize_stock_title(title):
    t = re.sub(r'[\(（]\d{4,5}[\)）]', '', title)
    t = re.sub(r'\d{5}\.HK', '', t, flags=re.IGNORECASE)
    t = re.sub(r'[^\w\u4e00-\u9fff]', '', t)
    return t.lower()

def is_duplicate_stock_title(title, code, pushed_titles):
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
# 快取管理
# ============================================================
def cache_path(config): return SCRIPT_DIR / config["dedup"]["cache_file"]
def load_cache(config):
    path = cache_path(config)
    if path.exists():
        try:
            with open(path, "r", encoding="utf-8") as f:
                d = json.load(f)
                return {"stock": d.get("stock", {}), "macro": d.get("macro", {})}
        except Exception: pass
    return {"stock": {}, "macro": {}}
def save_cache(cache, config):
    try:
        with open(cache_path(config), "w", encoding="utf-8") as f: json.dump(cache, f, ensure_ascii=False, indent=2)
    except Exception: pass
def cleanup_cache(cache, config):
    cutoff = (get_hkt_now() - timedelta(days=config["dedup"]["expire_days"])).strftime("%Y-%m-%d")
    for k in [k for k in cache["stock"] if k.split("|")[-1] < cutoff]: del cache["stock"][k]
    for k in [k for k in cache["macro"] if k < cutoff]: del cache["macro"][k]

MACRO_TOPIC_GROUPS = [
    {"油價", "原油", "石油", "地緣", "停火", "中東", "天然氣"},
    {"加息", "降準", "利率", "美聯儲", "央行", "通脹", "貨幣政策"},
    {"內房", "地產", "房地產"},
    {"人工智能", "芯片", "半導體", "AI", "英偉達"},
    {"新能源車", "電動車", "光伏"},
    {"關稅", "貿易戰", "制裁"},
]

def extract_keywords(text):
    cleaned = re.sub(r'[^\w\u4e00-\u9fff]', ' ', text)
    keywords = set([w.lower() for w in re.findall(r'[a-zA-Z]{2,}', cleaned) if w.lower() not in MACRO_STOP_WORDS])
    for segment in re.findall(r'[\u4e00-\u9fff]+', cleaned):
        for i in range(len(segment) - 1):
            bg = segment[i:i + 2]
            if bg not in MACRO_STOP_WORDS: keywords.add(bg)
    return keywords

def is_duplicate_macro(title, macro_cache, date_str):
    new_kw = extract_keywords(title)
    if not new_kw: return False
    topic_idx = next((i for i, g in enumerate(MACRO_TOPIC_GROUPS) if any(k in title for k in g)), -1)
    
    for old_kw_list in macro_cache.get(date_str, []):
        overlap = new_kw & set(old_kw_list)
        if topic_idx >= 0 and len(overlap) >= 2: return True
        if len(overlap) >= 3 and (len(overlap) / min(len(new_kw), len(old_kw_list))) >= 0.35: return True
    return False

def add_macro_keyword(title, macro_cache, date_str):
    kw = list(extract_keywords(title))
    if kw: macro_cache.setdefault(date_str, []).append(kw)

# ============================================================
# Gemini 調用
# ============================================================
def extract_grounding_urls(response):
    urls = []
    try:
        if not response.candidates: return urls
        meta = getattr(response.candidates[0], "grounding_metadata", None)
        if meta and getattr(meta, "grounding_chunks", None):
            for chunk in meta.grounding_chunks:
                if getattr(chunk, "web", None) and getattr(chunk.web, "uri", None):
                    urls.append((getattr(chunk.web, "title", "來源"), chunk.web.uri))
    except Exception: pass
    return urls

def count_source_domains(grounding_urls):
    domains, v_count = set(), 0
    for _, uri in grounding_urls:
        try:
            domain = urlparse(uri).netloc.lower().replace("www.", "")
            if "vertexaisearch" in domain: v_count += 1
            elif "google.com" not in domain: domains.add(domain)
        except Exception: pass
    return sorted(domains), v_count

_gemini_client = None
def get_gemini_client(config):
    global _gemini_client
    if _gemini_client is None:
        _gemini_client = genai.Client(api_key=os.getenv("GEMINI_API_KEY", ""), http_options=types.HttpOptions(timeout=config["gemini"]["timeout_sec"] * 1000))
    return _gemini_client

def gemini_call(prompt, config, chat=None):
    client = get_gemini_client(config)
    gen_config = types.GenerateContentConfig(
        temperature=0.2,
        system_instruction="你係港股新聞分析員。必須嚴格按照用戶指定格式輸出，所有內容必須使用繁體中文（香港用字）。禁止使用 Markdown 標題、項目符號。",
        tools=[types.Tool(google_search=types.GoogleSearch())],
    )
    for attempt in range(config["gemini"]["max_retries"]):
        try:
            if chat is None: chat = client.chats.create(model=config["gemini"]["model"], config=gen_config)
            resp = chat.send_message(prompt)
            return resp.text or "", extract_grounding_urls(resp), chat, False
        except Exception as e:
            if "exceeded your current quota" in str(e).lower(): return "", [], chat, True
            print(f"⚠️ Gemini API 發生錯誤 (嘗試 {attempt+1}/{config['gemini']['max_retries']}): {str(e)[:300]}")
            time.sleep(config["gemini"]["retry_wait_sec"])
    return None, [], chat, False

# ============================================================
# 新聞解析
# ============================================================
def split_sections(text):
    macro_text, stock_text = "", ""
    if "=== 【個股重大利好】 ===" in text:
        parts = text.split("=== 【個股重大利好】 ===")
        stock_text = parts[1] if len(parts)>1 else ""
        macro_text = parts[0].split("=== 【板塊宏觀消息】 ===")[-1] if "=== 【板塊宏觀消息】 ===" in parts[0] else ""
    elif "=== 【板塊宏觀消息】 ===" in text:
        macro_text = text.split("=== 【板塊宏觀消息】 ===")[-1]
    return macro_text.strip(), stock_text.strip()

def parse_entries(text):
    return [e.strip() for e in re.split(r'(?=📰)', text) if e.strip() and "📰" in e]

def extract_field(entry, emoji):
    m = re.search(rf'{emoji}\s*[^\n：:]*[：:]\s*([^\n]*)', entry)
    return m.group(1).strip() if m else ""

def extract_url_from_entry(entry):
    urls = re.findall(r'https?://[^\s\)\]]+', entry)
    return urls[0] if urls else ""

def parse_entry_time(entry):
    m = re.search(r'⏰[^\n]*', entry)
    if not m: return None, False
    t_line = m.group(0)
    if any(w in t_line for w in TIME_FORBIDDEN_WORDS): return None, False
    dt_m = re.search(r'(\d{4})-(\d{1,2})-(\d{1,2})\s+(\d{1,2}):(\d{2})', t_line)
    if dt_m:
        try:
            y, mo, d, h, mi = map(int, dt_m.groups())
            return datetime(y, mo, d, h, mi, tzinfo=HKT), True
        except ValueError: pass
    return None, False

# ============================================================
# 核心掃描
# ============================================================
def scan_once(session_name, turn_count, macro_pushed, stock_pushed, config, prompts):
    macro_prompt, stock_prompt = prompts
    now_hkt = get_hkt_now()
    news_after = calc_news_after(session_name, now_hkt, config)
    cache, time_info = load_cache(config), get_time_injection(now_hkt, news_after, session_name)
    cleanup_cache(cache, config)
    
    format_req = "\n⚠️ 格式要求：逐行輸出 📰🏷️⏰📌🔗💡，禁止 Markdown 標題及散文，無新聞則輸出無符合條件。"
    llm_result, grounding_urls = "", []

    # 🚀 第一輪：強制分兩次搜尋
    if turn_count == 1:
        print("📡 [第 1 輪] 啟動雙重掃描：先掃板塊，後掃個股...")
        
        if macro_prompt:
            print("   ➤ 正在掃描【板塊宏觀消息】...")
            p_macro = f"{macro_prompt}{time_info}\n【掃描模式】只輸出「=== 【板塊宏觀消息】 ===」區塊。{format_req}\n\n🛑 【立即行動】：立刻聯網搜尋今日最新宏觀及大市新聞！"
            res_m, urls_m, _, q_m = gemini_call(p_macro, config)
            if q_m: return "quota_exhausted"
            if res_m:
                res_m = to_traditional(res_m)
                print(f"   === 板塊回應 ({len(res_m)} 字元) ===")
                llm_result += res_m + "\n\n"
                grounding_urls.extend(urls_m)

        print("   ➤ 正在掃描【個股重大利好】...")
        p_stock = f"{stock_prompt}{time_info}\n【掃描模式】只輸出「=== 【個股重大利好】 ===」區塊。{format_req}\n\n🛑 【立即行動】：立刻聯網搜尋今日港股盈喜、業績、回購公告！"
        res_s, urls_s, _, q_s = gemini_call(p_stock, config)
        if q_s: return "quota_exhausted"
        if res_s:
            res_s = to_traditional(res_s)
            print(f"   === 個股回應 ({len(res_s)} 字元) ===")
            llm_result += res_s
            grounding_urls.extend(urls_s)
            
    # 🚀 第二輪起：只跑個股
    else:
        print(f"📡 [第 {turn_count} 輪] 盤中輪詢掃描：主力掃描個股...")
        p_stock = f"{stock_prompt}{time_info}\n【掃描模式】主力輸出「=== 【個股重大利好】 ===」區塊。{format_req}\n\n🛑 【立即行動】：立刻聯網搜尋今日港股突發公告！"
        res, urls, _, q = gemini_call(p_stock, config)
        if q: return "quota_exhausted"
        if res:
            llm_result = to_traditional(res)
            grounding_urls.extend(urls)
            print(f"=== Gemini 回應 ({len(llm_result)} 字元) ===")

    if not llm_result: return False
    llm_result = normalize_stock_codes(llm_result)
    
    # 🚨 列印 Grounding URLs 資訊
    if grounding_urls:
        source_domains, vertex_count = count_source_domains(grounding_urls)
        total_sources = len(source_domains) + vertex_count
        print(f"🔗 Grounding 來源: {len(grounding_urls)} 個 URL，{total_sources} 個搜尋結果")
    else:
        text_urls = re.findall(r'https?://vertexaisearch\.cloud\.google\.com/[^\s\)\]]+', llm_result)
        if text_urls:
            grounding_urls = [("來源", u) for u in text_urls]
            print(f"🔗 Grounding 來源 (從文本提取): {len(text_urls)} 個搜尋連結")
        else:
            print("⚠️ Gemini 沒有返回任何 Google 搜尋來源！")

    # 動態追問：冇搜尋就答無新聞
    if (len(grounding_urls) == 0) and ("📰" not in llm_result):
        print("⚠️ Gemini 冇使用搜尋工具就答無新聞，開新請求強制搜尋...")
        time.sleep(3)
        search_today = now_hkt.strftime("%Y年%m月%d日")
        followup = (
            f"{stock_prompt}\n\n"
            f"🚨 警告：你剛才未能成功調用聯網搜尋。請立即呼叫 Google 搜尋工具，搜尋 {search_today} 最新港股資訊。\n"
            f"關鍵詞建議：1. 港股 盈喜  2. site:cls.cn 港股 公告\n"
            f"絕對禁止唔搜尋就答無新聞！"
        )
        res_retry, urls_retry, _, q_retry = gemini_call(followup, config, chat=None)
        if q_retry: return "quota_exhausted"
        if res_retry:
            llm_result = to_traditional(res_retry)
            grounding_urls.extend(urls_retry)
            print(f"=== 重試回應 ({len(llm_result)} 字元) ===")
            if urls_retry:
                sd, vc = count_source_domains(urls_retry)
                print(f"🔗 Grounding 來源 (重試): {len(urls_retry)} 個 URL，{len(sd) + vc} 個搜尋結果")

    if not ("【板塊宏觀消息】" in llm_result or "【個股重大利好" in llm_result) and "📰" not in llm_result:
        return False

    # URL 去重與提取
    raw_urls = [u for _, u in grounding_urls if "vertexaisearch" not in u] or [u for _, u in grounding_urls]
    real_urls, used_urls, url_idx = list(dict.fromkeys(raw_urls)), set(), 0
    
    def get_url_for_entry(entry_text):
        nonlocal url_idx
        url = extract_url_from_entry(entry_text)
        if url and "vertexaisearch" not in url and len(url) < 300 and url not in used_urls:
            used_urls.add(url); return url
        while url_idx < len(real_urls):
            u = real_urls[url_idx]; url_idx += 1
            if u not in used_urls:
                used_urls.add(u); return u
        return url if url and "vertexaisearch" not in url else None

    macro_text, stock_text = split_sections(llm_result)
    macro_entries, stock_entries = [], []
    date_str = now_hkt.strftime("%Y-%m-%d")

    # 🚨 板塊解析與過濾日誌
    for entry in parse_entries(macro_text):
        title = extract_field(entry, "📰 新聞標題") or entry[:60]
        news_time, valid = parse_entry_time(entry)
        if not valid:
            print(f"🚫 板塊消息時間不明/含禁止詞，丟棄: {title[:40]}")
            continue
        if news_time and not (news_after <= news_time <= now_hkt + timedelta(minutes=10)):
            print(f"🚫 板塊消息超出時間範圍，丟棄: {title[:40]} ({format_hkt(news_time)})")
            continue
        if is_duplicate_macro(title, cache["macro"], date_str) or title in macro_pushed:
            print(f"🔁 板塊消息主題重複或已推送，跳過: {title[:40]}")
            continue
            
        url = get_url_for_entry(entry)
        if url: entry = re.sub(r'🔗 連結：[\s\S]*?(?=\n[💡🏷️📰⏰📌]|\Z)', f"🔗 連結：{url}", entry, flags=re.MULTILINE)
        macro_entries.append(entry)
        macro_pushed.add(title)
        add_macro_keyword(title, cache["macro"], date_str)

    # 🚨 個股解析與過濾日誌
    stock_dedups = []
    for entry in parse_entries(stock_text):
        title, stock_field = extract_field(entry, "📰 新聞標題") or entry[:60], extract_field(entry, "🏷️ 股票")
        code_m = re.search(r'(\d{5})\.HK', stock_field) or re.search(r'(\d{5})\.HK', entry)
        if not code_m:
            print(f"🚫 搵唔到股票代號，丟棄: {title[:40]}")
            continue
            
        code = f"{code_m.group(1)}.HK"
        news_time, valid = parse_entry_time(entry)
        if not valid:
            print(f"🚫 {code} 時間不明/含禁止詞，丟棄: {title[:40]}")
            continue
        if news_time and not (news_after <= news_time <= now_hkt + timedelta(minutes=10)):
            print(f"🚫 {code} 超出時間範圍，丟棄: {title[:40]} ({format_hkt(news_time)})")
            continue
        
        dedup_key = f"{code}|{news_time.strftime('%Y-%m-%d') if news_time else date_str}"
        if dedup_key in cache["stock"] or dedup_key in stock_pushed["keys"] or is_duplicate_stock_title(title, code, stock_pushed["titles"]):
            print(f"🔁 {code} 新聞重複或已推送，跳過: {title[:40]}")
            continue
        
        url = get_url_for_entry(entry)
        if url: entry = re.sub(r'🔗 連結：[\s\S]*?(?=\n[💡🏷️📰⏰📌]|\Z)', f"🔗 連結：{url}", entry, flags=re.MULTILINE)
        stock_entries.append(entry)
        stock_dedups.append((dedup_key, title[:100], code, normalize_stock_title(title)))

    if len(stock_entries) > config["filters"]["max_stock_news"]:
        print(f"⚠️ 個股新聞 {len(stock_entries)} 條，截斷至 {config['filters']['max_stock_news']} 條")
        stock_entries, stock_dedups = stock_entries[:config["filters"]["max_stock_news"]], stock_dedups[:config["filters"]["max_stock_news"]]

    for dk, st, cd, nt in stock_dedups:
        cache["stock"][dk] = st
        stock_pushed["keys"].add(dk)
        stock_pushed["titles"].append((cd, nt))

    # 🚨 打印解析統計結果
    print(f"📊 解析結果：板塊 {len(macro_entries)} 條，個股 {len(stock_entries)} 條")

    if not macro_entries and not stock_entries:
        print("ℹ️ 篩選後無新內容，唔推送")
        save_cache(cache, config)
        return False

    # 🚨 組合飛書訊息與搜尋統計
    source_domains, vertex_count = count_source_domains(grounding_urls)
    if source_domains:
        source_summary = f"{len(source_domains)} 個新聞源：{', '.join(source_domains)}"
    elif vertex_count:
        source_summary = f"{vertex_count} 個 Google 搜尋結果"
    else:
        source_summary = ""

    parts = []
    if macro_entries: parts.extend(["=== 【板塊宏觀消息】 ===", "\n\n".join(macro_entries)])
    if stock_entries: parts.extend(["=== 【個股重大利好】 ===", "\n\n".join(stock_entries)])
    
    final_text = format_links("\n\n".join(parts))
    if source_summary:
        final_text += f"\n\n---\n📡 本次搜尋咗 {source_summary}"
        
    send_feishu(final_text, config)
    save_cache(cache, config)
    return True

# ============================================================
# 主流程與進程鎖
# ============================================================
def acquire_lock():
    if LOCK_FILE.exists():
        try:
            if time.time() - float(LOCK_FILE.read_text().strip()) > 1800: LOCK_FILE.unlink()
            else: return False
        except Exception: LOCK_FILE.unlink()
    try: LOCK_FILE.write_text(str(time.time())); return True
    except Exception: return False
def release_lock():
    try:
        if LOCK_FILE.exists(): LOCK_FILE.unlink()
    except Exception: pass

def main():
    config = load_config()
    now_hkt = get_hkt_now()
    force_run = os.getenv("FORCE_RUN", "false").lower() == "true"
    
    print("=" * 60)
    print(f"=== HKT 現在時間: {now_hkt.strftime('%Y-%m-%d %H:%M:%S')} {WEEKDAY_CN[now_hkt.weekday()]} ===")
    
    if not (stock_prompt := os.getenv("HK_NEWS_PROMPT_STOCK", "").strip()):
        print("❌ HK_NEWS_PROMPT_STOCK 未設置"); sys.exit(1)
    macro_prompt = os.getenv("HK_NEWS_PROMPT_MACRO", "").strip()

    if force_run:
        session_name = get_force_run_session(now_hkt)
        print(f"⚠️ FORCE_RUN 模式：即時跑一次 ({session_name})")
        run_mode = "one_shot"
    else:
        if is_weekend(now_hkt): return print("ℹ️ 週末，自動退出")
        if not (session_name := get_session(now_hkt, config)): return print("ℹ️ 唔在任何執行窗口，退出")
        run_mode = "long_run"

    print(f"=== 新聞有效範圍: {format_hkt(calc_news_after(session_name, now_hkt, config))} ~ {format_hkt(now_hkt)} ===")
    if not acquire_lock(): return print("⚠️ 已有另一個實例在執行，跳過")

    try:
        if run_mode == "one_shot":
            scan_once(session_name, 1, set(), {"keys": set(), "titles": []}, config, (macro_prompt, stock_prompt))
        elif run_mode == "long_run":
            turn, macro_pushed, stock_pushed = 0, set(), {"keys": set(), "titles": []}
            while True:
                turn += 1
                print(f"\n{'─' * 50}\n--- Turn {turn} | {get_hkt_now().strftime('%H:%M:%S')} HKT ---\n{'─' * 50}")
                if scan_once(session_name, turn, macro_pushed, stock_pushed, config, (macro_prompt, stock_prompt)) == "quota_exhausted":
                    print("\n🚫 Gemini 配額已用盡，結束 session"); break
                if is_session_over(session_name, get_hkt_now(), config):
                    print("\n🏁 已到 session 結束時間，退出迴圈"); break
                
                sleep_sec = random.randint(config["scan"]["interval_min_min"] * 60, config["scan"]["interval_min_max"] * 60)
                print(f"💤 休眠 {sleep_sec // 60} 分 {sleep_sec % 60} 秒...")
                time.sleep(sleep_sec)
    finally:
        release_lock()

if __name__ == "__main__":
    main()
