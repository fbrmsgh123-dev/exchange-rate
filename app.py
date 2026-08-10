"""일자별 환율 현황 - Streamlit 버전.

Next.js로 만든 원본 대시보드(PRD.md 기준)를 단일 파일 Streamlit 앱으로
포팅한 것. 네이버 금융에서 실시간 환율 + 30일 히스토리를 크롤링하고,
규칙 기반 특이사항 요약과 카드/그래프 UI를 제공한다.
"""

from __future__ import annotations

import hashlib
import json
import math
import os
import tempfile
import threading
from datetime import date, datetime, timedelta, timezone

import pandas as pd
import plotly.graph_objects as go
import requests
import streamlit as st
from bs4 import BeautifulSoup
from streamlit_autorefresh import st_autorefresh

# ---------------------------------------------------------------------------
# 상수
# ---------------------------------------------------------------------------

KST = timezone(timedelta(hours=9))

CURRENCIES = [
    {"code": "USD", "label": "미국 달러", "unit": "1 USD"},
    {"code": "EUR", "label": "유로", "unit": "1 EUR"},
    {"code": "JPY", "label": "일본 옌", "unit": "100 JPY"},
    {"code": "CNY", "label": "중국 위안", "unit": "1 CNY"},
]
CURRENCY_CODES = [c["code"] for c in CURRENCIES]
CURRENCY_META = {c["code"]: c for c in CURRENCIES}

HISTORY_DAYS = 30
POLL_INTERVAL_SEC = 60

# 환율은 통계적으로 랜덤워크에 가까워 "예측"이라 부를 만한 신뢰도는 없다.
# 아래 forecast 관련 함수는 최근 N일 추세를 최소자승 선형회귀로 연장한
# 참고용 추정치만 만들며, UI에서도 반드시 "추정/참고용"으로 표시한다.
FORECAST_WINDOW_DAYS = 14
FORECAST_HORIZON_DAYS = 7

DATA_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data")
# Next.js 버전(lib/storage.ts)도 이 폴더에 data/rates.json(camelCase 스키마)을
# 쓴다. 같은 파일명을 쓰면 두 앱을 같은 디렉터리에서 같이 돌릴 때 스키마가
# 달라(snake_case) 서로의 데이터를 깨뜨릴 수 있어 파일명을 분리했다.
DATA_FILE = os.path.join(DATA_DIR, "streamlit_rates.json")

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
)
MARKET_INDEX_URL = "https://finance.naver.com/marketindex/"

# dataviz 팔레트 카테고리 슬롯 1~4를 통화별로 고정 배정(필터링해도 색 불변).
CURRENCY_COLOR = {
    "USD": "#2a78d6",  # blue
    "EUR": "#eb6834",  # orange
    "JPY": "#1baf7a",  # aqua
    "CNY": "#eda100",  # yellow
}
DELTA_UP_COLOR = "#e34948"  # 상승 = 빨강 (국내 관례)
DELTA_DOWN_COLOR = "#2a78d6"  # 하락 = 파랑
DELTA_FLAT_COLOR = "#898781"  # 변동 없음 = 중립 회색

BIG_MOVE_PCT = 1.0
NOTABLE_MOVE_PCT = 0.5
STREAK_MIN_DAYS = 3
DEVIATION_SIGMA = 2.0
MIN_DAYS_FOR_DEVIATION = 5

TAG_LABELS = {
    "big_move": "큰 변동",
    "notable_move": "변동 확대",
    "30d_high": "30일 신고가",
    "30d_low": "30일 신저가",
    "streak": "연속 추세",
    "deviation": "평균 이탈",
}


def daily_quote_url(code: str, page: int) -> str:
    return (
        "https://finance.naver.com/marketindex/exchangeDailyQuote.naver"
        f"?marketindexCd=FX_{code}KRW&page={page}"
    )


# ---------------------------------------------------------------------------
# 저장소 (로컬 JSON 파일)
# ---------------------------------------------------------------------------

_write_lock = threading.Lock()


def _empty_store() -> dict:
    return {"latest": {}, "history": {}}


def _read_store() -> dict:
    try:
        with open(DATA_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return _empty_store()


def _write_store(store: dict) -> None:
    os.makedirs(DATA_DIR, exist_ok=True)
    # 임시 파일에 쓰고 os.replace(원자적 교체)로 바꿔친다. 대상 파일에 직접
    # 쓰면 그 순간 걸린 read가 절반만 쓰인 JSON을 볼 수 있다.
    fd, tmp_path = tempfile.mkstemp(dir=DATA_DIR, prefix="rates.", suffix=".tmp")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            json.dump(store, f, ensure_ascii=False, indent=2)
        os.replace(tmp_path, DATA_FILE)
    except Exception:
        if os.path.exists(tmp_path):
            os.remove(tmp_path)
        raise


def today_kst_str() -> str:
    return datetime.now(KST).strftime("%Y-%m-%d")


def parse_iso(s: str) -> datetime:
    """수집 경로별로 형식이 다른(Z / +09:00, 밀리초 유무) ISO 문자열을 안전하게 파싱."""
    if s.endswith("Z"):
        s = s[:-1] + "+00:00"
    return datetime.fromisoformat(s)


def get_latest(code: str) -> dict | None:
    return _read_store()["latest"].get(code)


def get_all_latest() -> dict:
    store = _read_store()
    return {c: store["latest"][c] for c in CURRENCY_CODES if c in store["latest"]}


def set_latest(code: str, latest: dict) -> None:
    with _write_lock:
        store = _read_store()
        store["latest"][code] = latest
        _write_store(store)


def get_history(code: str, days: int = HISTORY_DAYS) -> list[dict]:
    store = _read_store()
    return store["history"].get(code, [])[-days:]


def get_all_history(days: int = HISTORY_DAYS) -> dict:
    store = _read_store()
    return {c: store["history"].get(c, [])[-days:] for c in CURRENCY_CODES}


def upsert_snapshot(code: str, snapshot: dict) -> None:
    with _write_lock:
        store = _read_store()
        series = store["history"].get(code, [])
        for i, s in enumerate(series):
            if s["date"] == snapshot["date"]:
                series[i] = snapshot
                break
        else:
            series.append(snapshot)
            series.sort(key=lambda s: s["date"])
        store["history"][code] = series[-HISTORY_DAYS * 2 :]
        _write_store(store)


# ---------------------------------------------------------------------------
# 네이버 크롤링
# ---------------------------------------------------------------------------


def _fetch_euckr_html(url: str) -> str:
    # 네이버 금융 페이지는 EUC-KR(사실상 CP949) 인코딩. response.text를 쓰면
    # requests가 잘못된 인코딩을 추측해 한글이 깨진다.
    res = requests.get(url, headers={"User-Agent": USER_AGENT}, timeout=10)
    res.raise_for_status()
    return res.content.decode("cp949", errors="replace")


def _parse_live_rate(soup: BeautifulSoup, code: str, today: str) -> dict:
    anchor = soup.select_one(f"a.head.{code.lower()}")
    if anchor is None:
        raise ValueError(f"{code} 항목을 찾을 수 없음 (네이버 페이지 구조 변경 가능성)")

    info = anchor.find("div", class_="head_info")
    if info is None:
        raise ValueError(f"{code} head_info 영역을 찾을 수 없음")

    value_span = info.find("span", class_="value")
    change_span = info.find("span", class_="change")
    rate_text = value_span.get_text(strip=True) if value_span else ""
    change_text = change_span.get_text(strip=True) if change_span else ""

    try:
        rate = float(rate_text.replace(",", ""))
        change_abs = float(change_text.replace(",", ""))
    except ValueError as e:
        raise ValueError(
            f"{code} 값 파싱 실패 (value={rate_text!r}, change={change_text!r})"
        ) from e

    is_down = "point_dn" in (info.get("class") or [])
    change = -change_abs if is_down else change_abs

    li = anchor.find_parent("li")
    time_span = li.select_one(".graph_info .time") if li else None
    time_text = time_span.get_text(strip=True) if time_span else ""  # "YYYY.MM.DD HH:mm"

    observed_date = time_text[:10].replace(".", "-") if time_text else today
    market_status = "open" if observed_date == today else "closed"
    if time_text:
        observed_at = f"{observed_date}T{time_text[11:]}:00+09:00"
    else:
        observed_at = datetime.now(timezone.utc).isoformat()

    return {
        "currency": code,
        "rate": rate,
        "change": change,
        "market_status": market_status,
        "observed_at": observed_at,
    }


def fetch_live_rates() -> tuple[dict, list[str]]:
    """네이버 환율 메인 페이지에서 4개 통화 현재값을 읽는다.

    통화 하나의 파싱이 실패해도 나머지는 계속 처리한다.
    """
    html = _fetch_euckr_html(MARKET_INDEX_URL)
    soup = BeautifulSoup(html, "html.parser")
    today = today_kst_str()

    rates: dict[str, dict] = {}
    errors: list[str] = []

    for code in CURRENCY_CODES:
        try:
            rates[code] = _parse_live_rate(soup, code, today)
        except Exception as e:
            errors.append(str(e))

    return rates, errors


def fetch_history_from_naver(code: str, days: int = HISTORY_DAYS) -> list[dict]:
    """네이버 "일별 환율" 표에서 과거 매매기준율을 페이지 단위(10건)로 가져온다.

    페이지 하나(요청 하나)가 실패해도 이미 받아온 다른 페이지 데이터는
    버리지 않는다. 3페이지 중 하나만 일시적으로 실패해도 나머지 20일치라도
    남기는 게, 전체를 예외로 날려서 30일 전체를 더미로 덮어써 버리는 것보다
    낫다. 한 건도 못 받았을 때만 예외를 던져 상위(ensure_seed_data)의 더미
    대체 로직이 동작하게 한다.
    """
    pages = math.ceil(days / 10)
    snapshots: list[dict] = []
    page_errors: list[str] = []

    for page in range(1, pages + 1):
        try:
            _collect_daily_quote_page(code, page, snapshots)
        except Exception as e:
            page_errors.append(f"page {page}: {e}")

    if not snapshots and page_errors:
        raise RuntimeError(f"{code} 히스토리 전 페이지 수집 실패: {'; '.join(page_errors)}")
    if page_errors:
        print(f"[history] {code} 일부 페이지 실패(나머지는 유지): {'; '.join(page_errors)}")

    return sorted(snapshots, key=lambda s: s["date"])[-days:]


def _collect_daily_quote_page(code: str, page: int, snapshots: list[dict]) -> None:
    html = _fetch_euckr_html(daily_quote_url(code, page))
    soup = BeautifulSoup(html, "html.parser")
    table = soup.select_one("table.tbl_exchange")
    if table is None:
        return

    for row in table.select("tbody tr"):
        date_td = row.find("td", class_="date")
        if not date_td or not date_td.get_text(strip=True):
            continue  # 레이아웃용 빈 행

        num_tds = row.find_all("td", class_="num")
        if not num_tds:
            continue
        rate_text = num_tds[0].get_text(strip=True)
        try:
            rate = float(rate_text.replace(",", ""))
        except ValueError:
            continue

        date = date_td.get_text(strip=True).replace(".", "-")
        snapshots.append(
            {
                "currency": code,
                "date": date,
                "rate": rate,
                "collected_at": f"{date}T09:00:00+09:00",
            }
        )


def collect_and_store() -> tuple[int, list[str]]:
    """실시간 크롤링 -> 저장소 반영까지 한 번에 수행."""
    rates, errors = fetch_live_rates()
    today = today_kst_str()
    updated = 0

    for code, live in rates.items():
        prev_close = round(live["rate"] - live["change"], 2)
        change_pct = round((live["change"] / prev_close) * 100, 2) if prev_close else 0.0

        latest = {
            "currency": code,
            "rate": live["rate"],
            "prev_close": prev_close,
            "change": live["change"],
            "change_pct": change_pct,
            "updated_at": live["observed_at"],
            "market_status": live["market_status"],
        }

        upsert_snapshot(
            code,
            {
                "currency": code,
                "date": today,
                "rate": live["rate"],
                "collected_at": datetime.now(timezone.utc).isoformat(),
            },
        )
        set_latest(code, latest)
        updated += 1

    return updated, errors


# ---------------------------------------------------------------------------
# 크롤링 실패 시 대체용 더미 히스토리
# ---------------------------------------------------------------------------

_BASE_RATES = {"USD": 1370.0, "EUR": 1470.0, "JPY": 930.0, "CNY": 190.0}


def _seeded_random(seed: str) -> float:
    h = int(hashlib.md5(seed.encode("utf-8")).hexdigest(), 16)
    return (h % 10_000) / 10_000


def generate_dummy_history(code: str, days: int = HISTORY_DAYS) -> list[dict]:
    base = _BASE_RATES[code]
    out: list[dict] = []
    for i in range(days - 1, -1, -1):
        d = (datetime.now(KST) - timedelta(days=i)).strftime("%Y-%m-%d")
        drift = (_seeded_random(f"{code}-{d}") - 0.5) * base * 0.02
        rate = round(base + drift, 2)
        out.append(
            {"currency": code, "date": d, "rate": rate, "collected_at": f"{d}T09:00:00+09:00"}
        )
    return out


# ---------------------------------------------------------------------------
# 최초 시딩 (30일 히스토리 백필)
# ---------------------------------------------------------------------------

_seed_lock = threading.Lock()


def ensure_seed_data() -> None:
    """통화별로 히스토리가 없으면 네이버에서 백필한다(실패 시 더미로 대체).

    락으로 전체를 감싸 여러 세션이 동시에 콜드 스타트에 진입해도 중복
    크롤링하지 않는다. 완료 여부를 통화 단위로 확인하므로, 이전 실행이
    중간에 실패해도 남은 통화만 이어서 채운다.
    """
    with _seed_lock:
        for code in CURRENCY_CODES:
            if get_latest(code) is not None:
                continue

            try:
                history = fetch_history_from_naver(code)
                if not history:
                    raise ValueError("빈 응답")
            except Exception as e:
                print(f"[seed] {code} 네이버 히스토리 수집 실패, 더미 데이터로 대체: {e}")
                history = generate_dummy_history(code)

            for snap in history:
                upsert_snapshot(code, snap)

            today_snap = history[-1]
            prev_snap = history[-2] if len(history) > 1 else today_snap
            change = round(today_snap["rate"] - prev_snap["rate"], 2)
            change_pct = (
                round((change / prev_snap["rate"]) * 100, 2) if prev_snap["rate"] else 0.0
            )
            set_latest(
                code,
                {
                    "currency": code,
                    "rate": today_snap["rate"],
                    "prev_close": prev_snap["rate"],
                    "change": change,
                    "change_pct": change_pct,
                    "updated_at": datetime.now(timezone.utc).isoformat(),
                    "market_status": "open",
                },
            )


# ---------------------------------------------------------------------------
# 특이사항 규칙 기반 요약
# ---------------------------------------------------------------------------


def _average(nums: list[float]) -> float:
    return sum(nums) / len(nums)


def _std_dev(nums: list[float], mean: float) -> float:
    variance = sum((n - mean) ** 2 for n in nums) / len(nums)
    return variance**0.5


def compute_streak(rates: list[float]) -> int:
    """rates는 오래된 -> 최신 순. 마지막 값 기준 연속 상승(+)/하락(-) 일수."""
    streak = 0
    for i in range(len(rates) - 1, 0, -1):
        diff = rates[i] - rates[i - 1]
        if diff == 0:
            break
        sign = 1 if diff > 0 else -1
        if streak == 0:
            streak = sign
        elif (streak > 0) == (sign > 0):
            streak += sign
        else:
            break
    return streak


def summarize_currency(latest: dict, history: list[dict]) -> dict:
    tags: list[str] = []
    messages: list[str] = []

    abs_pct = abs(latest["change_pct"])
    signed_pct = f"{'+' if latest['change_pct'] >= 0 else ''}{latest['change_pct']}%"

    if abs_pct >= BIG_MOVE_PCT:
        tags.append("big_move")
        messages.append(f"전일 대비 큰 변동({signed_pct})")
    elif abs_pct >= NOTABLE_MOVE_PCT:
        tags.append("notable_move")
        messages.append(f"전일 대비 변동폭이 다소 큼({signed_pct})")

    # history의 마지막 항목은 항상 latest와 같은 날짜/값으로 동기화되어
    # 있으므로 latest["rate"]를 따로 덧붙이지 않는다(중복하면 streak의
    # 마지막 일별 변동이 항상 0이 되는 버그가 생긴다).
    rates = [h["rate"] for h in history] if history else [latest["rate"]]
    hi, lo = max(rates), min(rates)

    if len(rates) > 1:
        if latest["rate"] >= hi and latest["rate"] > lo:
            tags.append("30d_high")
            messages.append(f"최근 {len(rates)}일 중 최고가")
        elif latest["rate"] <= lo and latest["rate"] < hi:
            tags.append("30d_low")
            messages.append(f"최근 {len(rates)}일 중 최저가")

    streak = compute_streak(rates)
    if abs(streak) >= STREAK_MIN_DAYS:
        tags.append("streak")
        messages.append(f"{abs(streak)}일 연속 {'상승' if streak > 0 else '하락'}")

    if len(rates) >= MIN_DAYS_FOR_DEVIATION:
        mean = _average(rates)
        std = _std_dev(rates, mean)
        if std > 0 and abs(latest["rate"] - mean) / std >= DEVIATION_SIGMA:
            tags.append("deviation")
            messages.append(f"최근 평균({mean:,.0f}) 대비 크게 이탈")

    if not messages:
        messages.append("평소와 유사한 흐름")

    return {"currency": latest["currency"], "message": ". ".join(messages), "tags": tags}


# ---------------------------------------------------------------------------
# 추세 연장 (참고용 추정치, 실제 예측 아님)
# ---------------------------------------------------------------------------


def _linear_regression(ys: list[float]) -> tuple[float, float]:
    n = len(ys)
    mean_x = (n - 1) / 2
    mean_y = sum(ys) / n

    num = sum((i - mean_x) * (y - mean_y) for i, y in enumerate(ys))
    den = sum((i - mean_x) ** 2 for i in range(n))

    slope = num / den if den else 0.0
    intercept = mean_y - slope * mean_x
    return slope, intercept


def _next_business_date(d: date) -> date:
    nd = d + timedelta(days=1)
    while nd.weekday() >= 5:  # 5=토, 6=일
        nd += timedelta(days=1)
    return nd


def build_forecast(
    series: list[dict],
    window_days: int = FORECAST_WINDOW_DAYS,
    horizon_days: int = FORECAST_HORIZON_DAYS,
) -> list[dict]:
    """최근 window_days일 추세를 선형회귀로 horizon_days 영업일만큼 연장한다.

    실제 예측이 아니다(환율은 랜덤워크에 가까워 신뢰할 수 있는 예측이
    거의 불가능하다) — 호출부(UI)에서 반드시 "추정/참고용"으로 표시할 것.
    """
    if len(series) < 2:
        return []

    window = series[-window_days:]
    ys = [s["rate"] for s in window]
    slope, intercept = _linear_regression(ys)

    cursor = datetime.strptime(window[-1]["date"], "%Y-%m-%d").date()
    points: list[dict] = []
    for i in range(1, horizon_days + 1):
        cursor = _next_business_date(cursor)
        x = len(ys) - 1 + i
        rate = round(slope * x + intercept, 2)
        points.append({"date": cursor.strftime("%Y-%m-%d"), "rate": rate})
    return points


# ---------------------------------------------------------------------------
# 캐시된 데이터 로더 (1분 주기 갱신)
# ---------------------------------------------------------------------------


@st.cache_data(ttl=POLL_INTERVAL_SEC, show_spinner=False)
def load_dashboard_data() -> dict:
    """st.cache_data(ttl=60)가 프로세스 전체에서 공유되므로, 여러 세션이
    동시에 새로고침해도 60초 창 안에서는 네이버를 한 번만 호출한다.
    """
    error: str | None = None

    try:
        ensure_seed_data()
    except Exception as e:
        error = f"초기 데이터 준비 실패: {e}"

    try:
        _, fetch_errors = collect_and_store()
        if fetch_errors:
            error = "일부 통화 수집 실패: " + ", ".join(fetch_errors)
    except Exception as e:
        error = f"네이버 실시간 페이지 조회 실패: {e}"

    rates = get_all_latest()
    history = get_all_history(HISTORY_DAYS)
    summaries = {c: summarize_currency(rates[c], history.get(c, [])) for c in rates}

    return {"rates": rates, "history": history, "summaries": summaries, "error": error}


# ---------------------------------------------------------------------------
# UI
# ---------------------------------------------------------------------------

STYLE = """
<style>
.rate-card { border:1px solid #e1e0d9; border-radius:12px; padding:16px; background:#fcfcfb; }
.rc-top { display:flex; justify-content:space-between; align-items:baseline; }
.rc-label { font-size:0.875rem; font-weight:600; color:#3f3e3b; }
.rc-unit { font-size:0.75rem; color:#898781; }
.rc-value { font-size:1.75rem; font-weight:700; margin:8px 0 4px; color:#0b0b0b; }
.rc-delta { font-size:0.9rem; font-weight:600; margin:0 0 8px; }
.rc-meta { font-size:0.75rem; color:#898781; }
.rc-badge { font-size:0.75rem; background:#fef3c7; color:#92400e; border-radius:6px; padding:2px 6px; }
.rc-empty { color:#898781; font-size:0.875rem; }
.summary-row { display:flex; gap:12px; padding:10px 0; border-bottom:1px solid #e1e0d9; align-items:baseline; flex-wrap:wrap; }
.summary-label { width:88px; flex-shrink:0; font-weight:600; font-size:0.875rem; color:#3f3e3b; }
.tag-badge { display:inline-block; border:1px solid #c3c2b7; border-radius:999px; padding:2px 8px; margin-right:6px; font-size:0.75rem; color:#52514e; }
.summary-msg { font-size:0.875rem; color:#52514e; }
</style>
"""


def render_rate_card(meta: dict, rate: dict | None) -> None:
    if rate is None:
        st.markdown(
            f"""<div class="rate-card"><p class="rc-label">{meta['label']} ({meta['unit']})</p>
            <p class="rc-empty">데이터 없음</p></div>""",
            unsafe_allow_html=True,
        )
        return

    change = rate["change"]
    is_up, is_down = change > 0, change < 0
    color = DELTA_UP_COLOR if is_up else DELTA_DOWN_COLOR if is_down else DELTA_FLAT_COLOR
    arrow = "▲" if is_up else "▼" if is_down else "–"
    sign = "+" if is_up else ""

    stale = rate["market_status"] == "closed"
    updated_dt = parse_iso(rate["updated_at"])
    updated_label = updated_dt.astimezone(KST).strftime("%m/%d %H:%M")
    minutes_ago = max(
        0,
        round(
            (datetime.now(timezone.utc) - updated_dt.astimezone(timezone.utc)).total_seconds()
            / 60
        ),
    )

    status_html = (
        f'<span class="rc-badge">휴장 · {updated_label} 기준</span>'
        if stale
        else f'<span class="rc-meta">갱신: {updated_label} ({minutes_ago}분 전)</span>'
    )

    st.markdown(
        f"""
        <div class="rate-card">
          <div class="rc-top"><span class="rc-label">{meta['label']}</span><span class="rc-unit">{meta['unit']}</span></div>
          <p class="rc-value">{rate['rate']:,.2f}</p>
          <p class="rc-delta" style="color:{color}">{arrow} {abs(change):,.2f} ({sign}{rate['change_pct']}%)</p>
          {status_html}
        </div>
        """,
        unsafe_allow_html=True,
    )


def _extreme_indices(values: list[float]) -> tuple[int, int]:
    hi_idx = max(range(len(values)), key=lambda i: values[i])
    lo_idx = min(range(len(values)), key=lambda i: values[i])
    return hi_idx, lo_idx


def build_currency_figure(
    code: str,
    series: list[dict],
    mode: str,
    summary: dict | None,
    show_forecast: bool = True,
) -> go.Figure:
    """통화 하나짜리 단독 차트. 통화마다 축 스케일이 달라(USD~1400대, JPY~900대
    등) 한 축에 같이 그리면 값이 작은 통화는 거의 안 보이므로 통화별로 분리해
    각자의 y축을 쓴다. 최고/최저/마지막(오늘) 지점에는 값을 직접 표시한다.
    """
    dates = [s["date"] for s in series]
    base = series[0]["rate"] if series else 0

    if mode == "절대값":
        values = [s["rate"] for s in series]

        def to_display(rate: float) -> float:
            return rate

        def value_fmt(v: float) -> str:
            return f"{v:,.0f}"

        hover_suffix = ""
    else:

        def to_display(rate: float) -> float:
            return round((rate / base - 1) * 100, 2) if base else 0.0

        values = [to_display(s["rate"]) for s in series]

        def value_fmt(v: float) -> str:
            return f"{v:+.2f}%"

        hover_suffix = "%"

    color = CURRENCY_COLOR[code]
    is_notable = bool(summary) and (
        "big_move" in summary["tags"] or "notable_move" in summary["tags"]
    )
    is_up_move = (is_notable and values[-1] >= values[-2]) if len(values) > 1 else False
    endpoint_color = (
        (DELTA_UP_COLOR if is_up_move else DELTA_DOWN_COLOR) if is_notable else color
    )

    fig = go.Figure()
    fig.add_trace(
        go.Scatter(
            x=dates,
            y=values,
            mode="lines",
            line=dict(color=color, width=2),
            hovertemplate=f"%{{y:,.2f}}{hover_suffix}<extra></extra>",
            showlegend=False,
        )
    )

    if values:
        last_idx = len(values) - 1
        hi_idx, lo_idx = _extreme_indices(values)

        # 우선순위: 마지막(오늘) > 최고 > 최저. 같은 지점이면 위치 하나만 남는다.
        positions: dict[int, str] = {hi_idx: "top center", lo_idx: "bottom center"}
        positions[last_idx] = "middle right" if last_idx not in (hi_idx, lo_idx) else positions[last_idx]

        idxs = sorted(positions)
        marker_colors = [endpoint_color if i == last_idx else color for i in idxs]
        marker_sizes = [10 if i == last_idx and is_notable else 8 for i in idxs]

        fig.add_trace(
            go.Scatter(
                x=[dates[i] for i in idxs],
                y=[values[i] for i in idxs],
                mode="markers+text",
                text=[value_fmt(values[i]) for i in idxs],
                textposition=[positions[i] for i in idxs],
                textfont=dict(size=11, color="#3f3e3b"),
                marker=dict(size=marker_sizes, color=marker_colors, line=dict(width=2, color="#fcfcfb")),
                showlegend=False,
                hoverinfo="skip",
            )
        )

    if show_forecast and series:
        forecast = build_forecast(series)
        if forecast:
            # 실선(실제)의 마지막 지점을 접합점으로 앞에 붙여, 점선이 끊기지
            # 않고 이어지는 것처럼 보이게 한다.
            f_dates = [dates[-1]] + [f["date"] for f in forecast]
            f_values = [values[-1]] + [to_display(f["rate"]) for f in forecast]

            fig.add_trace(
                go.Scatter(
                    x=f_dates,
                    y=f_values,
                    mode="lines",
                    line=dict(color=color, width=2, dash="dot"),
                    opacity=0.55,
                    hovertemplate=f"%{{y:,.2f}}{hover_suffix} (추정)<extra></extra>",
                    showlegend=False,
                )
            )
            fig.add_annotation(
                x=f_dates[-1],
                y=f_values[-1],
                text=f"{value_fmt(f_values[-1])} (추정)",
                showarrow=False,
                yshift=14,
                font=dict(size=10, color="#898781"),
            )

    fig.update_layout(
        title=dict(text=CURRENCY_META[code]["label"], font=dict(size=14, color="#3f3e3b")),
        margin=dict(l=8, r=8, t=36, b=8),
        height=260,
        plot_bgcolor="#fcfcfb",
        paper_bgcolor="#fcfcfb",
        font=dict(color="#52514e"),
        hovermode="x",
        showlegend=False,
        yaxis=dict(
            gridcolor="#e1e0d9",
            zerolinecolor="#c3c2b7",
            ticksuffix="%" if mode != "절대값" else "",
        ),
        xaxis=dict(showgrid=False),
    )
    return fig


def build_table_df(history: dict, selected: list[str], mode: str) -> pd.DataFrame:
    all_dates = sorted({s["date"] for series in history.values() for s in series})
    data: dict[str, list] = {"날짜": all_dates}

    for code in CURRENCY_CODES:
        if code not in selected:
            continue
        series = history.get(code, [])
        by_date = {s["date"]: s["rate"] for s in series}
        base = series[0]["rate"] if series else None

        col = []
        for d in all_dates:
            r = by_date.get(d)
            if r is None:
                col.append(None)
            elif mode == "절대값":
                col.append(r)
            else:
                col.append(round((r / base - 1) * 100, 2) if base else 0.0)
        data[CURRENCY_META[code]["label"]] = col

    return pd.DataFrame(data).sort_values("날짜", ascending=False).reset_index(drop=True)


def main() -> None:
    st.set_page_config(page_title="일자별 환율 현황", page_icon="💱", layout="wide")
    st.markdown(STYLE, unsafe_allow_html=True)
    st_autorefresh(interval=POLL_INTERVAL_SEC * 1000, key="autorefresh")

    data = load_dashboard_data()
    rates: dict = data["rates"]
    history: dict = data["history"]
    summaries: dict = data["summaries"]
    error: str | None = data["error"]

    header_col1, header_col2 = st.columns([3, 1])
    with header_col1:
        st.title("일자별 환율 현황")
        st.caption("USD · EUR · JPY · CNY 실시간 환율과 30일 추이")
    with header_col2:
        if rates:
            last_updated = max(rates.values(), key=lambda r: parse_iso(r["updated_at"]))
            st.caption(
                "마지막 갱신: "
                + parse_iso(last_updated["updated_at"]).astimezone(KST).strftime("%m/%d %H:%M")
            )

    if error:
        st.warning(
            f"최신 데이터를 갱신하지 못했습니다: {error}. "
            "마지막으로 정상 수집된 값을 계속 표시합니다."
        )

    if not rates:
        st.info("불러오는 중...")
        return

    cols = st.columns(4)
    for col, meta in zip(cols, CURRENCIES):
        with col:
            render_rate_card(meta, rates.get(meta["code"]))

    st.subheader("30일 추이")

    filter_cols = st.columns([1, 1, 1, 1, 1.4, 2, 2])
    selected: list[str] = []
    for col, meta in zip(filter_cols[:4], CURRENCIES):
        with col:
            if st.checkbox(meta["label"], value=True, key=f"filter_{meta['code']}"):
                selected.append(meta["code"])
    with filter_cols[4]:
        show_forecast = st.checkbox(f"향후 {FORECAST_HORIZON_DAYS}일 추세 연장", value=True)
    with filter_cols[5]:
        mode = st.radio(
            "표시 단위", ["절대값", "변화율(%)"], horizontal=True, label_visibility="collapsed"
        )
    with filter_cols[6]:
        show_table = st.checkbox("표로 보기")

    if show_forecast:
        st.caption(
            f"점선은 실제 예측이 아니라 최근 {FORECAST_WINDOW_DAYS}일 추세를 선형으로 "
            "연장한 참고용 추정치입니다. 환율은 등락을 예측하기 어려우니 참고만 하세요."
        )

    if show_table:
        st.dataframe(build_table_df(history, selected, mode), width="stretch")
    else:
        grid_cols = st.columns(2)
        for i, meta in enumerate(CURRENCIES):
            code = meta["code"]
            with grid_cols[i % 2]:
                if code not in selected:
                    st.caption(f"{meta['label']} (숨김)")
                    continue
                series = history.get(code, [])
                if not series:
                    st.caption(f"{meta['label']}: 히스토리 없음")
                    continue
                fig = build_currency_figure(code, series, mode, summaries.get(code), show_forecast)
                st.plotly_chart(fig, width="stretch")

    st.subheader("특이사항")
    for meta in CURRENCIES:
        summary = summaries.get(meta["code"])
        if not summary:
            continue
        badges = "".join(
            f'<span class="tag-badge">{TAG_LABELS.get(t, t)}</span>' for t in summary["tags"]
        )
        st.markdown(
            f'<div class="summary-row"><span class="summary-label">{meta["label"]}</span>'
            f'<span>{badges} <span class="summary-msg">{summary["message"]}</span></span></div>',
            unsafe_allow_html=True,
        )


if __name__ == "__main__":
    main()
