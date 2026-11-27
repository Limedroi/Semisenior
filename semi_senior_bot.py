"""
Semi Senior booking bot (Arabic).

Flow:  /start -> welcome + [أحجز معانا ❤️‍🔥] [🔎 حالة طلبي]
       -> name -> Telegram username -> phone -> هودي / بيسبول -> size (with size-guide link)
       -> payment screenshot (images only)
       -> the user gets everything back with [أضغط لتأكيد البيانات] / [الرجوع] and ✏️ buttons to fix one answer
       -> on confirm the application is SAVED as "pending" and sent to the admins with [قبول] / [رفض].
          ONLY an accepted application is posted to the results group. A rejection carries a reason, and the
          student can re-send just the screenshot.
Buttons flow in place (the same message turns into the next screen). Every step has [الرجوع].

Saving (same idea as the Quizician bot): users, applications, half-finished forms and settings are kept in a local
JSON file AND mirrored into a pinned, zipped backup in the storage group. Startup restores from that pin; backups are
throttled, skipped when nothing changed, retried by a background loop, and one last backup runs on shutdown.

Many students at once: updates run concurrently, each student's own messages are handled one at a time (so a
double-tap can't corrupt their form), each application can only be decided once even if both admins tap together,
and the last unit of a limited size can't be sold twice.

Railway variables (all optional except BOT_TOKEN):
    BOT_TOKEN              token from @BotFather
    ADMIN_IDS              admin Telegram ids, comma-separated. Default: 5242845517,940770584 — only these two can
                           use admin commands / accept applications (each must press /start once)
    GROUP_ID               results group for ACCEPTED applications, default -1005980424677
    STORAGE_GROUP_ID       backup group, default -1005738619227 — the bot must be an ADMIN there (send + pin)
    DATA_DIR               folder for the local JSON files (point it at a Railway volume if you have one)
    BACKUP_MIN_INTERVAL    seconds between backup uploads for real changes (default 60)
    DRAFT_BACKUP_MIN_INTERVAL  seconds between uploads when only half-finished forms changed (default 300)
    FINAL_BACKUP_TIMEOUT   seconds the last backup on shutdown may take (default 8)
    REMINDER_AFTER_HOURS   remind the admins about applications pending longer than this (default 6)
    MAX_CONCURRENT_UPDATES updates handled at the same time (default 128)

Admin commands (private chat): /pending /summary /stats /export /open /close /limit /health /backup /restore
                               /setwelcome (reply to a photo) /clearwelcome
Student commands: /start /status

requirements.txt:  python-telegram-bot[rate-limiter]>=21.0,<22
"""

import asyncio
import csv
import functools
import hashlib
import html
import json
import logging
import os
import re
import time
import weakref
import zipfile
from datetime import datetime, timedelta, timezone
from io import BytesIO, StringIO
from types import SimpleNamespace
from zoneinfo import ZoneInfo

from telegram import (
    BotCommand,
    BotCommandScopeAllPrivateChats,
    BotCommandScopeChat,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    InputFile,
    LinkPreviewOptions,
    ReplyParameters,
    Update,
)
from telegram.constants import ParseMode
from telegram.error import BadRequest, Forbidden
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

logging.basicConfig(format="%(asctime)s %(levelname)s %(name)s: %(message)s", level=logging.INFO)
log = logging.getLogger("semi_senior_bot")
_STARTED_AT = time.time()

# ── Config ────────────────────────────────────────────────────────────────────
BOT_TOKEN = os.environ.get("BOT_TOKEN", "")
GROUP_ID = int(os.environ.get("GROUP_ID", "-1005980424677"))                  # accepted applications only
STORAGE_GROUP_ID = int(os.environ.get("STORAGE_GROUP_ID", "-1005738619227"))  # pinned backups live here
_DEFAULT_ADMIN_IDS = "5242845517,940770584"      # the only people who can use the admin commands / accept applications
ADMIN_IDS = {int(x) for x in re.split(r"[,\s]+", (os.environ.get("ADMIN_IDS") or _DEFAULT_ADMIN_IDS).strip()) if x.lstrip("-").isdigit()}
DATA_DIR = os.environ.get("DATA_DIR", ".")
DATA_FILE = os.path.join(DATA_DIR, "semi_senior_data.json")
BACKUP_STATE_FILE = os.path.join(DATA_DIR, "semi_senior_backup_state.json")
BACKUP_MARKER = "🗄 SEMI_SENIOR_STORAGE_BACKUP"      # caption that identifies the pinned backup
BACKUP_JSON_NAME = "semi_senior_data.json"           # member inside the backup zip
BACKUP_MIN_INTERVAL = int(os.environ.get("BACKUP_MIN_INTERVAL", "60"))
DRAFT_BACKUP_MIN_INTERVAL = int(os.environ.get("DRAFT_BACKUP_MIN_INTERVAL", "300"))
FINAL_BACKUP_TIMEOUT = int(os.environ.get("FINAL_BACKUP_TIMEOUT", "8"))
RECONCILE_INTERVAL = 6 * 3600                        # re-check that the pinned backup is still there
REMINDER_AFTER_HOURS = float(os.environ.get("REMINDER_AFTER_HOURS", "6"))
MAX_CONCURRENT_UPDATES = int(os.environ.get("MAX_CONCURRENT_UPDATES", "128"))
BACKUP_ALERT_AFTER = 3                               # consecutive failed backups before the admins are told
DRAFT_TTL_DAYS = 7                                   # half-finished forms older than this are dropped
BLOCK_DUPLICATE_PHONE = False                        # True = only one active application per phone number
BLOCK_DUPLICATE_PHOTO = False                        # True = the same screenshot can't be used twice
WARN_DUPLICATE_PHOTO = True                          # admins are told on the card when ANOTHER person already used this screenshot
WARN_MAX_PEOPLE = 10                                 # how many other people are named (what doesn't fit on the card goes in a reply under it)
TZ = ZoneInfo("Africa/Cairo")
SIZE_GUIDE_URL = "https://t.me/Semi_senior44/2194"
MIN_NAME_WORDS = 2          # "الاسم الكامل" — set to 1 to accept a single word

# ── First-time onboarding: SEMI SENIOR, one big ASCII letter per message ───────
ONBOARDING_DELAY = 0.6      # seconds between the letters
ASCII_LETTERS = {
    "S": [" #### ",
          "#     ",
          " ###  ",
          "     #",
          " #### "],
    "E": ["######",
          "#     ",
          "####  ",
          "#     ",
          "######"],
    "M": ["#    #",
          "##  ##",
          "# ## #",
          "#    #",
          "#    #"],
    "I": ["######",
          "  ##  ",
          "  ##  ",
          "  ##  ",
          "######"],
    "N": ["#    #",
          "##   #",
          "# #  #",
          "#  # #",
          "#   ##"],
    "O": [" #### ",
          "#    #",
          "#    #",
          "#    #",
          " #### "],
    "R": ["##### ",
          "#    #",
          "##### ",
          "#   # ",
          "#    #"],
}
ONBOARDING_WORD = "SEMISENIOR"

# ── Texts (edit freely) ───────────────────────────────────────────────────────
WELCOME_HEAD = "أهلاً بيك في <b>Semi Senior</b> ❤️‍🔥"
WELCOME_TEXT = f"{WELCOME_HEAD}\n\nاضغط على الزرار اللي تحت عشان تحجز معانا، وهنسألك كام سؤال سريع."
CLOSED_TEXT = "🔒 الحجز مقفول دلوقتي، هنبلغكم لما يفتح تاني ❤️‍🔥"
BOOK_BTN = "أحجز معانا ❤️‍🔥"
STATUS_BTN = "🔎 حالة طلبي"
BACK_BTN = "الرجوع"
CONFIRM_BTN = "أضغط لتأكيد البيانات"
RESEND_BTN = "📤 ابعت صورة جديدة"
USE_USERNAME_BTN = "استخدم @{u} بتاعي"

Q_NAME = "أي هو أسمك الكامل"
Q_USERNAME = "أي هو اليوزر بتاعك على التليجرام"
Q_PHONE = "أي هو رقم تليفون"
Q_ITEM = "نفسك فأي؟!"
Q_SIZE = "أي هو مقاسك؟"
SIZE_NOTE = f'تقدر تعرف دليل المقاسات من <b><a href="{SIZE_GUIDE_URL}">اللينك ده</a></b>'
Q_PHOTO = "أبعت صورة/سكرين شوت بتمام إرسال المبلغ المطلوب"
Q_RESEND = "أبعت صورة/سكرين شوت التحويل الجديدة 📷"

SUBMITTED_TEXT = "تم استلام طلبك ✅\nهيتم مراجعته من الإدارة وهنبلغك بالنتيجة ❤️‍🔥"
ACCEPTED_TEXT = "تم قبول حجزك ✅\nشكراً ليك ❤️‍🔥"
ACCEPT_BTN = "✅ قبول"
REJECT_BTN = "❌ رفض"

# key -> (admin button, text the student sees, can the student re-send the screenshot?)
REJECT_REASONS = {
    "blur":     ("📷 الصورة مش واضحة", "الصورة اللي بعتها مش واضحة", True),
    "amount":   ("💰 المبلغ ناقص", "المبلغ المحوّل أقل من المطلوب", True),
    "notfound": ("🔎 التحويل مش ظاهر", "معرفناش نلاقي التحويل بالصورة دي", True),
    "final":    ("🚫 رفض نهائي", "تم رفض الطلب", False),
}

Q_PACK = "نفسك فأنهي باك؟"
PACKS_TEXT = """★سعر الباك الصغير 25ج
★المحتوي :
ميدالية 10
بريسلت 4
فريم تصوير صغير وقلم 10

★سعر الباك المتوسط " نظارة " 75ج
★المحتوي : نفس الصغير + نظارة


★سعر الباك المتوسط "كاب" 90ج
★المحتوي : نفس الباك الصغير + كاب

★سعر الباك الكبير 140ج
★المحتوي :
الباك الصغير + كاب و نظارة"""
# key -> button emoji, full name (receipts), short name (buttons/status), price in EGP
PACKS = {
    "small":   {"emoji": "🎁", "name": "الباك الصغير", "short": "الصغير", "price": 25},
    "glasses": {"emoji": "👓", "name": 'الباك المتوسط "نظارة"', "short": "المتوسط (نظارة)", "price": 75},
    "cap":     {"emoji": "🧢", "name": 'الباك المتوسط "كاب"', "short": "المتوسط (كاب)", "price": 90},
    "large":   {"emoji": "👑", "name": "الباك الكبير", "short": "الكبير", "price": 140},
}
PACK_ORDER = list(PACKS)

ITEMS = ["هودي", "بيسبول"]
SIZES = ["S", "M", "L", "XL"]
ITEM_EMOJI = {"هودي": "🧥", "بيسبول": "⚾"}
SIZE_EMOJI = "📏"

QUESTION_STEPS = ["name", "username", "phone", "item", "size", "pack", "photo"]
STEPS = QUESTION_STEPS + ["confirm"]
EDIT_LABELS = {"name": "الاسم", "username": "اليوزر", "phone": "الرقم", "item": "الطلب", "size": "المقاس", "pack": "الباك", "photo": "الصورة"}
NO_PREVIEW = LinkPreviewOptions(is_disabled=True)
LINE = "━━━━━━━━━━━━━━"

_DIGITS = str.maketrans("٠١٢٣٤٥٦٧٨٩۰۱۲۳۴۵۶۷۸۹", "01234567890123456789")


# ── Small helpers ─────────────────────────────────────────────────────────────
def _esc(value) -> str:
    return html.escape(str(value), quote=False)


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _fmt_time(iso) -> str:
    try:
        return datetime.fromisoformat(iso).astimezone(TZ).strftime("%d/%m/%Y %H:%M")
    except Exception:
        return iso or "-"


def _progress(step: str) -> str:
    n, total = QUESTION_STEPS.index(step) + 1, len(QUESTION_STEPS)
    return f"الخطوة {n} من {total}  {'▰' * n}{'▱' * (total - n)}"


def _item_label(item: str) -> str:
    return f"{ITEM_EMOJI.get(item, '🧥')} {item}"


def _pack_label(key: str) -> str:
    p = PACKS[key]
    return f"{p['emoji']} {p['short']} — {p['price']}ج"


def _pack_line(data: dict) -> str:
    p = PACKS.get(data.get("pack"))
    return f"\n{p['emoji']} الباك: {_esc(p['name'])} — {p['price']}ج" if p else ""


def _fields_html(data: dict) -> str:
    return (
        f"👤 الاسم: {_esc(data['name'])}\n"
        f"✈️ اليوزر: {_esc(data['username'])}\n"
        f"📱 رقم التليفون: {_esc(data['phone'])}\n"
        f"{ITEM_EMOJI.get(data['item'], '🧥')} الطلب: {_esc(data['item'])}\n"
        f"📏 المقاس: {_esc(data['size'])}"
        f"{_pack_line(data)}"
    )


def _status_line(rec: dict) -> str:
    if rec["status"] == "pending":
        return "⏳ قيد المراجعة"
    if rec["status"] == "accepted":
        return "✅ تم القبول"
    reason = rec.get("reject_reason")
    return "❌ مرفوض" + (f" — {_esc(reason)}" if reason else "")


def _receipt(data: dict, title: str, status_line: str = "") -> str:
    out = f"🧾 <b>{title}</b>\n{LINE}\n{_fields_html(data)}\n{LINE}"
    return f"{out}\n{status_line}" if status_line else out


def _back_row(step: str):
    return [InlineKeyboardButton(BACK_BTN, callback_data=f"back:{step}")]


def _kb_back(step: str, extra_rows=()) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([*extra_rows, _back_row(step)])


def _kb_choices(step: str, labels: list, per_row: int = 0) -> InlineKeyboardMarkup:
    btns = [InlineKeyboardButton(lab, callback_data=f"pick:{step}:{i}") for i, lab in enumerate(labels)]
    per_row = per_row or len(btns)
    return InlineKeyboardMarkup([btns[i:i + per_row] for i in range(0, len(btns), per_row)] + [_back_row(step)])


# ── Validation ────────────────────────────────────────────────────────────────
def clean_name(text: str):
    name = re.sub(r"\s+", " ", text).strip()
    if len(name) > 100 or len(name.split()) < MIN_NAME_WORDS or len(name) < 3:
        return None
    return name


def clean_username(text: str):
    t = text.strip()
    t = re.sub(r"^(https?://)?(www\.)?t\.me/", "", t, flags=re.I).lstrip("@").strip()
    if re.fullmatch(r"[A-Za-z][A-Za-z0-9_]{4,31}", t):
        return f"@{t}"
    return None


def clean_phone(text: str):
    t = text.translate(_DIGITS)
    t = re.sub(r"[\s\-().]", "", t)
    if re.fullmatch(r"\+?\d{8,15}", t):
        return t
    return None


# ── Data (users, applications, drafts, settings) ──────────────────────────────
# DATA = {"users": {"<tg id>": {...}}, "applications": {"<app id>": {...}}, "next_app_id": int,
#         "drafts": {"<tg id>": {...half-finished form...}}, "settings": {"open": bool, "limits": {...}, ...}}
# Every record carries "updated_at" (UTC ISO) — it decides which copy wins when a backup is merged in.
APP_STATUSES = ("pending", "accepted", "rejected")


def _valid_data(d) -> bool:
    return (
        isinstance(d, dict)
        and isinstance(d.get("users"), dict)
        and isinstance(d.get("applications"), dict)
        and isinstance(d.get("next_app_id"), int)
        and isinstance(d.get("drafts", {}), dict)
        and isinstance(d.get("settings", {}), dict)
        and all(isinstance(a, dict) and a.get("status") in APP_STATUSES for a in d["applications"].values())
        and all(isinstance(u, dict) for u in d["users"].values())
    )


def _load_json_file(path: str, default):
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except FileNotFoundError:
        return default
    except Exception as e:
        # Unreadable file: keep it for inspection instead of silently overwriting it.
        bad = f"{path}.corrupt-{int(time.time())}"
        try:
            os.replace(path, bad)
        except OSError:
            bad = "(could not move it)"
        log.error("Couldn't read %s (%s) — moved to %s, starting empty.", path, e, bad)
        return default


def _empty_data() -> dict:
    return {"users": {}, "applications": {}, "next_app_id": 1, "drafts": {}, "settings": {}}


DATA: dict = _load_json_file(DATA_FILE, None)
if not _valid_data(DATA):
    if DATA is not None:
        log.error("%s has the wrong structure — ignoring it.", DATA_FILE)
    DATA = _empty_data()
DATA.setdefault("drafts", {})
DATA.setdefault("settings", {})
BACKUP_STATE: dict = _load_json_file(BACKUP_STATE_FILE, {})
if not isinstance(BACKUP_STATE, dict):
    BACKUP_STATE = {}

_save_lock = asyncio.Lock()
_dirty = False               # something changed that isn't on disk yet (half-finished forms: written in batches)


def mark_dirty() -> None:
    global _dirty
    _dirty = True


def _atomic_write(path: str, text: str) -> None:
    os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
    tmp = f"{path}.tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(text)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)   # a crash mid-write can never leave a half-written data file


async def save_data() -> None:
    """The snapshot is taken INSIDE the lock, so when several saves queue up the last one to write is always
    the newest — an older snapshot can never overwrite a newer one."""
    global _dirty
    async with _save_lock:
        _dirty = False
        text = json.dumps(DATA, ensure_ascii=False)
        try:
            await asyncio.to_thread(_atomic_write, DATA_FILE, text)
        except Exception:
            _dirty = True
            raise


async def save_backup_state() -> None:
    async with _save_lock:
        text = json.dumps(BACKUP_STATE, ensure_ascii=False)
        await asyncio.to_thread(_atomic_write, BACKUP_STATE_FILE, text)


def touch_user(user) -> bool:
    """Records/refreshes a user. Returns True when something worth saving changed (a new user, or a
    new name/username) — plain activity only moves last_seen in memory, so it doesn't cause a backup."""
    uid = str(user.id)
    now = _now_iso()
    rec = DATA["users"].get(uid)
    if rec is None:
        DATA["users"][uid] = {"id": user.id, "username": user.username, "full_name": user.full_name,
                              "first_seen": now, "last_seen": now, "updated_at": now}
        return True
    rec["last_seen"] = now
    if rec.get("username") != user.username or rec.get("full_name") != user.full_name:
        rec["username"], rec["full_name"], rec["updated_at"] = user.username, user.full_name, now
        return True
    return False


async def commit() -> None:
    """Save locally now, then ask for a backup (throttled — see backup_to_storage)."""
    await save_data()
    request_backup(urgent=True)


# ── Settings: open/closed, size limits, welcome picture ───────────────────────
def _booking_open() -> bool:
    return DATA["settings"].get("open", True)


def _set_setting(key: str, value) -> None:
    DATA["settings"][key] = value
    DATA["settings"]["updated_at"] = _now_iso()


def _limit_for(item: str, size: str):
    return (DATA["settings"].get("limits") or {}).get(f"{item}|{size}")


def _taken(item: str, size: str) -> int:
    return sum(1 for a in DATA["applications"].values()
               if a["status"] in ("pending", "accepted") and a.get("item") == item and a.get("size") == size)


def _is_full(item: str, size: str) -> bool:
    lim = _limit_for(item, size)
    return lim is not None and _taken(item, size) >= lim


def _find_dup_phone(phone: str):
    """An active (pending/accepted) application with this phone number, if any."""
    for a in DATA["applications"].values():
        if a["status"] in ("pending", "accepted") and a.get("phone") == phone:
            return a
    return None


def _find_dup_photo(unique_id: str):
    """Any application that already used this exact screenshot (Telegram's file_unique_id)."""
    for a in DATA["applications"].values():
        if a.get("photo_uid") == unique_id:
            return a
    return None


def _photo_matches(rec: dict) -> list:
    """Applications from OTHER people that carry the same screenshot (Telegram's file_unique_id), oldest first.
    The same student re-using their own file is not "another person"."""
    uid = rec.get("photo_uid")
    if not uid:
        return []
    return sorted((a for a in DATA["applications"].values()
                   if a.get("photo_uid") == uid and a["id"] != rec["id"] and a["user_id"] != rec["user_id"]),
                  key=lambda a: a["id"])


_STATUS_SHORT = {"pending": "⏳ قيد المراجعة", "accepted": "✅ مقبول", "rejected": "❌ مرفوض"}


def _dup_entry(a: dict, rec: dict, verbose: bool) -> str:
    who = _esc((a.get("name") or "")[:40])
    acct = f" (@{_esc(a['tg_username'])})" if a.get("tg_username") else ""
    when = "قبل كده" if a["id"] < rec["id"] else "بعد كده"
    head = f'• #{a["id"]} — <a href="tg://user?id={a["user_id"]}">{who}</a>{acct}'
    if not verbose:
        return f'{head} — {_STATUS_SHORT[a["status"]]} — اتبعتت {when}'
    return (f'{head}\n   📱 {_esc(a.get("phone") or "-")}\n'
            f'   {_STATUS_SHORT[a["status"]]} · {_fmt_time(a["created_at"])} · اتبعتت {when}')


def _dup_photo_warning(rec: dict, n: int = WARN_MAX_PEOPLE, pointer: bool = False) -> str:
    """Text for the admin card: exactly WHO else sent this screenshot (name, account link, @username, application #,
    status). Names up to n people; the rest is a count (and a pointer to the reply under the card). Empty when
    nobody else did."""
    matches = _photo_matches(rec)
    if not WARN_DUPLICATE_PHOTO or not matches:
        return ""
    n = max(0, min(n, WARN_MAX_PEOPLE, len(matches)))
    lines = [_dup_entry(a, rec, False) for a in matches[:n]]
    if len(matches) > n:
        lines.append(f"… و{len(matches) - n} كمان" + (" — التفاصيل في الرسالة اللي تحت 👇" if pointer else ""))
    return "\n\n⚠️ <b>نفس صورة التحويل دي اتبعتت من شخص تاني:</b>\n" + "\n".join(lines)


def _dup_detail_message(rec: dict) -> str:
    """The full list (up to WARN_MAX_PEOPLE people, with phone numbers) — a plain message has room for it."""
    matches = _photo_matches(rec)
    body = "\n\n".join(_dup_entry(a, rec, True) for a in matches[:WARN_MAX_PEOPLE])
    extra = f"\n\n… و{len(matches) - WARN_MAX_PEOPLE} كمان" if len(matches) > WARN_MAX_PEOPLE else ""
    return f"⚠️ <b>طلب #{rec['id']} — نفس صورة التحويل اتبعتت من {len(matches)} شخص:</b>\n\n{body}{extra}"


class BookingError(Exception):
    """closed | full | dup_phone | dup_photo — raised before anything is stored."""
    def __init__(self, code: str, info=None):
        super().__init__(code)
        self.code, self.info = code, info


async def create_application(user, form_data: dict) -> dict:
    """Adds a pending application and saves it. All the checks and the insert happen with NO await in between,
    so two students confirming at the same moment can't both take the last unit of a size or the same phone number.
    If saving fails nothing is left half-added."""
    if not _booking_open():
        raise BookingError("closed")
    if _is_full(form_data["item"], form_data["size"]):
        raise BookingError("full")
    if BLOCK_DUPLICATE_PHONE and (dup := _find_dup_phone(form_data["phone"])):
        raise BookingError("dup_phone", dup["id"])
    if BLOCK_DUPLICATE_PHOTO and form_data.get("photo_uid") and (dup := _find_dup_photo(form_data["photo_uid"])):
        raise BookingError("dup_photo", dup["id"])
    app_id = DATA["next_app_id"]
    now = _now_iso()
    rec = {
        "id": app_id, "user_id": user.id, "tg_username": user.username, "tg_full_name": user.full_name,
        **{k: form_data[k] for k in ("name", "username", "phone", "item", "size", "pack", "photo_kind", "photo_id")},
        "photo_uid": form_data.get("photo_uid"),
        "status": "pending", "created_at": now, "updated_at": now,
        "decided_by": None, "decided_at": None, "reject_key": None, "reject_reason": None, "can_resend": False,
        "resubmits": 0, "history": [], "admin_msgs": {}, "group_msg_id": None, "user_msg_id": None,
    }
    DATA["next_app_id"] = app_id + 1
    DATA["applications"][str(app_id)] = rec
    touch_user(user)
    DATA["users"][str(user.id)]["updated_at"] = now
    DATA["users"][str(user.id)]["last_application_id"] = app_id
    try:
        await commit()
    except Exception:
        DATA["applications"].pop(str(app_id), None)
        DATA["next_app_id"] = app_id
        raise
    return rec


# ── Storage-group backup (same design as the Quizician bot's storage backup) ──
# One zip (a single JSON member) uploaded to the storage group and PINNED with a marker caption. On startup
# the pinned message is read back — a bot can't scan a group's history, but it can always read the pin.
RESTORE_OK = True            # False after a restore that failed for a real reason -> backups are paused so a
                             # failed restore can never overwrite the good backup with empty data
_backup_pending = False      # something changed since the last successful upload
_backup_urgent = False       # ...and part of it is a real change (not only half-finished forms)
_data_gen = 0                # bumped on every request_backup(); lets a finished upload tell if more changed meanwhile
_urgent_gen = 0
_last_backup_at = -1e9       # monotonic time of the last upload attempt (throttle)
_last_backup_ok_iso = None
_last_hash = None
_backup_fail_streak = 0
_backup_wakeup = asyncio.Event()
_backup_lock = asyncio.Lock()    # one backup at a time, built AFTER the lock is taken -> uploads are always in order
_alert_last: dict = {}


def request_backup(urgent: bool = True) -> None:
    """urgent = a real change (application, decision, setting...). Not urgent = only a half-finished form moved,
    which is backed up on the slower DRAFT_BACKUP_MIN_INTERVAL so students typing don't flood the storage group."""
    global _backup_pending, _backup_urgent, _data_gen, _urgent_gen
    _backup_pending = True
    _data_gen += 1
    if urgent:
        _backup_urgent, _urgent_gen = True, _data_gen
        _backup_wakeup.set()


def _backup_filename() -> str:
    return f"semi_senior_backup_{datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')}.zip"


def _build_backup_zip() -> bytes:
    buf = BytesIO()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as zf:
        zi = zipfile.ZipInfo(BACKUP_JSON_NAME, date_time=(2020, 1, 1, 0, 0, 0))   # fixed time: same data -> same bytes
        zi.compress_type = zipfile.ZIP_DEFLATED
        zf.writestr(zi, json.dumps(DATA, ensure_ascii=False, sort_keys=True))
    return buf.getvalue()


async def alert_admins(bot, kind: str, text: str, every: float = 6 * 3600) -> None:
    """DM the admins, at most once per `every` seconds per kind of alert."""
    now = time.monotonic()
    if now - _alert_last.get(kind, -1e9) < every:
        return
    _alert_last[kind] = now
    for admin_id in sorted(ADMIN_IDS):
        try:
            await bot.send_message(admin_id, text)
        except Exception:
            pass


async def backup_to_storage(context, force: bool = False, repair: bool = False) -> bool:
    """Uploads + pins the backup. force = skip the throttle; repair = also skip the "unchanged" check.
    Returns True when the backup is up to date (uploaded now, or identical to the last upload)."""
    global _backup_pending, _backup_urgent, _last_backup_at, _last_hash, _last_backup_ok_iso, _backup_fail_streak
    if not STORAGE_GROUP_ID:
        return False
    if not RESTORE_OK:
        log.error("BACKUP SKIPPED — the last restore failed, refusing to overwrite the storage-group backup. "
                  "Fix the problem and run /restore.")
        return False
    async with _backup_lock:
        now = time.monotonic()
        if not force and now - _last_backup_at < BACKUP_MIN_INTERVAL:
            _backup_pending = True          # the maintenance loop sends it once the interval has passed
            return False
        _last_backup_at = now
        gen = _data_gen
        raw = _build_backup_zip()
        digest = hashlib.sha1(raw).hexdigest()
        if not repair and digest == _last_hash:
            _backup_pending = _data_gen != gen
            _backup_urgent = _urgent_gen > gen
            return True
        try:
            sent = await context.bot.send_document(
                chat_id=STORAGE_GROUP_ID,
                document=InputFile(BytesIO(raw), filename=_backup_filename()),
                caption=BACKUP_MARKER,
            )
        except Exception as e:
            log.error("BACKUP UPLOAD FAILED: %s", e)
            _backup_pending = True          # retried by the maintenance loop
            _backup_fail_streak += 1
            if _backup_fail_streak >= BACKUP_ALERT_AFTER:
                await alert_admins(context.bot, "backup_fail",
                                   f"⚠️ النسخ الاحتياطي فشل {_backup_fail_streak} مرات ورا بعض:\n{e}\n"
                                   "اتأكد إن البوت أدمن في جروب التخزين.")
            return False
        _backup_fail_streak = 0
        _last_hash = digest
        _last_backup_ok_iso = _now_iso()
        _backup_pending = _data_gen != gen   # changed while uploading -> another round is needed
        _backup_urgent = _urgent_gen > gen
        # Remember the message id first — pinning is a nice-to-have on top and may fail (bot not admin).
        BACKUP_STATE["backup_msg_id"] = sent.message_id
        try:
            await save_backup_state()
        except Exception as e:
            log.error("Couldn't save backup state: %s", e)
        try:
            await context.bot.pin_chat_message(chat_id=STORAGE_GROUP_ID, message_id=sent.message_id,
                                               disable_notification=True)
        except Exception as e:
            log.error("BACKUP PIN FAILED (saved anyway, but a restart can't find it — make the bot an admin with "
                      "pin rights in the storage group): %s", e)
            await alert_admins(context.bot, "pin_fail",
                               "⚠️ البوت رفع النسخة الاحتياطية بس معرفش يثبّتها في جروب التخزين.\n"
                               "خلّيه أدمن وعنده صلاحية تثبيت الرسائل، وإلا الاستعادة بعد الريستارت مش هتلاقيها.")
        return True


class _BadBackup(Exception):
    pass


def _parse_backup(raw: bytes) -> dict:
    if not zipfile.is_zipfile(BytesIO(raw)):
        raise _BadBackup("the pinned document isn't a zip")
    with zipfile.ZipFile(BytesIO(raw)) as zf:
        if BACKUP_JSON_NAME not in zf.namelist():
            raise _BadBackup(f"the zip has no {BACKUP_JSON_NAME}")
        payload = json.loads(zf.read(BACKUP_JSON_NAME).decode("utf-8"))
    if not _valid_data(payload):
        raise _BadBackup("unexpected structure inside the backup")
    return payload


def _merge_data(payload: dict) -> None:
    """Backup records are added; when both sides have a record the one updated last wins."""
    for key in ("users", "applications"):
        for k, rec in payload[key].items():
            mine = DATA[key].get(k)
            if mine is None or (rec.get("updated_at") or "") > (mine.get("updated_at") or ""):
                DATA[key][k] = rec
    # half-finished forms come back too — unless that student submitted an application after the draft was saved
    latest_app: dict = {}
    for a in DATA["applications"].values():
        uid = str(a["user_id"])
        latest_app[uid] = max(latest_app.get(uid, ""), a.get("created_at") or "")
    for k, rec in (payload.get("drafts") or {}).items():
        if not isinstance(rec, dict) or (rec.get("updated_at") or "") <= latest_app.get(k, ""):
            continue
        mine = DATA["drafts"].get(k)
        if mine is None or (rec.get("updated_at") or "") > (mine.get("updated_at") or ""):
            DATA["drafts"][k] = rec
    ps = payload.get("settings") or {}
    if (ps.get("updated_at") or "") > (DATA["settings"].get("updated_at") or ""):
        DATA["settings"] = ps
    top = max((int(k) for k in DATA["applications"] if str(k).isdigit()), default=0) + 1
    DATA["next_app_id"] = max(DATA["next_app_id"], payload["next_app_id"], top)


async def restore_from_storage(bot) -> str:
    """Rebuilds the local data from the storage group's pinned backup. Returns "restored", "no_backup",
    "not_configured" or "failed: <why>" (and then pauses backups until a restore works)."""
    global RESTORE_OK, _last_hash
    if not STORAGE_GROUP_ID:
        return "not_configured"
    last_err = None
    for delay in (0, 3, 8):
        if delay:
            await asyncio.sleep(delay)
        try:
            chat = await bot.get_chat(STORAGE_GROUP_ID)
            pinned = chat.pinned_message
            if not pinned or not pinned.document or (pinned.caption or "") != BACKUP_MARKER:
                RESTORE_OK = True
                return "no_backup"
            tg_file = await bot.get_file(pinned.document.file_id)
            raw = bytes(await tg_file.download_as_bytearray())
            payload = _parse_backup(raw)
            _merge_data(payload)
            await save_data()
            BACKUP_STATE["backup_msg_id"] = pinned.message_id
            await save_backup_state()
            _last_hash = hashlib.sha1(raw).hexdigest()   # so an unchanged first backup is skipped
            RESTORE_OK = True
            log.info("Restored backup: %d user(s), %d application(s), %d draft(s).",
                     len(DATA["users"]), len(DATA["applications"]), len(DATA["drafts"]))
            return "restored"
        except (_BadBackup, BadRequest, Forbidden) as e:   # retrying won't help
            last_err = e
            break
        except Exception as e:                              # network hiccup — try again
            last_err = e
    RESTORE_OK = False
    log.error("RESTORE FAILED: %s", last_err)
    return f"failed: {last_err}"


async def reconcile_backup(context) -> None:
    """Every few hours: make sure the pinned backup is still there and is the one we know about."""
    if not STORAGE_GROUP_ID or not RESTORE_OK:
        return
    try:
        pinned = (await context.bot.get_chat(STORAGE_GROUP_ID)).pinned_message
    except Exception as e:
        log.error("Backup check failed: %s", e)
        return
    known = BACKUP_STATE.get("backup_msg_id")
    if (not pinned or (pinned.caption or "") != BACKUP_MARKER or (known and pinned.message_id != known)):
        log.warning("Pinned backup missing or replaced — uploading a fresh one.")
        await backup_to_storage(context, force=True, repair=True)


# ── Many students at once ─────────────────────────────────────────────────────
# Updates are processed concurrently (see main()). Two things keep that safe:
#   * each student's own updates run ONE AT A TIME (a double-tap or an album can't interleave),
#   * each application can only be decided/re-submitted by one coroutine at a time.
# Locks live in weak dictionaries, so idle ones disappear by themselves.
_user_locks: "weakref.WeakValueDictionary" = weakref.WeakValueDictionary()
_app_locks: "weakref.WeakValueDictionary" = weakref.WeakValueDictionary()


def _lock_for(registry, key) -> asyncio.Lock:
    lock = registry.get(key)
    if lock is None:
        lock = asyncio.Lock()
        registry[key] = lock
    return lock


def _form_sig(form) -> str:
    return json.dumps({k: v for k, v in form.items() if k != "updated_at"}, sort_keys=True)


def _persist_form(uid: str, context) -> None:
    """The student's form lives in DATA["drafts"] (so a redeploy doesn't lose a half-finished form).
    Welcome/status screens aren't worth saving; a finished or cancelled form is removed."""
    form = context.user_data.get("form")
    keep = form is not None and form.get("step") not in ("welcome", "status", "done")
    if not keep:
        if uid in DATA["drafts"]:
            del DATA["drafts"][uid]
            mark_dirty()
            request_backup(urgent=False)
        return
    old = DATA["drafts"].get(uid)
    if old is not form or _form_sig(form) != context.user_data.get("_form_sig"):
        form["updated_at"] = _now_iso()
        DATA["drafts"][uid] = form
        mark_dirty()
        request_backup(urgent=False)


def serialized(fn):
    """Per-student serialisation + loading/saving of that student's draft form around a handler."""
    @functools.wraps(fn)
    async def wrapper(update, context):
        user = update.effective_user
        if user is None:
            return await fn(update, context)
        async with _lock_for(_user_locks, user.id):
            uid = str(user.id)
            draft = DATA["drafts"].get(uid)
            if draft is not None:
                context.user_data["form"] = draft
                context.user_data["_form_sig"] = _form_sig(draft)
            else:
                context.user_data.pop("form", None)
                context.user_data.pop("_form_sig", None)
            context.user_data["tg_username"] = user.username
            try:
                return await fn(update, context)
            finally:
                _persist_form(uid, context)
    return wrapper


# ── Flow helpers ──────────────────────────────────────────────────────────────
def _form(context: ContextTypes.DEFAULT_TYPE):
    return context.user_data.get("form")


def _new_form(step: str = "welcome", **extra) -> dict:
    return {"step": step, "data": {}, "prompt_id": None, **extra}


async def _clear_prompt_buttons(context: ContextTypes.DEFAULT_TYPE, chat_id: int) -> None:
    """Remove the buttons from the last question so old buttons can't be pressed."""
    form = _form(context)
    pid = form.get("prompt_id") if form else None
    if not pid:
        return
    try:
        await context.bot.edit_message_reply_markup(chat_id=chat_id, message_id=pid, reply_markup=None)
    except Exception:
        pass   # already gone / unchanged — nothing to do
    form["prompt_id"] = None


async def _show(context: ContextTypes.DEFAULT_TYPE, chat_id: int, text: str, kb, edit=None) -> int:
    """Shows a screen. When `edit` (the message a button was pressed on) is a text message the screen is
    swapped IN PLACE — the button "flows" into the next thing without a new message. A photo message can't be
    turned into text, so that one is deleted and the screen sent fresh. Returns the id of the live message."""
    if edit is not None:
        if getattr(edit, "text", None):
            try:
                await context.bot.edit_message_text(text, chat_id=chat_id, message_id=edit.message_id,
                                                    parse_mode=ParseMode.HTML, reply_markup=kb,
                                                    link_preview_options=NO_PREVIEW)
                return edit.message_id
            except BadRequest as e:
                if "not modified" in str(e).lower():
                    return edit.message_id
            except Exception:
                pass   # fall back to a fresh message
        else:
            try:
                await context.bot.delete_message(chat_id, edit.message_id)
            except Exception:
                pass
    msg = await context.bot.send_message(chat_id, text, parse_mode=ParseMode.HTML,
                                         reply_markup=kb, link_preview_options=NO_PREVIEW)
    return msg.message_id


def _welcome_payload():
    rows = []
    if _booking_open():
        rows.append([InlineKeyboardButton(BOOK_BTN, callback_data="book")])
        text = WELCOME_TEXT
    else:
        text = f"{WELCOME_HEAD}\n\n{CLOSED_TEXT}"
    rows.append([InlineKeyboardButton(STATUS_BTN, callback_data="status")])
    return text, InlineKeyboardMarkup(rows)


async def send_welcome(context: ContextTypes.DEFAULT_TYPE, chat_id: int, edit=None) -> None:
    context.user_data["form"] = _new_form("welcome")
    text, kb = _welcome_payload()
    photo = DATA["settings"].get("welcome_photo_id")
    if edit is None and photo:          # banner as its own message, so the buttons below can still flow in place
        try:
            await context.bot.send_photo(chat_id, photo)
        except Exception as e:
            log.warning("Welcome picture couldn't be sent: %s", e)
    context.user_data["form"]["prompt_id"] = await _show(context, chat_id, text, kb, edit)


async def play_onboarding(context: ContextTypes.DEFAULT_TYPE, chat_id: int) -> None:
    """The very first /start a person ever sends: SEMISENIOR spelled out, one ASCII letter per message."""
    for i, letter in enumerate(ONBOARDING_WORD):
        art = "\n".join(ASCII_LETTERS[letter])
        try:
            await context.bot.send_message(chat_id, f"<pre>{art}</pre>", parse_mode=ParseMode.HTML)
        except Exception as e:
            log.error("Onboarding stopped at letter %s: %s", letter, e)
            return
        if i < len(ONBOARDING_WORD) - 1:
            await asyncio.sleep(ONBOARDING_DELAY)
    await asyncio.sleep(ONBOARDING_DELAY)


def _prompt(step: str, data: dict, tg_username=None):
    """-> (text, keyboard) for a question step."""
    head = _progress(step)
    if step == "name":
        return f"{head}\n\n{Q_NAME}", _kb_back(step)
    if step == "username":
        extra = []
        if tg_username and clean_username(tg_username):     # one tap instead of typing it
            extra = [[InlineKeyboardButton(USE_USERNAME_BTN.format(u=tg_username), callback_data="useun")]]
        return f"{head}\n\n{Q_USERNAME}", _kb_back(step, extra)
    if step == "phone":
        return f"{head}\n\n{Q_PHONE}", _kb_back(step)
    if step == "item":
        return f"{head}\n\n{Q_ITEM}", _kb_choices(step, [_item_label(i) for i in ITEMS])
    if step == "size":
        item = data.get("item")
        labels = [("❌ " if item and _is_full(item, s) else f"{SIZE_EMOJI} ") + s for s in SIZES]   # ❌ = sold out
        return f"{head}\n\n{Q_SIZE}\n\n{SIZE_NOTE}", _kb_choices(step, labels)
    if step == "pack":
        return f"{head}\n\n{Q_PACK}\n\n{PACKS_TEXT}", _kb_choices(step, [_pack_label(k) for k in PACK_ORDER], per_row=1)
    if step == "photo":
        return f"{head}\n\n{Q_PHOTO}", _kb_back(step)
    raise ValueError(step)


def _confirm_kb() -> InlineKeyboardMarkup:
    edit = lambda s: InlineKeyboardButton(f"✏️ {EDIT_LABELS[s]}", callback_data=f"edit:{s}")
    return InlineKeyboardMarkup([
        [edit("name"), edit("username"), edit("phone")],
        [edit("item"), edit("size"), edit("pack")],
        [edit("photo")],
        [InlineKeyboardButton(CONFIRM_BTN, callback_data="confirm")],
        _back_row("confirm"),
    ])


async def ask(context: ContextTypes.DEFAULT_TYPE, chat_id: int, step: str, edit=None) -> None:
    form = _form(context)
    form["step"] = step
    if step == "confirm":
        data = form["data"]
        caption = _receipt(data, "راجع بياناتك قبل التأكيد")
        if edit is not None:        # the previous screen is replaced by the summary
            try:
                await context.bot.delete_message(chat_id, edit.message_id)
            except Exception:
                pass
        if data["photo_kind"] == "photo":
            msg = await context.bot.send_photo(chat_id, data["photo_id"], caption=caption,
                                               parse_mode=ParseMode.HTML, reply_markup=_confirm_kb())
        else:
            msg = await context.bot.send_document(chat_id, data["photo_id"], caption=caption,
                                                  parse_mode=ParseMode.HTML, reply_markup=_confirm_kb())
        form["prompt_id"] = msg.message_id
    else:
        text, kb = _prompt(step, form["data"], context.user_data.get("tg_username"))
        form["prompt_id"] = await _show(context, chat_id, text, kb, edit)


async def go_next(context: ContextTypes.DEFAULT_TYPE, chat_id: int, edit=None) -> None:
    form = _form(context)
    if edit is None:                       # the answer came as a typed message: close the old question's buttons
        await _clear_prompt_buttons(context, chat_id)
    if form.pop("edit_mode", None):        # fixing one answer from the summary: straight back to the summary
        nxt = "confirm"
    else:
        nxt = STEPS[STEPS.index(form["step"]) + 1]
    await ask(context, chat_id, nxt, edit)


def _status_payload(user_id: int):
    apps = sorted((a for a in DATA["applications"].values() if a["user_id"] == user_id),
                  key=lambda a: a["id"], reverse=True)[:5]
    if not apps:
        return "مفيش طلبات متسجلة بإسمك لسه 🤷", []
    blocks = [
        f"🧾 <b>طلب #{a['id']}</b> — {ITEM_EMOJI.get(a['item'], '🧥')} {_esc(a['item'])} / {_esc(a['size'])}"
        f"{(' / ' + PACKS[a['pack']]['emoji'] + ' ' + PACKS[a['pack']]['short']) if a.get('pack') in PACKS else ''}\n"
        f"{_status_line(a)}\n🕒 {_fmt_time(a['created_at'])}"
        for a in apps
    ]
    rows = [[InlineKeyboardButton(f"{RESEND_BTN} #{a['id']}", callback_data=f"rs:{a['id']}")]
            for a in apps if a["status"] == "rejected" and a.get("can_resend")]
    return f"🔎 <b>حالة طلباتك</b>\n{LINE}\n" + "\n\n".join(blocks), rows


def _rejection_message(rec: dict):
    """-> (text, keyboard) the student sees when their application was rejected."""
    text = f"❌ طلبك #{rec['id']} اترفض\nالسبب: {_esc(rec.get('reject_reason') or '-')}"
    if rec.get("can_resend"):
        text += "\n\nمش لازم تعبّي البيانات من الأول — ابعت صورة جديدة بس 👇"
        return text, InlineKeyboardMarkup([[InlineKeyboardButton(RESEND_BTN, callback_data=f"rs:{rec['id']}")]])
    return text + "\nلو فاكر إن في غلط تواصل معانا.", None


# ── Student handlers ──────────────────────────────────────────────────────────
@serialized
async def start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user, chat_id = update.effective_user, update.effective_chat.id
    is_new = str(user.id) not in DATA["users"]       # never pressed /start before (survives restarts via the backup)
    try:
        if touch_user(user):
            await commit()
    except Exception:
        log.exception("Couldn't save the user")   # never block the form because of a save problem
    if is_new:
        await play_onboarding(context, chat_id)
    await send_welcome(context, chat_id)


@serialized
async def cmd_status(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    text, rows = _status_payload(update.effective_user.id)
    await update.message.reply_text(text, parse_mode=ParseMode.HTML,
                                    reply_markup=InlineKeyboardMarkup(rows) if rows else None)


@serialized
async def on_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    q = update.callback_query
    chat_id = q.from_user.id           # private chat: same id as the user
    form = _form(context)
    data = q.data or ""

    # ── screens that work with or without a form in progress ──────────────────
    if data.startswith("rs:"):                                  # "send a new screenshot" after a rejection
        sid = data[3:]
        rec = DATA["applications"].get(sid)
        if not (rec and rec["user_id"] == chat_id and rec["status"] == "rejected" and rec.get("can_resend")):
            await q.answer("مش متاح دلوقتي", show_alert=True)
            return
        await q.answer()
        context.user_data["form"] = _new_form("resend", app_id=rec["id"])
        kb = InlineKeyboardMarkup([[InlineKeyboardButton(BACK_BTN, callback_data=f"rsback:{sid}")]])
        context.user_data["form"]["prompt_id"] = await _show(context, chat_id, Q_RESEND, kb, q.message)
        return
    if data.startswith("rsback:"):
        rec = DATA["applications"].get(data[7:])
        await q.answer()
        context.user_data.pop("form", None)
        if rec and rec["user_id"] == chat_id:
            text, kb = _rejection_message(rec)
            await _show(context, chat_id, text, kb, q.message)
        return
    if data == "status":
        if form and form["step"] not in ("welcome", "status"):
            await q.answer()
            return
        await q.answer()
        text, rows = _status_payload(chat_id)
        kb = InlineKeyboardMarkup([*rows, [InlineKeyboardButton(BACK_BTN, callback_data="home")]])
        context.user_data["form"] = _new_form("status")
        context.user_data["form"]["prompt_id"] = await _show(context, chat_id, text, kb, q.message)
        return
    if data == "home":
        await q.answer()
        if not form or form["step"] in ("welcome", "status"):
            await send_welcome(context, chat_id, q.message)
        return
    if data == "book":
        if not _booking_open():
            await q.answer("الحجز مقفول دلوقتي 🔒", show_alert=True)
            return
        if form and form["step"] != "welcome":
            await q.answer()
            return
        if not form:                    # e.g. an old welcome message after a restart
            context.user_data["form"] = _new_form("welcome")
        await q.answer()
        await ask(context, chat_id, "name", q.message)   # the welcome message turns into the first question
        return

    if not form:
        await q.answer("الجلسة انتهت، ابعت /start من جديد 🙏", show_alert=True)
        return

    if data.startswith("back:"):
        step = data.split(":", 1)[1]
        if form["step"] != step:
            await q.answer("السؤال ده قديم", show_alert=False)
            return
        await q.answer()
        if form.pop("edit_mode", None):          # came from a ✏️ button: back means "back to the summary"
            await ask(context, chat_id, "confirm", q.message)
        elif step == "name":
            await send_welcome(context, chat_id, q.message)
        else:
            await ask(context, chat_id, STEPS[STEPS.index(step) - 1], q.message)
        return

    if data.startswith("pick:"):
        _, step, idx = data.split(":")
        options = {"item": ITEMS, "size": SIZES, "pack": PACK_ORDER}.get(step)
        if form["step"] != step or options is None or not idx.isdigit() or int(idx) >= len(options):
            await q.answer("السؤال ده قديم", show_alert=False)
            return
        choice = options[int(idx)]
        if step == "size" and _is_full(form["data"].get("item"), choice):
            await q.answer("المقاس ده خلص ❌ اختار مقاس تاني", show_alert=True)
            return
        await q.answer()
        form["data"][step] = choice
        await go_next(context, chat_id, q.message)
        return

    if data == "useun":                          # one tap: use the person's own Telegram username
        if form["step"] != "username":
            await q.answer("السؤال ده قديم", show_alert=False)
            return
        value = clean_username(q.from_user.username) if q.from_user.username else None
        if not value:
            await q.answer("اليوزر ده مش مقبول، اكتبه بإيدك 🙏", show_alert=True)
            return
        await q.answer()
        form["data"]["username"] = value
        await go_next(context, chat_id, q.message)
        return

    if data.startswith("edit:"):                 # ✏️ fix ONE answer from the summary
        step = data.split(":", 1)[1]
        if form["step"] != "confirm" or step not in QUESTION_STEPS:
            await q.answer("السؤال ده قديم", show_alert=False)
            return
        await q.answer()
        form["edit_mode"] = True
        await ask(context, chat_id, step, q.message)
        return

    if data == "confirm":
        if form["step"] != "confirm":
            await q.answer()
            return
        if form["data"].get("pack") not in PACKS:        # e.g. a draft saved before packs existed
            await q.answer()
            form["edit_mode"] = True
            await ask(context, chat_id, "pack", q.message)
            return
        try:
            rec = await create_application(q.from_user, form["data"])
        except BookingError as e:
            if e.code == "closed":
                await q.answer("الحجز اتقفل 🔒 بياناتك محفوظة وهنبلغكم لما يفتح.", show_alert=True)
            elif e.code == "full":
                await q.answer("المقاس ده خلص ❌ اختار مقاس تاني", show_alert=True)
                form["edit_mode"] = True
                await ask(context, chat_id, "size", q.message)
            elif e.code == "dup_phone":
                await q.answer(f"الرقم ده عليه طلب مسجل بالفعل (#{e.info}) 🙏 لو محتاج تعدّل كلّم الإدارة.", show_alert=True)
            else:   # dup_photo
                await q.answer("الصورة دي اتبعتت قبل كده 🙏 ابعت صورة التحويل الخاصة بيك.", show_alert=True)
                form["edit_mode"] = True
                await ask(context, chat_id, "photo", q.message)
            return
        except Exception:
            log.exception("Couldn't save the application")
            await q.answer("حصلت مشكلة وإحنا بنسجل بياناتك، جرب تاني كمان شوية 🙏", show_alert=True)
            return
        await q.answer()
        context.user_data.pop("form", None)
        rec["user_msg_id"] = q.message.message_id
        # The confirm button flows into the result: the same message's caption becomes the receipt, no new message.
        caption = _receipt(rec, f"طلب الحجز #{rec['id']}", f"{_status_line(rec)}\n\n{SUBMITTED_TEXT}")
        try:
            await context.bot.edit_message_caption(chat_id=chat_id, message_id=q.message.message_id,
                                                   caption=caption, parse_mode=ParseMode.HTML, reply_markup=None)
        except Exception:
            await context.bot.send_message(chat_id, SUBMITTED_TEXT)
        await notify_admins(context, rec)
        return

    await q.answer()


@serialized
async def on_text(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg = update.message
    chat_id = update.effective_chat.id
    form = _form(context)
    if not form or form["step"] in ("welcome", "done", "status"):
        await send_welcome(context, chat_id)
        return

    step, text = form["step"], msg.text or ""

    if step == "name":
        value = clean_name(text)
        if not value:
            await msg.reply_text("ابعت اسمك الكامل (على الأقل اسمك واسم أبوك) 🙏")
            return
        form["data"]["name"] = value
    elif step == "username":
        value = clean_username(text)
        if not value:
            await msg.reply_text(
                "اليوزر مش مظبوط 🙏\nلازم يبقى حروف إنجليزي وأرقام و _ (من 5 لـ 32 حرف). ابعته تاني."
            )
            return
        form["data"]["username"] = value
    elif step == "phone":
        value = clean_phone(text)
        if not value:
            await msg.reply_text("الرقم مش مظبوط 🙏 ابعته تاني (أرقام بس).")
            return
        if BLOCK_DUPLICATE_PHONE and (dup := _find_dup_phone(value)):
            await msg.reply_text(f"الرقم ده عليه طلب مسجل بالفعل (#{dup['id']}) 🙏\nلو محتاج تعدّل أو تحجز حاجة تانية كلّم الإدارة.")
            return
        form["data"]["phone"] = value
    elif step in ("item", "size"):
        await msg.reply_text("اختار من الأزرار اللي تحت 👇")
        return
    elif step in ("photo", "resend"):
        await msg.reply_text("الصورة بس هي المقبولة هنا 🙏 ابعت صورة/سكرين شوت التحويل.")
        return
    else:  # confirm
        await msg.reply_text("اضغط على أحد الأزرار اللي فوق 👆")
        return

    await go_next(context, chat_id)


async def _edit_text_by_id(context, chat_id: int, message_id: int, text: str, kb=None) -> None:
    try:
        await context.bot.edit_message_text(text, chat_id=chat_id, message_id=message_id,
                                            parse_mode=ParseMode.HTML, reply_markup=kb, link_preview_options=NO_PREVIEW)
    except Exception:
        try:
            await context.bot.send_message(chat_id, text, parse_mode=ParseMode.HTML, reply_markup=kb)
        except Exception:
            pass


async def _handle_resend_photo(context, chat_id: int, form: dict, msg, kind: str, fid: str, uid: str) -> None:
    """A rejected student sends ONLY a new screenshot — the application keeps its number and all other answers."""
    sid = str(form.get("app_id"))
    async with _lock_for(_app_locks, sid):       # an admin may be looking at this application at the same time
        rec = DATA["applications"].get(sid)
        if not (rec and rec["user_id"] == chat_id and rec["status"] == "rejected" and rec.get("can_resend")):
            context.user_data.pop("form", None)
            await msg.reply_text("الطلب ده مش محتاج صورة جديدة دلوقتي.")
            return
        if BLOCK_DUPLICATE_PHOTO and _find_dup_photo(uid):
            await msg.reply_text("الصورة دي اتبعتت قبل كده 🙏 ابعت صورة التحويل الجديدة الخاصة بيك.")
            return
        rec["history"].append({"status": "rejected", "reason": rec.get("reject_reason"),
                               "by": rec.get("decided_by"), "at": rec.get("decided_at")})
        rec.update(photo_kind=kind, photo_id=fid, photo_uid=uid, status="pending", reject_key=None,
                   reject_reason=None, can_resend=False, decided_by=None, decided_at=None,
                   resubmits=rec.get("resubmits", 0) + 1, updated_at=_now_iso())
        try:
            await commit()
        except Exception:
            log.exception("Couldn't save the new screenshot for #%s", sid)
    prompt_id = form.get("prompt_id")
    context.user_data.pop("form", None)
    done = f"✅ وصلتنا الصورة الجديدة لطلب #{rec['id']}\nهنراجعها ونبلغك ❤️‍🔥"
    if prompt_id:
        await _edit_text_by_id(context, chat_id, prompt_id, done)
    else:
        await context.bot.send_message(chat_id, done)
    await _refresh_user_card(context, rec)
    await notify_admins(context, rec, resubmitted=True)


@serialized
async def on_image(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg = update.message
    chat_id = update.effective_chat.id
    form = _form(context)
    if msg.media_group_id and (not form or form["step"] in ("welcome", "done", "status", "confirm")):
        return   # the rest of an album — the first image was already taken
    if not form or form["step"] in ("welcome", "done", "status"):
        await send_welcome(context, chat_id)
        return
    if form["step"] not in ("photo", "resend"):
        await msg.reply_text("الصورة مش مطلوبة دلوقتي، جاوب على السؤال اللي فوق 🙏")
        return

    if msg.photo:
        kind, fid, uid = "photo", msg.photo[-1].file_id, msg.photo[-1].file_unique_id
    else:
        kind, fid, uid = "document", msg.document.file_id, msg.document.file_unique_id
    if form["step"] == "resend":
        await _handle_resend_photo(context, chat_id, form, msg, kind, fid, uid)
        return
    if BLOCK_DUPLICATE_PHOTO and (dup := _find_dup_photo(uid)):
        await msg.reply_text("الصورة دي اتبعتت قبل كده في طلب تاني 🙏\nابعت صورة التحويل الخاصة بيك.")
        return
    form["data"].update(photo_kind=kind, photo_id=fid, photo_uid=uid)
    await go_next(context, chat_id)


@serialized
async def on_other(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Stickers, voice, video, files that aren't images, ..."""
    form = _form(context)
    chat_id = update.effective_chat.id
    if not form or form["step"] in ("welcome", "done", "status"):
        await send_welcome(context, chat_id)
    elif form["step"] in ("photo", "resend"):
        await update.message.reply_text("الصورة بس هي المقبولة هنا 🙏 ابعت صورة/سكرين شوت التحويل.")
    else:
        await update.message.reply_text("جاوب على السؤال اللي فوق 🙏")


# ── Admin side ────────────────────────────────────────────────────────────────
def _is_admin(user) -> bool:
    return user is not None and user.id in ADMIN_IDS


def _admin_caption_ex(rec: dict, title: str, footer: str = "", warn: bool = True, pointer: bool = False):
    """-> (caption, truncated). `truncated` = somebody who used the same screenshot isn't named on the card because a
    photo caption may not exceed 1024 characters — the caller then sends _dup_detail_message as a reply."""
    acct = f" (@{_esc(rec['tg_username'])})" if rec.get("tg_username") else ""
    base = (
        f"{title} #{rec['id']}\n{LINE}\n{_fields_html(rec)}\n{LINE}\n"
        f'🆔 <a href="tg://user?id={rec["user_id"]}">{_esc(rec.get("tg_full_name") or rec["user_id"])}</a>{acct}\n'
        f"🕒 {_fmt_time(rec['created_at'])}"
    )
    total = len(_photo_matches(rec)) if (warn and WARN_DUPLICATE_PHOTO) else 0
    n = min(total, WARN_MAX_PEOPLE)
    while True:                     # name as many people as fit under the limit
        text = base + (_dup_photo_warning(rec, n, pointer) if total else "") + footer
        if len(text) <= 1000 or n <= 0:
            return text, bool(total) and n < total
        n -= 1


def _admin_caption(rec: dict, title: str, footer: str = "", warn: bool = True) -> str:
    return _admin_caption_ex(rec, title, footer, warn)[0]


async def _send_dup_details(bot, chat_id: int, rec: dict, reply_to: int) -> None:
    try:
        await bot.send_message(chat_id, _dup_detail_message(rec), parse_mode=ParseMode.HTML,
                               reply_parameters=ReplyParameters(message_id=reply_to), link_preview_options=NO_PREVIEW)
    except Exception as e:
        log.error("Couldn't send the duplicate-screenshot details to %s for #%s: %s", chat_id, rec["id"], e)


def _decision_footer(rec: dict) -> str:
    if rec["status"] == "pending":
        return ""
    who = _esc((rec.get("decided_by") or {}).get("name", "?"))
    if rec["status"] == "accepted":
        return f"\n\n✅ تم القبول بواسطة {who} — {_fmt_time(rec['decided_at'])}"
    return f"\n\n❌ تم الرفض بواسطة {who} — {_fmt_time(rec['decided_at'])}\nالسبب: {_esc(rec.get('reject_reason') or '-')}"


def _review_kb(rec: dict) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[
        InlineKeyboardButton(ACCEPT_BTN, callback_data=f"adm:acc:{rec['id']}"),
        InlineKeyboardButton(REJECT_BTN, callback_data=f"adm:rej:{rec['id']}"),
    ]])


def _reasons_kb(rec: dict) -> InlineKeyboardMarkup:
    rows = [[InlineKeyboardButton(btn, callback_data=f"adm:rsn:{rec['id']}:{key}")] for key, (btn, _t, _c) in REJECT_REASONS.items()]
    rows.append([InlineKeyboardButton(BACK_BTN, callback_data=f"adm:back:{rec['id']}")])
    return InlineKeyboardMarkup(rows)


async def _send_card(bot, chat_id: int, rec: dict, caption: str, markup):
    if rec["photo_kind"] == "photo":
        return await bot.send_photo(chat_id, rec["photo_id"], caption=caption, parse_mode=ParseMode.HTML, reply_markup=markup)
    return await bot.send_document(chat_id, rec["photo_id"], caption=caption, parse_mode=ParseMode.HTML, reply_markup=markup)


async def notify_admins(context, rec: dict, resubmitted: bool = False) -> None:
    """DMs the application to every admin with [قبول]/[رفض]. Nothing goes to the results group yet."""
    if not ADMIN_IDS:
        log.warning("ADMIN_IDS is empty — application #%s is saved as pending but nobody was notified.", rec["id"])
        return
    title = "🔁 <b>صورة جديدة لطلب</b>" if resubmitted else "📥 <b>طلب حجز جديد</b>"
    if resubmitted:
        rec["admin_msgs"] = {}
    for admin_id in sorted(ADMIN_IDS):
        try:
            text, truncated = _admin_caption_ex(rec, title, pointer=True)
            sent = await _send_card(context.bot, admin_id, rec, text, _review_kb(rec))
            rec["admin_msgs"][str(admin_id)] = sent.message_id
            if truncated:
                await _send_dup_details(context.bot, admin_id, rec, sent.message_id)
        except Exception as e:
            log.error("Couldn't notify admin %s about #%s (has the admin pressed /start?): %s", admin_id, rec["id"], e)
    try:
        await commit()
    except Exception:
        log.exception("Couldn't save admin message ids")


async def _post_to_group(context, rec: dict):
    return await _send_card(context.bot, GROUP_ID, rec, _admin_caption(rec, "✅ <b>حجز مقبول</b>", warn=False), None)


async def _refresh_admin_cards(context, rec: dict) -> None:
    caption = _admin_caption(rec, "📥 <b>طلب حجز</b>", _decision_footer(rec))
    for admin_id, msg_id in (rec.get("admin_msgs") or {}).items():
        try:
            await context.bot.edit_message_caption(chat_id=int(admin_id), message_id=msg_id, caption=caption,
                                                   parse_mode=ParseMode.HTML, reply_markup=None)
        except Exception:
            pass   # message deleted / unchanged — nothing to do


async def _refresh_user_card(context, rec: dict) -> None:
    """The student's own receipt message follows the application: ⏳ -> ✅ / ❌ (edited in place)."""
    if not rec.get("user_msg_id"):
        return
    caption = _receipt(rec, f"طلب الحجز #{rec['id']}", _status_line(rec))
    try:
        await context.bot.edit_message_caption(chat_id=rec["user_id"], message_id=rec["user_msg_id"], caption=caption,
                                               parse_mode=ParseMode.HTML, reply_markup=None)
    except Exception:
        pass


@serialized
async def on_admin_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    q = update.callback_query
    admin = q.from_user
    if not _is_admin(admin):
        await q.answer("مش مسموحلك تعمل كده", show_alert=True)
        return
    parts = (q.data or "").split(":")
    action = parts[1] if len(parts) > 1 else ""
    sid = parts[2] if len(parts) > 2 else ""
    rec = DATA["applications"].get(sid)
    if rec is None:
        await q.answer("الطلب ده مش موجود", show_alert=True)
        return

    async def already_decided():
        await q.answer(f"الطلب ده اتقرر فيه بالفعل ({'مقبول' if rec['status'] == 'accepted' else 'مرفوض'})", show_alert=True)
        await _refresh_admin_cards(context, rec)

    if action in ("rej", "back"):                     # only swaps the buttons on this admin's card
        if rec["status"] != "pending":
            await already_decided()
            return
        await q.answer()
        kb = _reasons_kb(rec) if action == "rej" else _review_kb(rec)
        try:
            await context.bot.edit_message_reply_markup(chat_id=admin.id, message_id=q.message.message_id, reply_markup=kb)
        except Exception:
            pass
        return

    if action not in ("acc", "rsn"):
        await q.answer()
        return
    async with _lock_for(_app_locks, sid):            # two admins tapping together: the second one finds it decided
        if rec["status"] != "pending":
            await already_decided()
            return
        if action == "acc":
            try:
                posted = await _post_to_group(context, rec)   # only an ACCEPTED application reaches the first group
            except Exception:
                log.exception("Couldn't post accepted application #%s to the results group", sid)
                await q.answer("معرفتش أبعت للجروب — اتأكد إن البوت فيه وجرب تاني", show_alert=True)
                return   # still pending: nothing was decided
            rec.update(group_msg_id=posted.message_id, status="accepted", reject_key=None, reject_reason=None, can_resend=False)
        else:
            key = parts[3] if len(parts) > 3 else ""
            if key not in REJECT_REASONS:
                await q.answer()
                return
            _btn, reason_text, can_resend = REJECT_REASONS[key]
            rec.update(status="rejected", reject_key=key, reject_reason=reason_text, can_resend=can_resend)
        now = _now_iso()
        rec["decided_by"] = {"id": admin.id, "name": admin.full_name}
        rec["decided_at"] = rec["updated_at"] = now
        try:
            await commit()
        except Exception:
            log.exception("Couldn't save the decision on #%s", sid)
    await q.answer("تم ✅")
    await _refresh_admin_cards(context, rec)
    await _refresh_user_card(context, rec)
    try:
        if rec["status"] == "accepted":
            await context.bot.send_message(rec["user_id"], ACCEPTED_TEXT)
        else:
            text, kb = _rejection_message(rec)
            await context.bot.send_message(rec["user_id"], text, parse_mode=ParseMode.HTML, reply_markup=kb)
    except Exception:
        pass   # the applicant blocked the bot — the decision still stands


# ── Admin commands (only ADMIN_IDS) ───────────────────────────────────────────
def admin_only(fn):
    @functools.wraps(fn)
    async def wrapper(update, context):
        if not _is_admin(update.effective_user):
            return
        return await fn(update, context)
    return serialized(wrapper)


@admin_only
async def cmd_pending(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    pending = sorted((r for r in DATA["applications"].values() if r["status"] == "pending"), key=lambda r: r["id"])
    if not pending:
        await update.message.reply_text("مفيش طلبات معلقة ✅")
        return
    admin_id = update.effective_user.id
    for rec in pending[:20]:
        try:
            text, truncated = _admin_caption_ex(rec, "📥 <b>طلب حجز معلق</b>", pointer=True)
            sent = await _send_card(context.bot, admin_id, rec, text, _review_kb(rec))
            rec["admin_msgs"][str(admin_id)] = sent.message_id
            if truncated:
                await _send_dup_details(context.bot, admin_id, rec, sent.message_id)
        except Exception as e:
            log.error("Couldn't re-send #%s: %s", rec["id"], e)
    if len(pending) > 20:
        await update.message.reply_text(f"فيه {len(pending) - 20} طلب كمان — خلّص دول وابعت /pending تاني.")
    await commit()


def _counts() -> dict:
    out = {"pending": 0, "accepted": 0, "rejected": 0}
    for a in DATA["applications"].values():
        out[a["status"]] += 1
    return out


@admin_only
async def cmd_stats(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    c = _counts()
    await update.message.reply_text(
        f"👥 المستخدمين: {len(DATA['users'])}\n"
        f"📋 الطلبات: {len(DATA['applications'])} — معلق {c['pending']} · مقبول {c['accepted']} · مرفوض {c['rejected']}\n"
        f"✍️ استمارات لسه بتتملي: {len(DATA['drafts'])}\n"
        f"🗄 آخر نسخة احتياطية: {_fmt_time(_last_backup_ok_iso) if _last_backup_ok_iso else 'لسه'}"
        f"{'' if RESTORE_OK else chr(10) + '⚠️ النسخ الاحتياطي واقف — الاستعادة فشلت (/restore)'}"
    )


@admin_only
async def cmd_summary(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    c = _counts()
    lines = [
        "📊 <b>ملخص الطلبات</b>", LINE,
        f"👥 المستخدمين: {len(DATA['users'])}",
        f"📋 الطلبات: {len(DATA['applications'])} — ⏳ {c['pending']} · ✅ {c['accepted']} · ❌ {c['rejected']}",
        f"🚪 الحجز: {'مفتوح 🔓' if _booking_open() else 'مقفول 🔒'}",
    ]
    for item in ITEMS:
        total = 0
        rows = []
        for size in SIZES:
            acc = sum(1 for a in DATA["applications"].values() if a["status"] == "accepted" and a["item"] == item and a["size"] == size)
            pen = sum(1 for a in DATA["applications"].values() if a["status"] == "pending" and a["item"] == item and a["size"] == size)
            lim = _limit_for(item, size)
            total += acc + pen
            rows.append(f"   {size}: {acc + pen}{f'/{lim}' if lim is not None else ''}  (✅ {acc} · ⏳ {pen})")
        lines += ["", f"{ITEM_EMOJI[item]} <b>{item}</b> — {total}", *rows]
    live = [a for a in DATA["applications"].values() if a["status"] in ("pending", "accepted")]
    pack_rows, money = [], 0
    for key in PACK_ORDER:
        cnt = sum(1 for a in live if a.get("pack") == key)
        money += cnt * PACKS[key]["price"]
        pack_rows.append(f"   {PACKS[key]['emoji']} {PACKS[key]['short']}: {cnt}  ({cnt * PACKS[key]['price']}ج)")
    lines += ["", "🎁 <b>الباكات</b> (معلق + مقبول)", *pack_rows, f"   💰 إجمالي الباكات: {money}ج"]
    await update.message.reply_text("\n".join(lines), parse_mode=ParseMode.HTML)


_STATUS_AR = {"pending": "قيد المراجعة", "accepted": "مقبول", "rejected": "مرفوض"}
_CSV_HEAD = ["رقم الطلب", "الحالة", "تاريخ الطلب", "الاسم", "اليوزر", "رقم التليفون", "الطلب", "المقاس", "الباك", "سعر الباك",
             "ID التليجرام", "يوزر الحساب", "اتقرر بواسطة", "تاريخ القرار", "سبب الرفض", "مرات إعادة الإرسال"]


def _csv_safe(value) -> str:
    """Names are typed by students: stop a cell that starts with = + - @ from being run as a formula in Excel."""
    s = "" if value is None else str(value)
    return "'" + s if s[:1] in ("=", "+", "-", "@", "\t", "\r") else s


def _build_csv(statuses) -> bytes:
    sio = StringIO()
    w = csv.writer(sio)
    w.writerow(_CSV_HEAD)
    for a in sorted(DATA["applications"].values(), key=lambda r: r["id"]):
        if a["status"] not in statuses:
            continue
        phone = a.get("phone") or ""
        w.writerow([
            a["id"], _STATUS_AR[a["status"]], _fmt_time(a["created_at"]), _csv_safe(a["name"]), _csv_safe(a["username"]),
            f'="{phone}"' if re.fullmatch(r"\+?\d+", phone) else _csv_safe(phone),   # keeps the leading 0 in Excel
            a["item"], a["size"], PACKS.get(a.get("pack"), {}).get("name", ""), PACKS.get(a.get("pack"), {}).get("price", ""),
            a["user_id"], _csv_safe(a.get("tg_username")),
            _csv_safe((a.get("decided_by") or {}).get("name")), _fmt_time(a["decided_at"]) if a.get("decided_at") else "",
            _csv_safe(a.get("reject_reason")), a.get("resubmits", 0),
        ])
    return ("\ufeff" + sio.getvalue()).encode("utf-8")      # BOM: Excel shows the Arabic correctly


@admin_only
async def cmd_export(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    arg = (context.args[0].lower() if context.args else "all")
    pick = {"all": APP_STATUSES, "pending": ("pending",), "accepted": ("accepted",), "rejected": ("rejected",)}
    if arg not in pick:
        await update.message.reply_text("استخدم: /export  أو  /export accepted  أو  pending  أو  rejected")
        return
    raw = _build_csv(pick[arg])
    n = sum(1 for a in DATA["applications"].values() if a["status"] in pick[arg])
    fname = f"semi_senior_{arg}_{datetime.now(TZ).strftime('%Y%m%d_%H%M')}.csv"
    await update.message.reply_document(InputFile(BytesIO(raw), filename=fname), caption=f"📄 {n} طلب")


@admin_only
async def cmd_close(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    _set_setting("open", False)
    await commit()
    await update.message.reply_text("🔒 الحجز اتقفل. اللي في نص الاستمارة بياناته محفوظة وهيكمل لما يفتح.")


@admin_only
async def cmd_open(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    _set_setting("open", True)
    await commit()
    await update.message.reply_text("🔓 الحجز اتفتح.")


_ITEM_ALIASES = {"hoodie": "هودي", "baseball": "بيسبول", "jacket": "بيسبول"}


def _limits_text() -> str:
    lim = DATA["settings"].get("limits") or {}
    if not lim:
        return "مفيش حدود متظبطة."
    rows = []
    for key in sorted(lim):
        item, size = key.split("|")
        rows.append(f"{ITEM_EMOJI.get(item, '')} {item} {size}: {_taken(item, size)}/{lim[key]}")
    return "\n".join(rows)


@admin_only
async def cmd_limit(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    args = context.args or []
    if not args:
        await update.message.reply_text(
            f"📦 الحدود الحالية (محجوز/الحد):\n{_limits_text()}\n\n"
            "لتحديد حد: /limit هودي L 30\nلإلغاء الحد: /limit هودي L off")
        return
    if len(args) != 3:
        await update.message.reply_text("الصيغة: /limit هودي L 30   أو   /limit هودي L off")
        return
    item = _ITEM_ALIASES.get(args[0].lower(), args[0])
    size = args[1].upper()
    if item not in ITEMS or size not in SIZES:
        await update.message.reply_text(f"الطلب لازم يكون {' أو '.join(ITEMS)} والمقاس {' / '.join(SIZES)}.")
        return
    limits = dict(DATA["settings"].get("limits") or {})
    if args[2].lower() in ("off", "none", "0x", "-"):
        limits.pop(f"{item}|{size}", None)
        msg = f"✅ اتلغى حد {item} {size}."
    elif args[2].isdigit():
        limits[f"{item}|{size}"] = int(args[2])
        msg = f"✅ حد {item} {size} = {int(args[2])} (محجوز دلوقتي {_taken(item, size)})."
    else:
        await update.message.reply_text("الرقم لازم يكون عدد صحيح أو off.")
        return
    _set_setting("limits", limits)
    await commit()
    await update.message.reply_text(msg)


def _rss_mb():
    try:
        with open("/proc/self/status", encoding="utf-8") as f:
            for line in f:
                if line.startswith("VmRSS:"):
                    return int(line.split()[1]) / 1024
    except Exception:
        pass
    return None


@admin_only
async def cmd_health(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    up = int(time.time() - _STARTED_AT)
    c = _counts()
    rss = _rss_mb()
    await update.message.reply_text(
        "🩺 <b>حالة البوت</b>\n" + LINE + "\n"
        f"⏱ شغال من: {up // 86400}ي {(up % 86400) // 3600}س {(up % 3600) // 60}د\n"
        f"🧠 الذاكرة: {f'{rss:.0f} MB' if rss else '—'}\n"
        f"👥 {len(DATA['users'])} مستخدم · 📋 {len(DATA['applications'])} طلب (⏳ {c['pending']}) · ✍️ {len(DATA['drafts'])} استمارة مفتوحة\n"
        f"🚪 الحجز: {'مفتوح 🔓' if _booking_open() else 'مقفول 🔒'}\n"
        f"🗄 آخر نسخة: {_fmt_time(_last_backup_ok_iso) if _last_backup_ok_iso else 'لسه'}"
        f" · {'في انتظار رفع' if _backup_pending else 'محدّثة'} · فشل ورا بعض: {_backup_fail_streak}\n"
        f"{'✅' if RESTORE_OK else '⚠️'} الاستعادة: {'تمام' if RESTORE_OK else 'فشلت — النسخ واقف (/restore)'}",
        parse_mode=ParseMode.HTML,
    )


@admin_only
async def cmd_backup(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not RESTORE_OK:
        await update.message.reply_text("⚠️ النسخ الاحتياطي واقف لأن آخر استعادة فشلت. جرب /restore الأول.")
        return
    await save_data()
    ok = await backup_to_storage(context, force=True, repair=True)
    await update.message.reply_text("تم رفع نسخة احتياطية ✅" if ok else "❌ فشل رفع النسخة — شوف الـ logs.")


@admin_only
async def cmd_restore(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    result = await restore_from_storage(context.bot)
    texts = {
        "restored": f"تمت الاستعادة ✅ ({len(DATA['users'])} مستخدم · {len(DATA['applications'])} طلب)",
        "no_backup": "مفيش نسخة احتياطية متثبتة في جروب التخزين.",
        "not_configured": "STORAGE_GROUP_ID مش متظبط.",
    }
    await update.message.reply_text(texts.get(result, f"❌ {result}"))


@admin_only
async def cmd_setwelcome(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    replied = update.message.reply_to_message
    if not (replied and replied.photo):
        await update.message.reply_text("ابعت الصورة الأول، وبعدين اعمل ريبلاي عليها بـ /setwelcome")
        return
    _set_setting("welcome_photo_id", replied.photo[-1].file_id)
    await commit()
    await update.message.reply_text("✅ الصورة دي هتظهر قبل رسالة الترحيب.")


@admin_only
async def cmd_clearwelcome(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    _set_setting("welcome_photo_id", None)
    await commit()
    await update.message.reply_text("✅ اتشالت صورة الترحيب.")


# ── Background work ───────────────────────────────────────────────────────────
async def housekeeping(ctx) -> None:
    """Every ~10 minutes: drop abandoned forms, remind the admins about applications nobody has decided on."""
    cutoff = (datetime.now(timezone.utc) - timedelta(days=DRAFT_TTL_DAYS)).isoformat(timespec="seconds")
    stale = [k for k, d in DATA["drafts"].items() if (d.get("updated_at") or "") < cutoff]
    for k in stale:
        DATA["drafts"].pop(k, None)
    if stale:
        mark_dirty()
        request_backup(urgent=False)
    limit = datetime.now(timezone.utc) - timedelta(hours=REMINDER_AFTER_HOURS)
    old = sorted((a for a in DATA["applications"].values()
                  if a["status"] == "pending" and (a.get("updated_at") or a["created_at"]) <= limit.isoformat(timespec="seconds")),
                 key=lambda a: a["id"])
    if old:
        lines = [f"#{a['id']} — {_esc(a['name'])} ({_fmt_time(a['created_at'])})" for a in old[:15]]
        more = f"\n… و{len(old) - 15} كمان" if len(old) > 15 else ""
        await alert_admins(ctx.bot, "pending_reminder",
                           f"⏰ {len(old)} طلب لسه معلق من أكتر من {REMINDER_AFTER_HOURS:g} ساعة:\n" + "\n".join(lines) + more
                           + "\n\nابعت /pending عشان تراجعهم.", every=REMINDER_AFTER_HOURS * 3600)


async def _maintenance_loop(app) -> None:
    ctx = SimpleNamespace(bot=app.bot)
    now = time.monotonic()
    last_reconcile = now - RECONCILE_INTERVAL + 60      # first check ~1 minute after boot
    last_housekeeping = now
    last_flush = now - 2                                 # the first flush needn't wait
    while True:
        try:
            try:
                await asyncio.wait_for(_backup_wakeup.wait(), timeout=2)
            except asyncio.TimeoutError:
                pass
            _backup_wakeup.clear()
            now = time.monotonic()
            if _dirty and now - last_flush >= 2:          # half-finished forms are written in batches
                last_flush = now
                await save_data()
            if _backup_pending:
                interval = BACKUP_MIN_INTERVAL if _backup_urgent else DRAFT_BACKUP_MIN_INTERVAL
                if now - _last_backup_at >= interval:
                    await backup_to_storage(ctx)
            if now - last_reconcile >= RECONCILE_INTERVAL:
                last_reconcile = now
                await reconcile_backup(ctx)
            if now - last_housekeeping >= 600:
                last_housekeeping = now
                await housekeeping(ctx)
        except asyncio.CancelledError:
            raise
        except Exception:
            log.exception("Maintenance loop error")
            await asyncio.sleep(5)


async def on_error(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    log.error("Unhandled error", exc_info=context.error)


STUDENT_COMMANDS = [BotCommand("start", "ابدأ الحجز"), BotCommand("status", "حالة طلبي")]
ADMIN_COMMANDS = STUDENT_COMMANDS + [
    BotCommand("pending", "الطلبات المعلقة"), BotCommand("summary", "ملخص الطلبات والمقاسات"),
    BotCommand("stats", "أرقام سريعة"), BotCommand("export", "تصدير الطلبات CSV"),
    BotCommand("open", "فتح الحجز"), BotCommand("close", "قفل الحجز"), BotCommand("limit", "حد المقاسات"),
    BotCommand("health", "حالة البوت"), BotCommand("backup", "نسخة احتياطية الآن"), BotCommand("restore", "استعادة"),
    BotCommand("setwelcome", "صورة الترحيب (ريبلاي على صورة)"), BotCommand("clearwelcome", "شيل صورة الترحيب"),
]


async def post_init(app: Application) -> None:
    result = await restore_from_storage(app.bot)
    log.info("Startup restore: %s", result)
    if result.startswith("failed"):
        for admin_id in ADMIN_IDS:
            try:
                await app.bot.send_message(
                    admin_id, f"⚠️ الاستعادة من جروب التخزين فشلت:\n{result}\nالنسخ الاحتياطي واقف لحد ما /restore تنجح.")
            except Exception:
                pass
    if not ADMIN_IDS:
        log.warning("ADMIN_IDS is empty: applications will be saved as pending but no admin can accept them.")
    try:      # the "/" menu: students see two commands, each admin sees all of theirs
        await app.bot.set_my_commands(STUDENT_COMMANDS, scope=BotCommandScopeAllPrivateChats())
        for admin_id in ADMIN_IDS:
            await app.bot.set_my_commands(ADMIN_COMMANDS, scope=BotCommandScopeChat(admin_id))
    except Exception as e:
        log.warning("Couldn't set the command menu: %s", e)
    request_backup(urgent=False)   # the first loop pass uploads only if something differs from the restored backup
    app.bot_data["maintenance_task"] = asyncio.create_task(_maintenance_loop(app))


async def post_stop(app: Application) -> None:
    """Last save + backup on shutdown, so a redeploy doesn't lose the changes since the last upload."""
    task = app.bot_data.get("maintenance_task")
    if task:
        task.cancel()
    try:
        async def _final():
            await save_data()
            await backup_to_storage(SimpleNamespace(bot=app.bot), force=True)
        await asyncio.wait_for(_final(), timeout=FINAL_BACKUP_TIMEOUT)
    except Exception as e:
        log.error("Final backup on stop incomplete: %r", e)


def main() -> None:
    if not BOT_TOKEN:
        raise SystemExit("Set the BOT_TOKEN environment variable.")
    builder = (Application.builder().token(BOT_TOKEN).post_init(post_init).post_stop(post_stop)
               .concurrent_updates(MAX_CONCURRENT_UPDATES))      # many students at once
    try:      # waits/retries when Telegram's flood limits are hit instead of dropping messages
        from telegram.ext import AIORateLimiter
        builder = builder.rate_limiter(AIORateLimiter(overall_max_rate=25, max_retries=3))
    except Exception as e:
        log.warning("Rate limiter not active (%s) — install python-telegram-bot[rate-limiter].", e)
    app = builder.build()
    private = filters.ChatType.PRIVATE
    for name, fn in (("start", start), ("status", cmd_status), ("pending", cmd_pending), ("summary", cmd_summary),
                     ("stats", cmd_stats), ("export", cmd_export), ("open", cmd_open), ("close", cmd_close),
                     ("limit", cmd_limit), ("health", cmd_health), ("backup", cmd_backup), ("restore", cmd_restore),
                     ("setwelcome", cmd_setwelcome), ("clearwelcome", cmd_clearwelcome)):
        app.add_handler(CommandHandler(name, fn, filters=private))
    app.add_handler(CallbackQueryHandler(on_admin_callback, pattern=r"^adm:"))
    app.add_handler(CallbackQueryHandler(on_callback))
    app.add_handler(MessageHandler(private & (filters.PHOTO | filters.Document.IMAGE), on_image))
    app.add_handler(MessageHandler(private & filters.TEXT & ~filters.COMMAND, on_text))
    app.add_handler(MessageHandler(
        private & ~filters.TEXT & ~filters.COMMAND & ~filters.PHOTO & ~filters.Document.IMAGE, on_other))
    app.add_error_handler(on_error)
    app.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()
