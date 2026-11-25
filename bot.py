"""
Semi Senior booking bot (Arabic).

Flow:  /start -> welcome + [أحجز معانا ❤️‍🔥]
       -> name -> Telegram username -> phone -> هودي / بيسبول -> size (S/M/L/XL, with size-guide link)
       -> payment screenshot (images only)
       -> the user gets everything back with [أضغط لتأكيد البيانات] / [الرجوع]
       -> on confirm the application is SAVED as "pending" and sent to the admins (private chat) with
          [قبول] / [رفض]. ONLY an accepted application is posted to the results group.
Every step has an [الرجوع] button.

Saving (same idea as the Quizician bot): every user and every application is kept in a local JSON file
AND mirrored into a pinned, zipped backup document in the storage group. On startup the bot restores from
that pinned backup (so a redeploy / wiped disk loses nothing), backups are throttled + skipped when
nothing changed + retried by a background loop, and one last backup runs when the bot stops.

Railway variables:
    BOT_TOKEN          (required)  token from @BotFather
    ADMIN_IDS          (optional)  Telegram user ids of the admins, comma-separated. Default: 5242845517,940770584
                                   — only these two can use the admin commands and accept/reject applications
                                   (each admin must press /start in the bot once so it can message them)
    GROUP_ID           (optional)  results group for ACCEPTED applications, default -1005980424677
    STORAGE_GROUP_ID   (optional)  backup group, default -1005738619227 — the bot must be an ADMIN there
                                   (it needs to send documents and pin messages)
    DATA_DIR           (optional)  folder for the local JSON files (default: current folder; point it at a
                                   Railway volume if you have one — without one the storage group is the
                                   durable copy)
    BACKUP_MIN_INTERVAL (optional) seconds between backup uploads, default 60
    FINAL_BACKUP_TIMEOUT (optional) seconds the last backup on shutdown may take, default 8

Admin commands (private chat): /pending  /stats  /backup  /restore

requirements.txt:  python-telegram-bot>=21.0,<22
"""

import asyncio
import hashlib
import html
import json
import logging
import os
import re
import time
import zipfile
from datetime import datetime, timezone
from io import BytesIO
from types import SimpleNamespace
from zoneinfo import ZoneInfo

from telegram import InlineKeyboardButton, InlineKeyboardMarkup, InputFile, LinkPreviewOptions, Update
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
FINAL_BACKUP_TIMEOUT = int(os.environ.get("FINAL_BACKUP_TIMEOUT", "8"))
RECONCILE_INTERVAL = 6 * 3600                        # re-check that the pinned backup is still there
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
WELCOME_TEXT = (
    "أهلاً بيك في <b>Semi Senior</b> ❤️‍🔥\n\n"
    "اضغط على الزرار اللي تحت عشان تحجز معانا، وهنسألك كام سؤال سريع."
)
BOOK_BTN = "أحجز معانا ❤️‍🔥"
BACK_BTN = "الرجوع"
CONFIRM_BTN = "أضغط لتأكيد البيانات"

Q_NAME = "أي هو أسمك الكامل"
Q_USERNAME = "أي هو اليوزر بتاعك على التليجرام"
Q_PHONE = "أي هو رقم تليفون"
Q_ITEM = "نفسك فأي؟!"
Q_SIZE = "أي هو مقاسك؟"
SIZE_NOTE = f'تقدر تعرف دليل المقاسات من <b><a href="{SIZE_GUIDE_URL}">اللينك ده</a></b>'
Q_PHOTO = "أبعت صورة/سكرين شوت بتمام إرسال المبلغ المطلوب"

SUBMITTED_TEXT = "تم استلام طلبك ✅\nهيتم مراجعته من الإدارة وهنبلغك بالنتيجة ❤️‍🔥"
ACCEPTED_TEXT = "تم قبول حجزك ✅\nشكراً ليك ❤️‍🔥"
REJECTED_TEXT = "للأسف طلب الحجز اترفض ❌\nلو فاكر إن في غلط تواصل معانا."
ACCEPT_BTN = "✅ قبول"
REJECT_BTN = "❌ رفض"

ITEMS = ["هودي", "بيسبول"]
SIZES = ["S", "M", "L", "XL"]

STEPS = ["name", "username", "phone", "item", "size", "photo", "confirm"]
NO_PREVIEW = LinkPreviewOptions(is_disabled=True)

_DIGITS = str.maketrans("٠١٢٣٤٥٦٧٨٩۰۱۲۳۴۵۶۷۸۹", "01234567890123456789")


# ── Small helpers ─────────────────────────────────────────────────────────────
def _esc(value) -> str:
    return html.escape(str(value), quote=False)


def _back_row(step: str):
    return [InlineKeyboardButton(BACK_BTN, callback_data=f"back:{step}")]


def _kb_back(step: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([_back_row(step)])


def _kb_choices(step: str, options: list) -> InlineKeyboardMarkup:
    row = [InlineKeyboardButton(o, callback_data=f"pick:{step}:{i}") for i, o in enumerate(options)]
    return InlineKeyboardMarkup([row, _back_row(step)])


def _fields_html(data: dict) -> str:
    return (
        f"👤 الاسم: {_esc(data['name'])}\n"
        f"✈️ اليوزر: {_esc(data['username'])}\n"
        f"📱 رقم التليفون: {_esc(data['phone'])}\n"
        f"🧥 الطلب: {_esc(data['item'])}\n"
        f"📏 المقاس: {_esc(data['size'])}"
    )


def _prompt(step: str):
    """-> (text, keyboard) for a question step."""
    if step == "name":
        return Q_NAME, _kb_back(step)
    if step == "username":
        return Q_USERNAME, _kb_back(step)
    if step == "phone":
        return Q_PHONE, _kb_back(step)
    if step == "item":
        return Q_ITEM, _kb_choices(step, ITEMS)
    if step == "size":
        return f"{Q_SIZE}\n\n{SIZE_NOTE}", _kb_choices(step, SIZES)
    if step == "photo":
        return Q_PHOTO, _kb_back(step)
    raise ValueError(step)


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


# ── Data (users + applications) ───────────────────────────────────────────────
# DATA = {"users": {"<tg id>": {...}}, "applications": {"<app id>": {...}}, "next_app_id": int}
# Every record carries "updated_at" (UTC ISO) — it decides which copy wins when a backup is merged in.
APP_STATUSES = ("pending", "accepted", "rejected")


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _fmt_time(iso: str) -> str:
    try:
        return datetime.fromisoformat(iso).astimezone(TZ).strftime("%d/%m/%Y %H:%M")
    except Exception:
        return iso or "-"


def _valid_data(d) -> bool:
    return (
        isinstance(d, dict)
        and isinstance(d.get("users"), dict)
        and isinstance(d.get("applications"), dict)
        and isinstance(d.get("next_app_id"), int)
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
    return {"users": {}, "applications": {}, "next_app_id": 1}


DATA: dict = _load_json_file(DATA_FILE, None)
if not _valid_data(DATA):
    if DATA is not None:
        log.error("%s has the wrong structure — ignoring it.", DATA_FILE)
    DATA = _empty_data()
BACKUP_STATE: dict = _load_json_file(BACKUP_STATE_FILE, {})
if not isinstance(BACKUP_STATE, dict):
    BACKUP_STATE = {}

_save_lock = asyncio.Lock()


def _atomic_write(path: str, text: str) -> None:
    os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
    tmp = f"{path}.tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(text)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)   # a crash mid-write can never leave a half-written data file


async def save_data() -> None:
    text = json.dumps(DATA, ensure_ascii=False)   # snapshot taken on the event loop, written off it
    async with _save_lock:
        await asyncio.to_thread(_atomic_write, DATA_FILE, text)


async def save_backup_state() -> None:
    text = json.dumps(BACKUP_STATE, ensure_ascii=False)
    async with _save_lock:
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
    """Save locally, then ask for a backup (throttled — see backup_to_storage)."""
    await save_data()
    request_backup()


async def create_application(user, form_data: dict) -> dict:
    """Adds a pending application and saves it. If saving fails nothing is left half-added."""
    app_id = DATA["next_app_id"]
    now = _now_iso()
    rec = {
        "id": app_id, "user_id": user.id, "tg_username": user.username, "tg_full_name": user.full_name,
        **{k: form_data[k] for k in ("name", "username", "phone", "item", "size", "photo_kind", "photo_id")},
        "status": "pending", "created_at": now, "updated_at": now,
        "decided_by": None, "decided_at": None, "admin_msgs": {}, "group_msg_id": None,
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
_data_gen = 0                # bumped on every request_backup(); lets a finished upload tell if more changed meanwhile
_last_backup_at = -1e9       # monotonic time of the last upload attempt (throttle)
_last_backup_ok_iso = None
_last_hash = None
_backup_wakeup = asyncio.Event()


def request_backup() -> None:
    global _backup_pending, _data_gen
    _backup_pending = True
    _data_gen += 1
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


async def backup_to_storage(context, force: bool = False, repair: bool = False) -> bool:
    """Uploads + pins the backup. force = skip the throttle; repair = also skip the "unchanged" check.
    Returns True when the backup is up to date (uploaded now, or identical to the last upload)."""
    global _backup_pending, _last_backup_at, _last_hash, _last_backup_ok_iso
    if not STORAGE_GROUP_ID:
        return False
    if not RESTORE_OK:
        log.error("BACKUP SKIPPED — the last restore failed, refusing to overwrite the storage-group backup. "
                  "Fix the problem and run /restore.")
        return False
    now = time.monotonic()
    if not force and now - _last_backup_at < BACKUP_MIN_INTERVAL:
        _backup_pending = True          # the background loop sends it once the interval has passed
        return False
    _last_backup_at = now
    gen = _data_gen
    raw = _build_backup_zip()
    digest = hashlib.sha1(raw).hexdigest()
    if not repair and digest == _last_hash:
        _backup_pending = _data_gen != gen
        return True
    try:
        sent = await context.bot.send_document(
            chat_id=STORAGE_GROUP_ID,
            document=InputFile(BytesIO(raw), filename=_backup_filename()),
            caption=BACKUP_MARKER,
        )
    except Exception as e:
        log.error("BACKUP UPLOAD FAILED: %s", e)
        _backup_pending = True          # retried by the background loop
        return False
    _last_hash = digest
    _last_backup_ok_iso = _now_iso()
    _backup_pending = _data_gen != gen   # changed while uploading -> another round is needed
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
            log.info("Restored backup: %d user(s), %d application(s).", len(DATA["users"]), len(DATA["applications"]))
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


async def _backup_loop(app) -> None:
    ctx = SimpleNamespace(bot=app.bot)
    last_reconcile = time.monotonic() - RECONCILE_INTERVAL + 60      # first check ~1 minute after boot
    while True:
        try:
            try:
                await asyncio.wait_for(_backup_wakeup.wait(), timeout=15)
            except asyncio.TimeoutError:
                pass
            _backup_wakeup.clear()
            if _backup_pending and time.monotonic() - _last_backup_at >= BACKUP_MIN_INTERVAL:
                await backup_to_storage(ctx)
            if time.monotonic() - last_reconcile >= RECONCILE_INTERVAL:
                last_reconcile = time.monotonic()
                await reconcile_backup(ctx)
        except asyncio.CancelledError:
            raise
        except Exception:
            log.exception("Backup loop error")
            await asyncio.sleep(5)


# ── Flow helpers ──────────────────────────────────────────────────────────────
def _form(context: ContextTypes.DEFAULT_TYPE):
    return context.user_data.get("form")


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


async def send_welcome(context: ContextTypes.DEFAULT_TYPE, chat_id: int, edit=None) -> None:
    context.user_data["form"] = {"step": "welcome", "data": {}, "prompt_id": None, "sending": False}
    kb = InlineKeyboardMarkup([[InlineKeyboardButton(BOOK_BTN, callback_data="book")]])
    context.user_data["form"]["prompt_id"] = await _show(context, chat_id, WELCOME_TEXT, kb, edit)


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


async def ask(context: ContextTypes.DEFAULT_TYPE, chat_id: int, step: str, edit=None) -> None:
    form = _form(context)
    form["step"] = step
    if step == "confirm":
        data = form["data"]
        caption = f"<b>راجع بياناتك قبل التأكيد 👇</b>\n\n{_fields_html(data)}"
        kb = InlineKeyboardMarkup([
            [InlineKeyboardButton(CONFIRM_BTN, callback_data="confirm")],
            _back_row("confirm"),
        ])
        if data["photo_kind"] == "photo":
            msg = await context.bot.send_photo(chat_id, data["photo_id"], caption=caption,
                                               parse_mode=ParseMode.HTML, reply_markup=kb)
        else:
            msg = await context.bot.send_document(chat_id, data["photo_id"], caption=caption,
                                                  parse_mode=ParseMode.HTML, reply_markup=kb)
        form["prompt_id"] = msg.message_id
    else:
        text, kb = _prompt(step)
        form["prompt_id"] = await _show(context, chat_id, text, kb, edit)


async def go_next(context: ContextTypes.DEFAULT_TYPE, chat_id: int, edit=None) -> None:
    if edit is None:                       # the answer came as a typed message: close the old question's buttons
        await _clear_prompt_buttons(context, chat_id)
    step = _form(context)["step"]
    await ask(context, chat_id, STEPS[STEPS.index(step) + 1], edit)


# ── Handlers ──────────────────────────────────────────────────────────────────
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


async def on_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    q = update.callback_query
    chat_id = q.from_user.id           # private chat: same id as the user
    form = _form(context)
    data = q.data or ""

    if not form:
        await q.answer("الجلسة انتهت، ابعت /start من جديد 🙏", show_alert=True)
        return

    if data == "book":
        if form["step"] != "welcome":
            await q.answer()
            return
        await q.answer()
        await ask(context, chat_id, "name", q.message)   # the welcome message turns into the first question
        return

    if data.startswith("back:"):
        step = data.split(":", 1)[1]
        if form["step"] != step:
            await q.answer("السؤال ده قديم", show_alert=False)
            return
        await q.answer()
        if step == "name":
            await send_welcome(context, chat_id, q.message)
        else:
            await ask(context, chat_id, STEPS[STEPS.index(step) - 1], q.message)
        return

    if data.startswith("pick:"):
        _, step, idx = data.split(":")
        options = {"item": ITEMS, "size": SIZES}.get(step)
        if form["step"] != step or options is None or not idx.isdigit() or int(idx) >= len(options):
            await q.answer("السؤال ده قديم", show_alert=False)
            return
        await q.answer()
        form["data"][step] = options[int(idx)]
        await go_next(context, chat_id, q.message)
        return

    if data == "confirm":
        if form["step"] != "confirm" or form.get("sending"):
            await q.answer()
            return
        form["sending"] = True
        try:
            rec = await create_application(q.from_user, form["data"])
        except Exception:
            log.exception("Couldn't save the application")
            form["sending"] = False
            await q.answer("حصلت مشكلة وإحنا بنسجل بياناتك، جرب تاني كمان شوية 🙏", show_alert=True)
            return
        await q.answer()
        context.user_data["form"] = {"step": "done", "data": {}, "prompt_id": None, "sending": False}
        # The confirm button flows into the result: the same message's caption becomes "received", no new message.
        done_caption = f"<b>طلب الحجز #{rec['id']}</b>\n\n{_fields_html(rec)}\n\n{SUBMITTED_TEXT}"
        try:
            await context.bot.edit_message_caption(chat_id=chat_id, message_id=q.message.message_id,
                                                   caption=done_caption, parse_mode=ParseMode.HTML, reply_markup=None)
        except Exception:
            await context.bot.send_message(chat_id, SUBMITTED_TEXT)
        await notify_admins(context, rec)
        return

    await q.answer()


async def on_text(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg = update.message
    chat_id = update.effective_chat.id
    form = _form(context)
    if not form or form["step"] in ("welcome", "done"):
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
        form["data"]["phone"] = value
    elif step in ("item", "size"):
        await msg.reply_text("اختار من الأزرار اللي تحت 👇")
        return
    elif step == "photo":
        await msg.reply_text("الصورة بس هي المقبولة هنا 🙏 ابعت صورة/سكرين شوت التحويل.")
        return
    else:  # confirm
        await msg.reply_text("اضغط على أحد الزرارين اللي فوق 👆")
        return

    await go_next(context, chat_id)


async def on_image(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg = update.message
    chat_id = update.effective_chat.id
    form = _form(context)
    if not form or form["step"] in ("welcome", "done"):
        await send_welcome(context, chat_id)
        return
    if form["step"] == "confirm" and msg.media_group_id:
        return   # the rest of an album — the first image was already taken
    if form["step"] != "photo":
        await msg.reply_text("الصورة مش مطلوبة دلوقتي، جاوب على السؤال اللي فوق 🙏")
        return

    if msg.photo:
        form["data"]["photo_kind"], form["data"]["photo_id"] = "photo", msg.photo[-1].file_id
    else:
        form["data"]["photo_kind"], form["data"]["photo_id"] = "document", msg.document.file_id
    await go_next(context, chat_id)


async def on_other(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Stickers, voice, video, files that aren't images, ..."""
    form = _form(context)
    chat_id = update.effective_chat.id
    if not form or form["step"] in ("welcome", "done"):
        await send_welcome(context, chat_id)
    elif form["step"] == "photo":
        await update.message.reply_text("الصورة بس هي المقبولة هنا 🙏 ابعت صورة/سكرين شوت التحويل.")
    else:
        await update.message.reply_text("جاوب على السؤال اللي فوق 🙏")


def _is_admin(user) -> bool:
    return user is not None and user.id in ADMIN_IDS


def _app_caption(rec: dict, title: str, footer: str = "") -> str:
    acct = f" (@{_esc(rec['tg_username'])})" if rec.get("tg_username") else ""
    return (
        f"{title} #{rec['id']}\n\n"
        f"{_fields_html(rec)}\n\n"
        f'🆔 حساب التليجرام: <a href="tg://user?id={rec["user_id"]}">{_esc(rec.get("tg_full_name") or rec["user_id"])}</a>{acct}\n'
        f"🕒 {_fmt_time(rec['created_at'])}"
        f"{footer}"
    )


def _decision_footer(rec: dict) -> str:
    if rec["status"] == "pending":
        return ""
    who = _esc((rec.get("decided_by") or {}).get("name", "?"))
    mark = "✅ تم القبول" if rec["status"] == "accepted" else "❌ تم الرفض"
    return f"\n\n{mark} بواسطة {who} — {_fmt_time(rec['decided_at'])}"


def _review_kb(rec: dict) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[
        InlineKeyboardButton(ACCEPT_BTN, callback_data=f"adm:acc:{rec['id']}"),
        InlineKeyboardButton(REJECT_BTN, callback_data=f"adm:rej:{rec['id']}"),
    ]])


async def _send_card(bot, chat_id: int, rec: dict, caption: str, markup):
    if rec["photo_kind"] == "photo":
        return await bot.send_photo(chat_id, rec["photo_id"], caption=caption, parse_mode=ParseMode.HTML, reply_markup=markup)
    return await bot.send_document(chat_id, rec["photo_id"], caption=caption, parse_mode=ParseMode.HTML, reply_markup=markup)


async def notify_admins(context, rec: dict) -> None:
    """DMs the application to every admin with [قبول]/[رفض]. Nothing goes to the results group yet."""
    if not ADMIN_IDS:
        log.warning("ADMIN_IDS is empty — application #%s is saved as pending but nobody was notified.", rec["id"])
        return
    for admin_id in sorted(ADMIN_IDS):
        try:
            sent = await _send_card(context.bot, admin_id, rec, _app_caption(rec, "📥 <b>طلب حجز جديد</b>"), _review_kb(rec))
            rec["admin_msgs"][str(admin_id)] = sent.message_id
        except Exception as e:
            log.error("Couldn't notify admin %s about #%s (has the admin pressed /start?): %s", admin_id, rec["id"], e)
    try:
        await commit()
    except Exception:
        log.exception("Couldn't save admin message ids")


async def _post_to_group(context, rec: dict):
    return await _send_card(context.bot, GROUP_ID, rec, _app_caption(rec, "✅ <b>حجز مقبول</b>"), None)


async def _refresh_admin_cards(context, rec: dict) -> None:
    caption = _app_caption(rec, "📥 <b>طلب حجز</b>", _decision_footer(rec))
    for admin_id, msg_id in (rec.get("admin_msgs") or {}).items():
        try:
            await context.bot.edit_message_caption(chat_id=int(admin_id), message_id=msg_id, caption=caption,
                                                   parse_mode=ParseMode.HTML, reply_markup=None)
        except Exception:
            pass   # message deleted / unchanged — nothing to do


async def on_admin_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    q = update.callback_query
    admin = q.from_user
    if not _is_admin(admin):
        await q.answer("مش مسموحلك تعمل كده", show_alert=True)
        return
    try:
        _, action, sid = (q.data or "").split(":")
    except ValueError:
        await q.answer()
        return
    rec = DATA["applications"].get(sid)
    if rec is None:
        await q.answer("الطلب ده مش موجود", show_alert=True)
        return
    if rec["status"] != "pending":
        await q.answer(f"الطلب ده اتقرر فيه بالفعل ({'مقبول' if rec['status'] == 'accepted' else 'مرفوض'})", show_alert=True)
        await _refresh_admin_cards(context, rec)
        return

    if action == "acc":
        try:
            posted = await _post_to_group(context, rec)   # only an ACCEPTED application reaches the first group
        except Exception:
            log.exception("Couldn't post accepted application #%s to the results group", sid)
            await q.answer("معرفتش أبعت للجروب — اتأكد إن البوت فيه وجرب تاني", show_alert=True)
            return   # still pending: nothing was decided
        rec["group_msg_id"] = posted.message_id
        rec["status"] = "accepted"
    elif action == "rej":
        rec["status"] = "rejected"
    else:
        await q.answer()
        return
    now = _now_iso()
    rec["decided_by"] = {"id": admin.id, "name": admin.full_name}
    rec["decided_at"] = rec["updated_at"] = now
    try:
        await commit()
    except Exception:
        log.exception("Couldn't save the decision on #%s", sid)
    await q.answer("تم ✅")
    await _refresh_admin_cards(context, rec)
    try:
        await context.bot.send_message(rec["user_id"], ACCEPTED_TEXT if rec["status"] == "accepted" else REJECTED_TEXT)
    except Exception:
        pass   # the applicant blocked the bot — the decision still stands


# ── Admin commands ────────────────────────────────────────────────────────────
async def cmd_pending(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not _is_admin(update.effective_user):
        return
    pending = [r for r in DATA["applications"].values() if r["status"] == "pending"]
    pending.sort(key=lambda r: r["id"])
    if not pending:
        await update.message.reply_text("مفيش طلبات معلقة ✅")
        return
    admin_id = update.effective_user.id
    for rec in pending[:20]:
        try:
            sent = await _send_card(context.bot, admin_id, rec, _app_caption(rec, "📥 <b>طلب حجز معلق</b>"), _review_kb(rec))
            rec["admin_msgs"][str(admin_id)] = sent.message_id
        except Exception as e:
            log.error("Couldn't re-send #%s: %s", rec["id"], e)
    if len(pending) > 20:
        await update.message.reply_text(f"فيه {len(pending) - 20} طلب كمان — خلّص دول وابعت /pending تاني.")
    await commit()


async def cmd_stats(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not _is_admin(update.effective_user):
        return
    apps = list(DATA["applications"].values())
    count = lambda st: sum(1 for a in apps if a["status"] == st)
    await update.message.reply_text(
        f"👥 المستخدمين: {len(DATA['users'])}\n"
        f"📋 الطلبات: {len(apps)} — معلق {count('pending')} · مقبول {count('accepted')} · مرفوض {count('rejected')}\n"
        f"🗄 آخر نسخة احتياطية: {_fmt_time(_last_backup_ok_iso) if _last_backup_ok_iso else 'لسه'}"
        f"{'' if RESTORE_OK else chr(10) + '⚠️ النسخ الاحتياطي واقف — الاستعادة فشلت (/restore)'}"
    )


async def cmd_backup(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not _is_admin(update.effective_user):
        return
    if not RESTORE_OK:
        await update.message.reply_text("⚠️ النسخ الاحتياطي واقف لأن آخر استعادة فشلت. جرب /restore الأول.")
        return
    ok = await backup_to_storage(context, force=True, repair=True)
    await update.message.reply_text("تم رفع نسخة احتياطية ✅" if ok else "❌ فشل رفع النسخة — شوف الـ logs.")


async def cmd_restore(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not _is_admin(update.effective_user):
        return
    result = await restore_from_storage(context.bot)
    texts = {
        "restored": f"تمت الاستعادة ✅ ({len(DATA['users'])} مستخدم · {len(DATA['applications'])} طلب)",
        "no_backup": "مفيش نسخة احتياطية متثبتة في جروب التخزين.",
        "not_configured": "STORAGE_GROUP_ID مش متظبط.",
    }
    await update.message.reply_text(texts.get(result, f"❌ {result}"))


async def on_error(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    log.error("Unhandled error", exc_info=context.error)


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
    request_backup()   # the first loop pass uploads only if something differs from the restored backup
    app.bot_data["backup_task"] = asyncio.create_task(_backup_loop(app))


async def post_stop(app: Application) -> None:
    """Last backup on shutdown, so a redeploy doesn't lose the changes since the last upload."""
    task = app.bot_data.get("backup_task")
    if task:
        task.cancel()
    try:
        await asyncio.wait_for(backup_to_storage(SimpleNamespace(bot=app.bot), force=True), timeout=FINAL_BACKUP_TIMEOUT)
    except Exception as e:
        log.error("Final backup on stop incomplete: %r", e)


def main() -> None:
    if not BOT_TOKEN:
        raise SystemExit("Set the BOT_TOKEN environment variable.")
    app = Application.builder().token(BOT_TOKEN).post_init(post_init).post_stop(post_stop).build()
    private = filters.ChatType.PRIVATE
    app.add_handler(CommandHandler("start", start, filters=private))
    app.add_handler(CommandHandler("pending", cmd_pending, filters=private))
    app.add_handler(CommandHandler("stats", cmd_stats, filters=private))
    app.add_handler(CommandHandler("backup", cmd_backup, filters=private))
    app.add_handler(CommandHandler("restore", cmd_restore, filters=private))
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
