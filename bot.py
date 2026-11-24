"""
Semi Senior booking bot (Arabic).

Flow:  /start -> welcome + [أحجز معانا ❤️‍🔥]
       -> name -> Telegram username -> phone -> هودي / بيسبول -> size (S/M/L/XL, with size-guide link)
       -> payment screenshot (images only)
       -> the user gets everything back with [أضغط لتأكيد البيانات] / [الرجوع]
       -> on confirm the booking (data + screenshot) is posted to the results group.
Every step has an [الرجوع] button.

Railway variables:
    BOT_TOKEN   (required)  token from @BotFather
    GROUP_ID    (optional)  results group, default -1005980424677 — the bot must be a member of it

requirements.txt:  python-telegram-bot>=21.0,<22
"""

import html
import logging
import os
import re
from datetime import datetime
from zoneinfo import ZoneInfo

from telegram import InlineKeyboardButton, InlineKeyboardMarkup, LinkPreviewOptions, Update
from telegram.constants import ParseMode
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
GROUP_ID = int(os.environ.get("GROUP_ID", "-1005980424677"))
TZ = ZoneInfo("Africa/Cairo")
SIZE_GUIDE_URL = "https://t.me/Semi_senior44/2194"
MIN_NAME_WORDS = 2          # "الاسم الكامل" — set to 1 to accept a single word

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


async def send_welcome(context: ContextTypes.DEFAULT_TYPE, chat_id: int) -> None:
    context.user_data["form"] = {"step": "welcome", "data": {}, "prompt_id": None, "sending": False}
    msg = await context.bot.send_message(
        chat_id,
        WELCOME_TEXT,
        parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton(BOOK_BTN, callback_data="book")]]),
    )
    context.user_data["form"]["prompt_id"] = msg.message_id


async def ask(context: ContextTypes.DEFAULT_TYPE, chat_id: int, step: str) -> None:
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
    else:
        text, kb = _prompt(step)
        msg = await context.bot.send_message(chat_id, text, parse_mode=ParseMode.HTML,
                                             reply_markup=kb, link_preview_options=NO_PREVIEW)
    form["prompt_id"] = msg.message_id


async def go_next(context: ContextTypes.DEFAULT_TYPE, chat_id: int) -> None:
    await _clear_prompt_buttons(context, chat_id)
    step = _form(context)["step"]
    await ask(context, chat_id, STEPS[STEPS.index(step) + 1])


# ── Handlers ──────────────────────────────────────────────────────────────────
async def start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await send_welcome(context, update.effective_chat.id)


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
        await _clear_prompt_buttons(context, chat_id)
        await ask(context, chat_id, "name")
        return

    if data.startswith("back:"):
        step = data.split(":", 1)[1]
        if form["step"] != step:
            await q.answer("السؤال ده قديم", show_alert=False)
            return
        await q.answer()
        await _clear_prompt_buttons(context, chat_id)
        if step == "name":
            await send_welcome(context, chat_id)
        else:
            await ask(context, chat_id, STEPS[STEPS.index(step) - 1])
        return

    if data.startswith("pick:"):
        _, step, idx = data.split(":")
        options = {"item": ITEMS, "size": SIZES}.get(step)
        if form["step"] != step or options is None or not idx.isdigit() or int(idx) >= len(options):
            await q.answer("السؤال ده قديم", show_alert=False)
            return
        await q.answer()
        form["data"][step] = options[int(idx)]
        await go_next(context, chat_id)
        return

    if data == "confirm":
        if form["step"] != "confirm" or form.get("sending"):
            await q.answer()
            return
        form["sending"] = True
        try:
            await _send_to_group(context, q.from_user, form["data"])
        except Exception:
            log.exception("Couldn't send the booking to the results group")
            form["sending"] = False
            await q.answer("حصلت مشكلة وإحنا بنبعت بياناتك، جرب تاني كمان شوية 🙏", show_alert=True)
            return
        await q.answer()
        await _clear_prompt_buttons(context, chat_id)
        context.user_data["form"] = {"step": "done", "data": {}, "prompt_id": None, "sending": False}
        await context.bot.send_message(chat_id, "تم تسجيل بياناتك ✅\nشكراً ليك ❤️‍🔥")
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


async def _send_to_group(context: ContextTypes.DEFAULT_TYPE, user, data: dict) -> None:
    acct = f" (@{_esc(user.username)})" if user.username else ""
    caption = (
        "🔥 <b>حجز جديد</b>\n\n"
        f"{_fields_html(data)}\n\n"
        f'🆔 حساب التليجرام: <a href="tg://user?id={user.id}">{_esc(user.full_name)}</a>{acct}\n'
        f"🕒 {datetime.now(TZ).strftime('%d/%m/%Y %H:%M')}"
    )
    if data["photo_kind"] == "photo":
        await context.bot.send_photo(GROUP_ID, data["photo_id"], caption=caption, parse_mode=ParseMode.HTML)
    else:
        await context.bot.send_document(GROUP_ID, data["photo_id"], caption=caption, parse_mode=ParseMode.HTML)


async def on_error(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    log.error("Unhandled error", exc_info=context.error)


def main() -> None:
    if not BOT_TOKEN:
        raise SystemExit("Set the BOT_TOKEN environment variable.")
    app = Application.builder().token(BOT_TOKEN).build()
    private = filters.ChatType.PRIVATE
    app.add_handler(CommandHandler("start", start, filters=private))
    app.add_handler(CallbackQueryHandler(on_callback))
    app.add_handler(MessageHandler(private & (filters.PHOTO | filters.Document.IMAGE), on_image))
    app.add_handler(MessageHandler(private & filters.TEXT & ~filters.COMMAND, on_text))
    app.add_handler(MessageHandler(
        private & ~filters.TEXT & ~filters.COMMAND & ~filters.PHOTO & ~filters.Document.IMAGE, on_other))
    app.add_error_handler(on_error)
    app.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()
