# -*- coding: utf-8 -*-
"""LZT Market -> FunPay resale plugin.

The plugin keeps LZT search, account operations, purchasing, and FunPay lot
population separate. Purchasing supports both automatic paid-order handling
and explicit Telegram confirmation; customer delivery remains protected by
the order state machine.
"""

from __future__ import annotations

import html
import base64
import hashlib
import hmac
import json
import logging
import os
import struct
import tempfile
import threading
import time
import re
from dataclasses import asdict, dataclass
from typing import Any, Callable

import requests
from cardinal import Cardinal
from FunPayAPI.common.enums import MessageTypes, OrderStatuses, SubCategoryTypes
from FunPayAPI.updater.events import NewMessageEvent, NewOrderEvent, OrderStatusChangedEvent
from telebot.types import InlineKeyboardButton as B
from telebot.types import InlineKeyboardMarkup as K
from tg_bot import CBT as GLOBAL_CBT


NAME = "LZT to FunPay Resale"
VERSION = "0.20.3"
CREDITS = "@n3mpt"
DESCRIPTION = "Ручная перепродажа LZT-аккаунтов через FunPay с пресетами и защищённым жизненным циклом."
UUID = "4e7506a8-8e7e-4ebd-9fd9-52cdb6f6a6e8"
SETTINGS_PAGE = True
BIND_TO_DELETE = None

logger = logging.getLogger("FPC.LZTToFPResale")
_cardinal: Cardinal | None = None
_temporary: dict[tuple[int, int], dict[str, Any]] = {}
_debug_item_ids: dict[int, str] = {}
_purchase_confirmations: dict[tuple[int, str], dict[str, Any]] = {}
_lock = threading.RLock()
_request_lock = threading.Lock()
_refresh_lock = threading.Lock()
_lot_reconcile_lock = threading.Lock()
_purchase_lock = threading.Lock()
_balance_monitor_stop = threading.Event()
_balance_monitor_thread: threading.Thread | None = None
_catalog_monitor_stop = threading.Event()
_catalog_monitor_thread: threading.Thread | None = None
_last_lzt_balance: dict[str, Any] = {}
_last_request_at = 0.0
_customer_delete_confirmations: dict[tuple[str, int], dict[str, Any]] = {}
_valorant_skin_names: dict[str, dict[str, str]] = {}
_valorant_skin_names_loaded: set[str] = set()
_valorant_skin_names_lock = threading.Lock()
CUSTOMER_DELETE_CONFIRMATION_TTL_SECONDS = 10 * 60
AUTO_REFUND_VERIFY_ATTEMPTS = 3
AUTO_REFUND_VERIFY_DELAY_SECONDS = 1.0

# A refund is safe only for a validation rejection, not for arbitrary LZT
# errors. Other 4xx responses can mean permissions, balance, price, or an
# unknown purchase state and must remain a manual-review case.
LZT_ACCOUNT_VALIDATION_ERROR_MARKERS = (
    ("провер", "ошиб"),
    ("check", "error"),
    ("validation", "error"),
)
DELIVERY_DATA_MARKERS = (
    "данные для входа",
    "логин:",
    "пароль:",
    "login:",
    "password:",
    "пароль почты",
    "email:",
    "почта:",
    "steam guard",
    "код steam",
    "код почты",
    "данные от резервной почты",
    "backup email",
    "recovery email",
)

LZT_BASE_URL = "https://api.lzt.market"
VALORANT_SKIN_CATALOG_URL = "https://valorant-api.com/v1/weapons/skins"
SEARCH_MAX_PAGES = 5
CATALOG_REFRESH_INTERVAL_SECONDS = 15 * 60
FUNPAY_LOT_CREATE_DELAY_SECONDS = 3.0
FUNPAY_LOT_SAVE_DELAY_SECONDS = 1.5
FUNPAY_LOT_SAVE_FAILURE_PAUSE_SECONDS = 5.0
FUNPAY_LOT_SUMMARY_MAX_LENGTH = 100
_funpay_lot_save_lock = threading.Lock()
_last_funpay_lot_save_at = 0.0

DEFAULT_DOTA_FILTERS: dict[str, Any] = {
    "game[]": [570],
    "no_vac": True,
    "reg": 1000,
    "reg_period": "day",
    "daybreak": 1000,
    "no_trans": True,
    "mafile": "yes",
    "d2_game_count_min": 300,
    "d2_behavior_min": 5000,
    "order_by": "price",
}


# LZT returns country names in English, while FunPay's Steam form expects the
# localized option values from its <select>. Keep this mapping explicit so a
# metadata value cannot silently turn a valid lot into an invalid request.
FUNPAY_REGION_ALIASES = {
    "argentina": "Аргентина",
    "аргентина": "Аргентина",
    "bulgaria": "Болгария",
    "болгария": "Болгария",
    "hungary": "Венгрия",
    "венгрия": "Венгрия",
    "vietnam": "Вьетнам",
    "вьетнам": "Вьетнам",
    "germany": "Германия",
    "германия": "Германия",
    "indonesia": "Индонезия",
    "индонезия": "Индонезия",
    "spain": "Испания",
    "испания": "Испания",
    "kazakhstan": "Казахстан",
    "казахстан": "Казахстан",
    "china": "Китай",
    "китай": "Китай",
    "poland": "Польша",
    "польша": "Польша",
    "romania": "Румыния",
    "румыния": "Румыния",
    "slovakia": "Словакия",
    "словакия": "Словакия",
    "united states": "США",
    "usa": "США",
    "сша": "США",
    "turkey": "Турция",
    "turkiye": "Турция",
    "турция": "Турция",
    "ukraine": "Украина",
    "украина": "Украина",
    "france": "Франция",
    "франция": "Франция",
    "czech republic": "Чехия",
    "czechia": "Чехия",
    "чехия": "Чехия",
    "estonia": "Эстония",
    "эстония": "Эстония",
    "russian federation": "Россия",
    "russia": "Россия",
    "россия": "Россия",
    "korea, republic of": "Южная Корея",
    "south korea": "Южная Корея",
    "republic of korea": "Южная Корея",
    "южная корея": "Южная Корея",
    "other": "Другой",
    "другой": "Другой",
}

DOTA_RANK_NAMES_RU = ("РЕКРУТ", "СТРАЖ", "РЫЦАРЬ", "ГЕРОЙ", "ЛЕГЕНДА", "ВЛАСТЕЛИН", "БОЖЕСТВО")
DOTA_RANK_NAMES_EN = ("RECRUIT", "GUARDIAN", "CRUSADER", "ARCHON", "LEGEND", "ANCIENT", "DIVINE")

VALORANT_SERVER_IDS = {
    "AP": "3937",
    "BR": "3940",
    "EU": "3938",
    "KR": "3941",
    "LATAM": "3942",
    "NA": "3939",
    "RU": "3943",
    "TR": "3944",
}
VALORANT_AGENT_NAMES = {
    "41fb69c1-4189-7b37-f117-bcaf1e96f1bf": "Astra",
    "5f8d3a7f-467b-97f3-062c-13acf203c006": "Breach",
    "9f0d8ba9-4140-b941-57d3-a7ad57c6b417": "Brimstone",
    "22697a3d-45bf-8dd7-4fec-84a9e28c69d7": "Chamber",
    "1dbf2edd-4729-0984-3115-daa5eed44993": "Clove",
    "117ed9e3-49f3-6512-3ccf-0cada7e3823b": "Cypher",
    "cc8b64c8-4b25-4ff9-6e7f-37b4da43d235": "Deadlock",
    "dade69b4-4f5a-8528-247b-219e5a1facd6": "Fade",
    "e370fa57-4757-3604-3648-499e1f642d3f": "Gekko",
    "95b78ed7-4637-86d9-7e41-71ba8c293152": "Harbor",
    "0e38b510-41a8-5780-5e8f-568b2a4f2d6c": "Iso",
    "add6443a-41bd-e414-f6ad-e58d267f4e95": "Jett",
    "601dbbe7-43ce-be57-2a40-4abd24953621": "KAY/O",
    "1e58de9c-4950-5125-93e9-a0aee9f98746": "Killjoy",
    "7c8a4701-4de6-9355-b254-e09bc2a34b72": "Miks",
    "bb2a4828-46eb-8cd1-e765-15848195d751": "Neon",
    "8e253930-4c05-31dd-1b6c-968525494517": "Omen",
    "eb93336a-449b-9c1b-0a54-a891f7921d69": "Phoenix",
    "f94c3b30-42be-e959-889c-5aa313dba261": "Raze",
    "a3bfb853-43b2-7238-a4f1-ad90e9e46bcc": "Reyna",
    "569fdd95-4d10-43ab-ca70-79becc718b46": "Sage",
    "6f2a04ca-43e0-be17-7f36-b3908627744d": "Skye",
    "320b2a48-4d9b-a075-30f1-1f93a9b638fa": "Sova",
    "b444168c-4e35-8076-db47-ef9bf368f384": "Tejo",
    "92eeef5d-43b5-1d4a-8d03-b3927a09034b": "Veto",
    "707eab51-4836-f488-046a-cda6bf494859": "Viper",
    "efba5359-4016-a1e5-7626-b1ae76895940": "Vyse",
    "df1cb487-4902-002e-5c17-d28e83e78588": "Waylay",
    "7f94d92c-4234-0a36-9646-3a87eb8b5c89": "Yoru",
}
VALORANT_RANK_TRANSLATIONS_RU_EN = {
    "железо": "Iron",
    "бронза": "Bronze",
    "серебро": "Silver",
    "золото": "Gold",
    "платина": "Platinum",
    "алмаз": "Diamond",
    "расцвет": "Ascendant",
    "бессмертный": "Immortal",
    "радиант": "Radiant",
}
VALORANT_RANK_TRANSLATIONS_EN_RU = {
    value.casefold(): key.capitalize()
    for key, value in VALORANT_RANK_TRANSLATIONS_RU_EN.items()
}

VALORANT_DESCRIPTION_RU = """💎 Доброго времени суток, уважаемый покупатель! Пожалуйста, ознакомься с информацией, представленной ниже.

🧊 После покупки вы получите аккаунт вместе с почтой, разумеется с возможностью перевязать всё под себя.

🌀 После покупки аккаунт гарантированно ваш, вы можете использовать его как угодно.
🌀 Продавец НЕ ВОССТАНОВИТ доступ к аккаунту через поддержку, гарантией может выступать весомое количество положительных отзывов на сделках по продаже аккаунтов.

⚡Список персонажей на аккаунте: {agents}.

❄️ После оплаты у вас будет время проверить аккаунт, перевязать его на свои данные. После этого не забудьте, пожалуйста ПОДТВЕРДИТЬ выполнения заказа (оплату).
❄️ Продавец будет рад любому отзыву, так вы сможете и высказать собственное мнение, и позволите другим покупателям знать о том, что здесь не обманывают.
❄️ В случае, если у вас возникли какие-либо трудности, продавец рекомендует воздержаться от оставления негативного отзыва, а вместо этого написать ему, чтобы проблема могла быть разрешена."""

VALORANT_DESCRIPTION_EN = """💎 Good day, dear buyer! Please review the information provided below.

🧊 After purchase, you will receive the account along with the email, of course with the ability to link everything to yourself.

🌀 After purchase, the account is guaranteed to be yours, you can use it however you like.
🌀 The seller will NOT RESTORE access to the account through support, the guarantee can be a significant number of positive reviews on account sales.

⚡Agent list on current account: {agents}.

❄️ After payment, you will have time to check the account and link it to your details. After that, please don't forget to CONFIRM the order completion (payment).
❄️ The seller will appreciate any feedback, as you can express your own opinion and allow other buyers to know that they are not being deceived here.
❄️ If you encounter any difficulties, the seller recommends refraining from leaving a negative review, and instead writing to him so that the problem can be resolved."""

VALORANT_SKINS_DESCRIPTION_RU = """💎 Доброго времени суток, уважаемый покупатель! Пожалуйста, ознакомься с информацией, представленной ниже.

🧊 После покупки вы получите аккаунт вместе с почтой, разумеется с возможностью перевязать всё под себя.

🌀 После покупки аккаунт гарантированно ваш, вы можете использовать его как угодно.
🌀 Продавец НЕ ВОССТАНОВИТ доступ к аккаунту через поддержку, гарантией может выступать весомое количество положительных отзывов на сделках по продаже аккаунтов.

⚡Список персонажей на аккаунте: {agents}.

⚡Список скинов на аккаунте: {skins_ru}.

❄️ После оплаты у вас будет время проверить аккаунт, перевязать его на свои данные. После этого не забудьте, пожалуйста ПОДТВЕРДИТЬ выполнения заказа (оплату).
❄️ Продавец будет рад любому отзыву, так вы сможете и высказать собственное мнение, и позволите другим покупателям знать, что здесь не обманывают.
❄️ В случае, если у вас возникнут какие-либо трудности, продавец рекомендует воздержаться от оставления негативного отзыва и вместо этого написать ему, чтобы проблему можно было решить."""

VALORANT_SKINS_DESCRIPTION_EN = """💎 Good day, dear buyer! Please review the information provided below.

🧊 After purchase, you will receive the account along with the email, of course with the ability to link everything to yourself.

🌀 After purchase, the account is guaranteed to be yours, you can use it however you like.
🌀 The seller will NOT RESTORE access to the account through support, the guarantee can be a significant number of positive reviews on account sales.

⚡Agent list on current account: {agents}.

⚡Skin list on current account: {skins_en}.

❄️ After payment, you will have time to check the account and link it to your details. After that, please don't forget to CONFIRM the order completion (payment).
❄️ The seller will appreciate any feedback, as you can express your own opinion and allow other buyers to know that they are not being deceived here.
❄️ If you encounter any difficulties, the seller recommends refraining from leaving a negative review and instead writing to him so that the problem can be resolved."""

DOTA_DESCRIPTION_RU = """💎 Доброго времени суток, уважаемый покупатель! Пожалуйста, ознакомься с информацией, представленной ниже.

🧊 После покупки вы получите аккаунт вместе с почтой, разумеется с возможностью перевязать всё под себя.
🧊 Аккаунт гарантированно не имеет VAC-бана в Dota 2.

🌀 После покупки аккаунт гарантированно ваш, вы можете использовать его как угодно.
🌀 Продавец НЕ ВОССТАНОВИТ доступ к аккаунту через поддержку, гарантией может выступать весомое количество положительных отзывов на сделках по продаже аккаунтов.
🌀 При игре на аккаунте не использовался сторонний софт вроде "Волка", "Зонтика", "Буквы М" или прочего, к чему продавец призывает и вас, если хотите сохранить аккаунт.

❄️ После оплаты у вас будет время проверить аккаунт, перевязать его на свои данные. После этого не забудьте, пожалуйста ПОДТВЕРДИТЬ выполнение заказа (оплату).
❄️ Продавец будет рад любому отзыву, так вы сможете и высказать собственное мнение, и позволите другим покупателям знать о том, что здесь не обманывают.
❄️ В случае, если у вас возникли какие-либо трудности, продавец рекомендует воздержаться от оставления негативного отзыва, а вместо этого написать ему, чтобы проблема могла быть разрешена.

🧿 Ответы на частые вопросы, которые встречались в практике:

❓ КАКОЙ УРОВЕНЬ ТРОФЕЯ? АККАУНТ МЕЙНПУЛЬНЫЙ?
❗ Данный аккаунт является мейнпульным, в случае, если об этом заявлено в названии лота. Трофей не играет особой роли, так как не существует прямой корреляции между пулом и трофеем. Если аккаунт зарегистрирован ДО введения системы пулов (и уж тем более если аккаунт настолько старый, что введён до системы 100 часов), то там может быть хоть первый трофей и 1 матч, но там будет доступен рейтинг и будут искаться мейнпульные лобби. Я ГАРАНТИРУЮ, что если в названии указано слово "мейнпул", то аккаунт будет мейнпульным.

❓ АККАУНТ СОЗДАВАЛСЯ БОТАМИ (ПЕСОЧНЫЙ)?
❗ Нет, аккаунты, которые я продаю, прокачаны человеком. Однако если вы встретите где-то объявления с песочными аккаунтами, то крайне маловероятно, что вы поймаете бан, если чистите свой Steam от горы userdata. К тому же, если на аккаунте указаны рекалибровки в наличии, то это ТОЧНО не песочный аккаунт. Песочные аккаунты создаются за пару дней и сразу продаются, там не может быть рекалибровки и уж тем более второй рекалибровки.

❓ КАКОВЫ ГАРАНТИИ?
❗ В качестве весомого аргумента для покупки именно у меня могут выступать отзывы у меня в профиле, подавляющее большинство которых относятся к недешёвым лотам с аккаунтами. Каждый аккаунт, которым я торгую, обезопасен от любых махинаций с моей стороны, а потому, перевязав всё под себя, я никоим образом не смогу забрать аккаунт себе.

🌊 А теперь, когда вы это прочитали - приятного использования!"""

DOTA_DESCRIPTION_EN = """💎 Good day, dear customer! Please review the information provided below.

🧊 After purchase, you will receive an account along with mail, with the ability to link everything to your own details.
🧊 The account is guaranteed not to have a VAC ban in Dota 2.

🌀 After purchasing, the account is guaranteed to be yours; you can use it as you wish.
🌀 The seller WILL NOT RESTORE access to the account through support; a significant number of positive reviews on account sales transactions can be a guarantee.
🌀 When playing on your account, no third-party software was used, such as “Wolf”, “Umbrella”, “Letter M” or anything else that the seller encourages you to use if you want to keep the account.

❄️ After payment, you will have time to check the account and link it to your data. After this, please do not forget to CONFIRM the completion of the order (payment).
❄️ The seller will be happy to receive any feedback, so you can express your own opinion and let other buyers know that they are not being deceived here.
❄️ In case you have any difficulties, the seller recommends that you refrain from leaving negative feedback and instead write to him so that the problem can be resolved.

🧿 Answers to frequently asked questions encountered in practice:

❓ WHAT IS THE LEVEL OF THE TROPHY? IS YOUR ACCOUNT MAINPOOL?
❗ This account is a mainpool account if this is stated in the title of the lot. The trophy does not play a special role, since there is no direct correlation between the pool and the trophy. If an account was registered BEFORE the introduction of the pool system (and even more so if the account is so old that it was created before the 100-hour system), then there may be at least the first trophy and 1 match, but a rating will be available and mainpool lobbies will be found. I GUARANTEE that if the word "mainpool" is indicated in the name, then the account will be mainpool.

❓ WAS THE ACCOUNT CREATED BY BOTS (SANDY)?
❗ No, the accounts I sell are upgraded by a person. However, if you come across ads with sandbox accounts, it is extremely unlikely that you will get banned if you clean your Steam from a mountain of userdata. In addition, if the account indicates that recalibrations are available, then it is DEFINITELY not a sandbox account. Sandbox accounts are created in a couple of days and sold immediately; there can be no recalibration, much less a second recalibration.

❓ WHAT ARE THE GUARANTEES?
❗ The reviews in my profile can be a strong argument for purchasing from me, the vast majority of which relate to expensive lots with accounts. Each account I trade is protected from any fraud on my part, and therefore, having linked everything to yourself, I will in no way be able to take the account back.

🌊 And now that you have read this - enjoy using it!"""


@dataclass
class Settings:
    api_token: str = ""
    language: str = "ru"
    proxy: str = ""
    timeout_seconds: float = 300.0
    min_request_delay_seconds: float = 0.5
    balance_id: int = 0
    auto_purchase_after_paid: bool = True

    @classmethod
    def from_dict(cls, data: Any) -> "Settings":
        result = cls()
        if isinstance(data, dict):
            for key in asdict(result):
                if key in data:
                    setattr(result, key, data[key])
        result.api_token = str(result.api_token or "").strip()
        result.language = str(result.language or "ru").strip().lower()
        if result.language not in {"ru", "en"}:
            result.language = "ru"
        result.proxy = str(result.proxy or "").strip()
        result.timeout_seconds = _float(result.timeout_seconds, 300.0, minimum=1.0)
        result.min_request_delay_seconds = _float(result.min_request_delay_seconds, 0.5, minimum=0.0)
        result.balance_id = max(0, _int(result.balance_id, 0))
        result.auto_purchase_after_paid = bool(data.get("auto_purchase_after_paid", True)) if isinstance(data, dict) else True
        return result


SETTINGS = Settings()


def _int(value: Any, default: int = 0) -> int:
    try:
        return int(str(value).strip())
    except (TypeError, ValueError):
        return default


def _float(value: Any, default: float, minimum: float) -> float:
    try:
        return max(minimum, float(str(value).strip().replace(",", ".")))
    except (TypeError, ValueError):
        return default


def _short_exception(exc: BaseException, limit: int = 600) -> str:
    """Keep external HTML/error pages out of logs and Telegram messages."""
    text = " ".join(str(exc).split())
    if len(text) > limit:
        text = text[:limit - 3] + "..."
    return f"{type(exc).__name__}: {text}" if text else type(exc).__name__


def _is_funpay_lot_save_error(exc: BaseException) -> bool:
    """Identify a rejected FunPay lot save without relying on response text."""
    return type(exc).__name__ == "LotSavingError" or "lots/offerSave" in str(
        getattr(exc, "url", "") or ""
    )


def _funpay_lot_save_error_detail(exc: BaseException) -> str:
    """Extract FunPay's structured save error without logging its HTML response."""
    parts: list[str] = []
    message = str(getattr(exc, "error_message", "") or "").strip()
    if message:
        parts.append(message)
    errors = getattr(exc, "errors", {})
    if isinstance(errors, dict):
        for field, value in errors.items():
            text = " ".join(str(value).split())
            if text:
                parts.append(f"{field}: {text}")
    return "; ".join(parts)[:500]


def _is_retryable_funpay_lot_save_error(exc: BaseException) -> bool:
    """Keep retrying transient rejects, but let validation errors reach the queue."""
    response = getattr(exc, "response", None)
    status_code = getattr(response, "status_code", None)
    if status_code == 429:
        return True
    detail = _funpay_lot_save_error_detail(exc).casefold()
    permanent_markers = (
        "слишком длин",
        "заполните",
        "обязательн",
        "некоррект",
        "недопустим",
        "неверн",
        "too long",
        "required",
        "invalid",
    )
    return not any(marker in detail for marker in permanent_markers)


def _fit_funpay_summary(value: Any) -> str:
    """Fit a lot title into FunPay's 100-character summary limit."""
    text = str(value or "")
    if len(text) <= FUNPAY_LOT_SUMMARY_MAX_LENGTH:
        return text
    overflow = len(text) - FUNPAY_LOT_SUMMARY_MAX_LENGTH
    spans = list(re.finditer(r"【([^【】]*)】", text))
    spans.sort(key=lambda match: len(match.group(1)), reverse=True)
    for match in spans:
        inner = match.group(1)
        available = len(inner) - overflow - 3
        if available < 1:
            continue
        shortened = inner[:available].rstrip() + "..."
        result = text[:match.start(1)] + shortened + text[match.end(1):]
        if len(result) <= FUNPAY_LOT_SUMMARY_MAX_LENGTH:
            return result
    return text[:FUNPAY_LOT_SUMMARY_MAX_LENGTH - 3].rstrip() + "..."


def _save_funpay_lot_request(lot_fields: Any) -> dict[str, Any]:
    """Serialize FunPay lot saves so the service never sends them as a burst."""
    global _last_funpay_lot_save_at
    with _funpay_lot_save_lock:
        wait = FUNPAY_LOT_SAVE_DELAY_SECONDS - (
            time.monotonic() - _last_funpay_lot_save_at
        )
        if wait > 0:
            time.sleep(wait)
        _last_funpay_lot_save_at = time.monotonic()
        return _cardinal.account.save_lot(lot_fields) or {}


def _save_funpay_lot_with_retry(
    lot_id: int,
    prepare_fields: Callable[[Any], None],
    *,
    initial_fields: Any | None = None,
    refresh_after_failure: bool = True,
) -> tuple[Any, dict[str, Any], int]:
    """Save one existing lot and keep retrying transient FunPay rejections."""
    if not _cardinal or not _cardinal.account:
        raise RuntimeError("FunPay API не инициализирован")
    fields = initial_fields
    attempts = 0
    while True:
        if fields is None:
            fields = _cardinal.account.get_lot_fields(lot_id)
        prepare_fields(fields)
        try:
            response = _save_funpay_lot_request(fields)
        except Exception as exc:
            if not _is_funpay_lot_save_error(exc):
                raise
            if not _is_retryable_funpay_lot_save_error(exc):
                raise
            attempts += 1
            detail = _funpay_lot_save_error_detail(exc)
            logger.warning(
                "LZT-FP: FunPay rejected lot save lot=%s attempt=%s%s; "
                "retrying the same queue item after %.1f seconds",
                lot_id,
                attempts,
                f" detail={detail}" if detail else "",
                FUNPAY_LOT_SAVE_FAILURE_PAUSE_SECONDS,
            )
            time.sleep(FUNPAY_LOT_SAVE_FAILURE_PAUSE_SECONDS)
            fields = None if refresh_after_failure else initial_fields
            continue
        return fields, response, attempts + 1


def _input_float(value: str) -> float:
    try:
        return float(value.strip().replace(",", "."))
    except (TypeError, ValueError) as exc:
        raise ValueError("нужно указать число") from exc


def _parse_lot_ids(value: str) -> list[int]:
    """Parse a Telegram-entered FunPay lot pool without changing its order."""
    if value.strip() == "-":
        return []
    tokens = [token for token in re.split(r"[\s,;]+", value.strip()) if token]
    if not tokens:
        raise ValueError("укажите хотя бы один ID или отправьте - для очистки пула")
    result: list[int] = []
    seen: set[int] = set()
    invalid: list[str] = []
    for token in tokens:
        if not token.isdigit() or int(token) <= 0:
            invalid.append(token)
            continue
        lot_id = int(token)
        if lot_id not in seen:
            result.append(lot_id)
            seen.add(lot_id)
    if invalid:
        raise ValueError("некорректные ID: " + ", ".join(invalid[:10]))
    return result


def _plugin_dir() -> str:
    path = os.path.join(os.path.dirname(__file__), "..", "storage", "plugins", "lzt_to_fp_resale")
    os.makedirs(path, exist_ok=True)
    return path


def _settings_path() -> str:
    return os.path.join(_plugin_dir(), "settings.json")


def _presets_path() -> str:
    return os.path.join(_plugin_dir(), "presets.json")


def _catalog_path() -> str:
    return os.path.join(_plugin_dir(), "catalog.json")


def _funpay_path() -> str:
    return os.path.join(_plugin_dir(), "funpay.json")


def _accounts_path() -> str:
    return os.path.join(_plugin_dir(), "accounts.json")


def _purchases_path() -> str:
    return os.path.join(_plugin_dir(), "purchases.json")


def _credentials_path() -> str:
    return os.path.join(_plugin_dir(), "credentials.json")


def _orders_path() -> str:
    return os.path.join(_plugin_dir(), "orders.json")


def _atomic_json_save(path: str, data: Any, mode: int = 0o600) -> None:
    directory = os.path.dirname(path)
    fd, temp_path = tempfile.mkstemp(prefix="lztfp_", suffix=".tmp", dir=directory)
    try:
        os.fchmod(fd, mode)
        with os.fdopen(fd, "w", encoding="utf-8") as fp:
            json.dump(data, fp, ensure_ascii=False, indent=2)
            fp.flush()
            os.fsync(fp.fileno())
        os.replace(temp_path, path)
    except Exception:
        try:
            os.unlink(temp_path)
        except OSError:
            pass
        raise


def _load_settings() -> None:
    global SETTINGS
    try:
        with open(_settings_path(), encoding="utf-8") as fp:
            SETTINGS = Settings.from_dict(json.load(fp))
        _save_settings()
    except FileNotFoundError:
        _save_settings()
    except Exception as exc:
        logger.warning("LZT-FP: failed to load settings: %s", exc)


def _save_settings() -> None:
    with _lock:
        _atomic_json_save(_settings_path(), asdict(SETTINGS))


def _default_presets() -> dict[str, dict[str, Any]]:
    common_funpay = {
        "subcategory_id": None,
        "lot_ids": [],
        "offer_type": "Продажа",
        "field_values": {},
        "metadata_map": {},
        "templates": {},
    }
    return {
        "dota_2": {
            "name": "Dota 2",
            "category": "steam",
            "enabled": True,
            "selling_enabled": True,
            "selection_limit": 10,
            "markup_percent": 100.0,
            "filters": DEFAULT_DOTA_FILTERS,
            "funpay": {
                **common_funpay,
                "subcategory_id": 81,
                "price_mode": "buyer",
                "field_values": {
                    "fields[type1]": "Продажа",
                    "fields[type]": "С рейтингом",
                },
                "metadata_map": {
                    "fields[solommr]": "steam_dota2_solo_mmr",
                    "fields[decency]": "steam_dota2_behavior",
                    "fields[politeness]": "steam_dota2_behavior",
                    "fields[games]": "steam_dota2_game_count",
                    "fields[time]": "steam_full_games.list.570.playtime_forever",
                },
                "templates": {
                    "summary_ru": "🧊🌀【АВТО-ВЫДАЧА】❄️~❄️【{mmr} ММР ┃{rank_ru}】❄️~❄️【{mainpool_ru}】❄️~❄️【{games} МАТЧЕЙ】❄️~❄️【{topups_ru}】",
                    "summary_en": "🧊🌀【AUTO-DELIVERY】❄️~❄️【{mmr} MMR ┃{rank_en}】❄️~❄️【{mainpool_en}】❄️~❄️【{games} MATCHES】❄️~❄️【{topups_en}】",
                    "description_ru": DOTA_DESCRIPTION_RU,
                    "description_en": DOTA_DESCRIPTION_EN,
                    "payment_msg_ru": "",
                    "payment_msg_en": "",
                },
            },
        },
        "steam_test": {
            "name": "Test Steam maFile",
            "category": "steam",
            "enabled": True,
            "selling_enabled": True,
            "selection_limit": 10,
            "markup_percent": 25.0,
            "filters": {
                "mafile": "yes",
                "order_by": "price",
            },
            "funpay": {
                **common_funpay,
                "subcategory_id": 89,
                "field_values": {
                    "fields[type]": "",
                    "fields[region]": "",
                },
                "metadata_map": {
                    "fields[region]": "steam_country",
                    "fields[level]": "steam_level",
                },
            },
        },
        "valorant": {
            "name": "Valorant",
            "category": "riot",
            "enabled": True,
            "selling_enabled": True,
            "selection_limit": 10,
            "markup_percent": 25.0,
            "filters": {
                "daybreak": 365,
                "tel": "no",
                "valorant_region[]": ["EU"],
                    "valorant_level_min": 30,
                    "knife": 0,
                "order_by": "price_to_up",
            },
            "funpay": {
                **common_funpay,
                "subcategory_id": 612,
                "price_mode": "buyer",
                "field_values": {
                    "node_id": "612",
                    "fields[type]": "Продажа",
                    "server_id": "3938",
                    "fields[skins]": "-1",
                },
                "metadata_map": {
                    "server_id": "valorant_server_id",
                    "fields[rank]": "valorant_rank_ru",
                    "fields[agent]": "valorant_agent_count",
                },
                "templates": {
                    "summary_ru": "🧊🌀【АВТО-ВЫДАЧА】❄️~❄️【{valorant_rank_title_ru} / КАЛЛИБРОВКА】❄️~❄️【{valorant_level} УРОВЕНЬ】❄️~❄️【ПОЛНЫЙ ДОСТУП】",
                    "summary_en": "🧊🌀【AUTO-DELIVERY】❄️~❄️【{valorant_rank_title_en} / CALLIBRATION】❄️~❄️【{valorant_level} LEVEL】❄️~❄️【FULL ACCESS】",
                    "description_ru": VALORANT_DESCRIPTION_RU,
                    "description_en": VALORANT_DESCRIPTION_EN,
                    "payment_msg_ru": "",
                    "payment_msg_en": "",
                },
            },
        },
        "valorant_skins": {
            "name": "Valorant со скинами",
            "category": "riot",
            "enabled": True,
            "selling_enabled": True,
            "selection_limit": 5,
            "markup_percent": 50.0,
            "filters": {
                "daybreak": 365,
                "tel": "no",
                "knife": 1,
                "valorant_region[]": ["EU"],
                "valorant_level_min": 20,
                "order_by": "price_to_up",
            },
            "funpay": {
                **common_funpay,
                "subcategory_id": 612,
                "price_mode": "buyer",
                "field_values": {
                    "node_id": "612",
                    "fields[type]": "Продажа",
                    "server_id": "3938",
                },
                "metadata_map": {
                    "server_id": "valorant_server_id",
                    "fields[rank]": "valorant_rank_ru",
                    "fields[agent]": "valorant_agent_count",
                    "fields[skins]": "valorant_skin_count",
                },
                "templates": {
                    "summary_ru": "🌸🎀【ПРОДАЖА】💕~💕【{valorant_top_skin_ru} / и др. (СКИНЫ В ОПИСАНИИ)】💕~💕【ПОЛНЫЙ ДОСТУП】💕~💕【УРОВЕНЬ {valorant_level}】",
                    "summary_en": "🌸🎀【FOR SALE】💕~💕【{valorant_top_skin_en} / etc. (SKINS IN DESCRIPTION)】💕~💕【FULL ACCESS】💕~💕【LEVEL {valorant_level}】",
                    "description_ru": VALORANT_SKINS_DESCRIPTION_RU,
                    "description_en": VALORANT_SKINS_DESCRIPTION_EN,
                    "payment_msg_ru": "",
                    "payment_msg_en": "",
                },
            },
        },
    }


def _load_presets() -> dict[str, dict[str, Any]]:
    try:
        with open(_presets_path(), encoding="utf-8") as fp:
            data = json.load(fp)
        if isinstance(data, dict) and data:
            changed = False
            defaults = _default_presets()
            for default_key, default_preset in defaults.items():
                if default_key not in data:
                    data[default_key] = default_preset
                    changed = True
            for key, preset in data.items():
                if not isinstance(preset, dict):
                    continue
                if "selection_limit" not in preset:
                    preset["selection_limit"] = 10
                    changed = True
                if "markup_percent" not in preset:
                    preset["markup_percent"] = 25.0
                    changed = True
                if "selling_enabled" not in preset:
                    preset["selling_enabled"] = True
                    changed = True
                if "funpay" not in preset or not isinstance(preset["funpay"], dict):
                    preset["funpay"] = dict(defaults.get(key, {}).get("funpay", {
                        "subcategory_id": None,
                        "lot_ids": [],
                        "offer_type": "Продажа",
                        "field_values": {},
                        "metadata_map": {},
                        "templates": {},
                    }))
                    changed = True
                default_preset = defaults.get(key)
                default_funpay = default_preset.get("funpay", {}) if isinstance(default_preset, dict) else {}
                if isinstance(default_funpay, dict):
                    for funpay_key in ("subcategory_id", "offer_type", "price_mode"):
                        if funpay_key in default_funpay and funpay_key not in preset["funpay"]:
                            preset["funpay"][funpay_key] = default_funpay[funpay_key]
                            changed = True
                    for mapping_key in ("field_values", "metadata_map", "templates"):
                        defaults_mapping = default_funpay.get(mapping_key, {})
                        current_mapping = preset["funpay"].get(mapping_key, {})
                        if not isinstance(current_mapping, dict):
                            current_mapping = {}
                        for mapping_name, mapping_value in defaults_mapping.items():
                            if mapping_name not in current_mapping:
                                current_mapping[mapping_name] = mapping_value
                                changed = True
                        preset["funpay"][mapping_key] = current_mapping
                if not isinstance(preset["funpay"].get("lot_ids", []), list):
                    preset["funpay"]["lot_ids"] = []
                    changed = True
                if not isinstance(preset["funpay"].get("retired_lot_ids", []), list):
                    preset["funpay"]["retired_lot_ids"] = []
                    changed = True
                filters = preset.get("filters")
                if isinstance(filters, dict) and isinstance(filters.get("mafile"), bool):
                    filters["mafile"] = "yes" if filters["mafile"] else "no"
                    changed = True
                elif key in defaults:
                    default_filters = defaults[key].get("filters", {})
                    if isinstance(default_filters, dict) and not isinstance(filters, dict):
                        preset["filters"] = dict(default_filters)
                        changed = True
                if key == "dota_2" and isinstance(preset.get("filters"), dict):
                    if preset["filters"].get("mafile") != "yes":
                        preset["filters"]["mafile"] = "yes"
                        changed = True
                    field_values = preset["funpay"].setdefault("field_values", {})
                    metadata_map = preset["funpay"].setdefault("metadata_map", {})
                    if isinstance(field_values, dict):
                        if field_values.get("fields[type1]") != "Продажа":
                            field_values["fields[type1]"] = "Продажа"
                            changed = True
                        if field_values.get("fields[type]") != "С рейтингом":
                            field_values["fields[type]"] = "С рейтингом"
                            changed = True
                        if "fields[account_type]" in field_values:
                            changed = True
                        field_values.pop("fields[account_type]", None)
                    if isinstance(metadata_map, dict):
                        if metadata_map.get("fields[politeness]") != "steam_dota2_behavior":
                            metadata_map["fields[politeness]"] = "steam_dota2_behavior"
                            changed = True
                        if metadata_map.get("fields[time]") != "steam_full_games.list.570.playtime_forever":
                            metadata_map["fields[time]"] = "steam_full_games.list.570.playtime_forever"
                            changed = True
                        if "fields[hours]" in metadata_map:
                            changed = True
                        metadata_map.pop("fields[hours]", None)
                    default_templates = default_funpay.get("templates", {}) if isinstance(default_funpay, dict) else {}
                    templates = preset["funpay"].setdefault("templates", {})
                    if isinstance(templates, dict) and isinstance(default_templates, dict):
                        for template_key, template_value in default_templates.items():
                            if not templates.get(template_key) and template_value:
                                templates[template_key] = template_value
                                changed = True
                    if preset["filters"].get("d2_behavior_min") != 5000:
                        preset["filters"]["d2_behavior_min"] = 5000
                        changed = True
                    if _float(preset.get("markup_percent"), 25.0, minimum=0.0) != 100.0:
                        preset["markup_percent"] = 100.0
                        changed = True
            valorant_preset = data.get("valorant")
            if isinstance(valorant_preset, dict):
                valorant_filters = valorant_preset.setdefault("filters", {})
                if isinstance(valorant_filters, dict) and "knife" not in valorant_filters:
                    valorant_filters["knife"] = 0
                    changed = True
            if changed:
                _save_presets(data)
            return data
    except FileNotFoundError:
        pass
    except Exception as exc:
        logger.warning("LZT-FP: failed to load presets: %s", exc)
    presets = _default_presets()
    _save_presets(presets)
    return presets


def _save_presets(presets: dict[str, dict[str, Any]]) -> None:
    with _lock:
        _atomic_json_save(_presets_path(), presets)


def _empty_catalog() -> dict[str, Any]:
    return {"version": 1, "updated_at": None, "last_run": None, "items": {}}


def _load_catalog() -> dict[str, Any]:
    try:
        with open(_catalog_path(), encoding="utf-8") as fp:
            data = json.load(fp)
        if not isinstance(data, dict):
            raise ValueError("catalog root must be an object")
        data.setdefault("version", 1)
        data.setdefault("updated_at", None)
        data.setdefault("last_run", None)
        if not isinstance(data.get("items"), dict):
            data["items"] = {}
        if isinstance(data.get("last_run"), dict) and data["last_run"].get("status") == "running":
            data["last_run"]["status"] = "interrupted"
            data["last_run"]["recovered_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
            _save_catalog(data)
        return data
    except FileNotFoundError:
        catalog = _empty_catalog()
        _save_catalog(catalog)
        return catalog
    except Exception as exc:
        logger.warning("LZT-FP: failed to load catalog: %s", exc)
        return _empty_catalog()


def _save_catalog(catalog: dict[str, Any]) -> None:
    with _lock:
        _atomic_json_save(_catalog_path(), catalog)


def _default_funpay_settings() -> dict[str, Any]:
    return {
        "version": 1,
        "default_template": {
            "summary_ru": "Аккаунт Steam",
            "summary_en": "Steam account",
            "description_ru": "",
            "description_en": "",
            "payment_msg_ru": "",
            "payment_msg_en": "",
        },
        "lot_tags": [],
        "order_messages": {
            "waiting": "⏳ Заказ получен. Аккаунт готовится к передаче.",
            "ready": "✅ Аккаунт готов к выдаче. Используйте команду !help для доступных действий.",
            "failed": "❌ Не удалось автоматически подготовить аккаунт. Администратор проверит заказ вручную.",
            "refund_conflict": "⚠️ Возврат обнаружен после начала подготовки аккаунта. Заказ передан администратору на проверку.",
            "refunded": "ℹ️ Заказ отменён или возвращён.",
            "closed": "✅ Заказ завершён.",
        },
        "locale": "ru",
        "validate_lots_before_save": True,
    }


def _load_funpay_settings() -> dict[str, Any]:
    try:
        with open(_funpay_path(), encoding="utf-8") as fp:
            data = json.load(fp)
        if not isinstance(data, dict):
            raise ValueError("funpay settings root must be an object")
        defaults = _default_funpay_settings()
        for key, value in defaults.items():
            data.setdefault(key, value)
        if not isinstance(data.get("order_messages"), dict):
            data["order_messages"] = dict(defaults["order_messages"])
        else:
            for key, value in defaults["order_messages"].items():
                data["order_messages"].setdefault(key, value)
        return data
    except FileNotFoundError:
        data = _default_funpay_settings()
        _save_funpay_settings(data)
        return data
    except Exception as exc:
        logger.warning("LZT-FP: failed to load FunPay settings: %s", exc)
        return _default_funpay_settings()


def _save_funpay_settings(data: dict[str, Any]) -> None:
    with _lock:
        _atomic_json_save(_funpay_path(), data)


def _load_accounts() -> dict[str, Any]:
    try:
        with open(_accounts_path(), encoding="utf-8") as fp:
            data = json.load(fp)
        if not isinstance(data, dict):
            raise ValueError("accounts root must be an object")
        data.setdefault("version", 1)
        data.setdefault("accounts", {})
        return data
    except FileNotFoundError:
        data = {"version": 1, "accounts": {}}
        _save_accounts(data)
        return data
    except Exception as exc:
        logger.warning("LZT-FP: failed to load account state: %s", exc)
        return {"version": 1, "accounts": {}}


def _save_accounts(data: dict[str, Any]) -> None:
    with _lock:
        _atomic_json_save(_accounts_path(), data)


def _load_json_state(path: str, default: dict[str, Any]) -> dict[str, Any]:
    try:
        with open(path, encoding="utf-8") as fp:
            data = json.load(fp)
        if not isinstance(data, dict):
            raise ValueError("state root must be an object")
        return data
    except FileNotFoundError:
        _atomic_json_save(path, default)
        return dict(default)
    except Exception as exc:
        logger.warning("LZT-FP: failed to load state file %s: %s", os.path.basename(path), exc)
        return dict(default)


def _load_purchases() -> dict[str, Any]:
    data = _load_json_state(_purchases_path(), {"version": 1, "operations": {}})
    data.setdefault("version", 1)
    data.setdefault("operations", {})
    return data


def _save_purchases(data: dict[str, Any]) -> None:
    with _lock:
        _atomic_json_save(_purchases_path(), data)


def _load_credentials() -> dict[str, Any]:
    data = _load_json_state(_credentials_path(), {"version": 1, "accounts": {}})
    data.setdefault("version", 1)
    data.setdefault("accounts", {})
    return data


def _save_credentials(data: dict[str, Any]) -> None:
    with _lock:
        _atomic_json_save(_credentials_path(), data)


def _load_orders() -> dict[str, Any]:
    data = _load_json_state(_orders_path(), {"version": 1, "orders": {}})
    data.setdefault("version", 1)
    data.setdefault("orders", {})
    return data


def _save_orders(data: dict[str, Any]) -> None:
    with _lock:
        _atomic_json_save(_orders_path(), data)


def _masked_token() -> str:
    token = SETTINGS.api_token
    if not token:
        return "не задан"
    if len(token) <= 8:
        return "*" * len(token)
    return f"{token[:4]}...{token[-4:]}"


def _masked_proxy() -> str:
    return "задан" if SETTINGS.proxy else "не задан"


def _safe_api_detail(payload: Any, raw_text: str = "") -> str:
    """Extract a short, non-secret diagnostic from an LZT error response."""
    values: list[str] = []
    if isinstance(payload, dict):
        errors = payload.get("errors")
        if isinstance(errors, list):
            values.extend(str(value) for value in errors)
        elif errors not in (None, ""):
            values.append(str(errors))
        for key in ("error", "message", "detail"):
            value = payload.get(key)
            if value not in (None, ""):
                values.append(str(value))
    if not values and raw_text:
        values.append(raw_text)
    detail = " | ".join(values)
    detail = re.sub(r"(?i)Bearer\s+\S+", "Bearer [REDACTED]", detail)
    detail = re.sub(
        r"(?i)(password|token|secret|encodedraw|encodedpassword|encodedoldpassword)\s*[:=]\s*[^,;\s}]+",
        r"\1=[REDACTED]",
        detail,
    )
    detail = " ".join(detail.split())
    return detail[:500]


class LZTAPIError(RuntimeError):
    def __init__(self, status_code: int, message: str, *, detail: str = "", path: str = ""):
        self.status_code = status_code
        self.detail = detail[:500]
        self.path = path
        super().__init__(message)


def _exception_detail(exc: Exception) -> str:
    if isinstance(exc, LZTAPIError):
        return exc.detail or str(exc)
    if isinstance(exc, ValueError):
        detail = " ".join(str(exc).split())
        return detail[:300] if detail else type(exc).__name__
    return type(exc).__name__


def _wait_before_request(search: bool) -> None:
    global _last_request_at
    required_delay = max(3.0 if search else 0.0, SETTINGS.min_request_delay_seconds)
    with _request_lock:
        wait = required_delay - (time.monotonic() - _last_request_at)
        if wait > 0:
            time.sleep(wait)
        _last_request_at = time.monotonic()


def _query_pairs(filters: dict[str, Any]) -> list[tuple[str, str]]:
    pairs: list[tuple[str, str]] = []
    for raw_key, value in filters.items():
        key = "game[]" if raw_key == "game" else raw_key
        if value is None or value == "" or (value is False and key not in {"no_vac", "no_trans"}):
            continue
        if isinstance(value, dict):
            for nested_key, nested_value in value.items():
                pairs.append((f"{key}[{nested_key}]", str(nested_value)))
        elif isinstance(value, (list, tuple, set)):
            for item in value:
                pairs.append((key if key.endswith("[]") else f"{key}[]", str(item)))
        elif isinstance(value, bool):
            pairs.append((key, "1" if value else "0"))
        else:
            pairs.append((key, str(value)))
    return pairs


def _lzt_request(path: str, *, method: str = "GET",
                 params: list[tuple[str, str]] | None = None,
                 json_body: dict[str, Any] | None = None,
                 search: bool = False) -> dict[str, Any]:
    if not SETTINGS.api_token:
        raise LZTAPIError(0, "LZT API-токен не задан")
    headers = {"Authorization": f"Bearer {SETTINGS.api_token}", "Accept-Language": SETTINGS.language}
    session = requests.Session()
    if SETTINGS.proxy:
        session.proxies.update({"http": SETTINGS.proxy, "https": SETTINGS.proxy})
    try:
        retry_cap = 100 if path.endswith((
            "/fast-buy", "/check-account", "/email-code", "/letters",
        )) else 3
        for attempt in range(retry_cap):
            _wait_before_request(search)
            try:
                response = session.request(
                    method.upper(), f"{LZT_BASE_URL}{path}", headers=headers,
                    params=params, json=json_body, timeout=SETTINGS.timeout_seconds,
                )
            except requests.RequestException as exc:
                raise LZTAPIError(
                    0,
                    f"LZT API network error: {type(exc).__name__}",
                    detail=type(exc).__name__,
                    path=path,
                ) from exc
            logger.info(
                "LZT-FP: %s %s status=%s remaining=%s attempt=%s",
                method.upper(), path, response.status_code,
                response.headers.get("X-RateLimit-Remaining", "?"), attempt + 1,
            )
            if response.status_code == 429 and attempt < retry_cap - 1:
                retry_after = _float(response.headers.get("Retry-After"), 3.0, minimum=0.0)
                time.sleep(min(60.0, max(3.0, retry_after)))
                continue
            try:
                payload = response.json()
            except ValueError:
                payload = {"raw": response.text[:500]}
            retry_requested = isinstance(payload, dict) and "retry_request" in str(payload).lower()
            if retry_requested and attempt < retry_cap - 1:
                logger.warning(
                    "LZT-FP: %s %s requested retry (%s/%s)",
                    method.upper(), path, attempt + 1, retry_cap,
                )
                time.sleep(min(5.0, max(0.5, _float(
                    response.headers.get("Retry-After"), 1.0, minimum=0.0
                ))))
                continue
            if not response.ok:
                detail = _safe_api_detail(payload, response.text)
                suffix = f": {detail[:300]}" if detail else ""
                raise LZTAPIError(
                    response.status_code,
                    f"LZT API HTTP {response.status_code}{suffix}",
                    detail=detail,
                    path=path,
                )
            if not isinstance(payload, dict):
                raise LZTAPIError(
                    response.status_code,
                    "LZT API вернул неожиданный формат",
                    path=path,
                )
            return payload
    finally:
        session.close()
    raise LZTAPIError(429, "LZT API: превышен лимит запросов", path=path)


class SteamGuard:
    """Local Steam Guard primitives for maFiles returned by LZT."""

    SYMBOLS = "23456789BCDFGHJKMNPQRTVWXY"
    _time_offset = 0
    _last_sync = 0.0

    @classmethod
    def sync_time(cls) -> int:
        try:
            response = requests.post(
                "https://api.steampowered.com/ITwoFactorService/QueryTime/v0001",
                timeout=10,
            )
            if response.ok:
                server_time = int(response.json()["response"]["server_time"])
                cls._time_offset = server_time - int(time.time())
                cls._last_sync = time.time()
        except Exception as exc:
            logger.warning("LZT-FP: Steam time sync failed: %s", exc)
        return cls._time_offset

    @classmethod
    def code_from_shared_secret(cls, shared_secret: str) -> str:
        if not shared_secret:
            raise ValueError("maFile не содержит shared_secret")
        if time.time() - cls._last_sync > 300:
            cls.sync_time()
        encoded = shared_secret + "=" * (-len(shared_secret) % 4)
        secret = base64.b64decode(encoded)
        timestamp = int((time.time() + cls._time_offset) / 30)
        digest = hmac.new(secret, struct.pack(">Q", timestamp), hashlib.sha1).digest()
        offset = digest[19] & 0x0F
        value = struct.unpack(">I", digest[offset:offset + 4])[0] & 0x7FFFFFFF
        code = []
        for _ in range(5):
            code.append(cls.SYMBOLS[value % len(cls.SYMBOLS)])
            value //= len(cls.SYMBOLS)
        return "".join(code)

    @classmethod
    def confirmation_key(cls, identity_secret: str, tag: str, timestamp: int | None = None) -> str:
        if not identity_secret:
            raise ValueError("maFile не содержит identity_secret")
        encoded = identity_secret + "=" * (-len(identity_secret) % 4)
        stamp = int(timestamp or (time.time() + cls._time_offset))
        digest = hmac.new(
            base64.b64decode(encoded), struct.pack(">Q", stamp) + tag.encode(), hashlib.sha1
        ).digest()
        return base64.b64encode(digest).decode()


class LZTAccountOperations:
    """LZT operations for catalog candidates and owned Market items."""

    @staticmethod
    def get_item(item_id: int | str) -> dict[str, Any]:
        return _lzt_request(f"/{_require_item_id(item_id)}")

    @staticmethod
    def check_account(item_id: int | str) -> dict[str, Any]:
        return _lzt_request(f"/{_require_item_id(item_id)}/check-account", method="POST", json_body={})

    @staticmethod
    def fast_buy(item_id: int | str, price: float | int | None = None,
                 balance_id: int | None = None) -> dict[str, Any]:
        body: dict[str, Any] = {}
        if price is not None:
            body["price"] = price
        if balance_id:
            body["balance_id"] = int(balance_id)
        return _lzt_request(f"/{_require_item_id(item_id)}/fast-buy", method="POST", json_body=body)

    @staticmethod
    def confirm_buy(item_id: int | str, price: float | int,
                    balance_id: int | None = None) -> dict[str, Any]:
        body: dict[str, Any] = {"price": price}
        if balance_id:
            body["balance_id"] = int(balance_id)
        return _lzt_request(f"/{_require_item_id(item_id)}/confirm-buy", method="POST", json_body=body)

    @staticmethod
    def list_balances() -> dict[str, Any]:
        return _lzt_request("/balance/exchange")

    @staticmethod
    def get_purchase_balance() -> tuple[int, float]:
        """Return the configured/selected account balance used by FastBuy."""
        global _last_lzt_balance
        payload = LZTAccountOperations.list_balances()
        raw_balances = payload.get("to", {}) if isinstance(payload, dict) else {}
        if not isinstance(raw_balances, dict):
            raise ValueError("LZT не вернул список балансов")

        entries: list[tuple[int, float, dict[str, Any]]] = []
        for key, value in raw_balances.items():
            if not isinstance(value, dict) or value.get("type") != "account":
                continue
            try:
                balance_id = int(value.get("balance_id", key))
                amount = float(str(value.get("balance", "0")).replace(",", "."))
            except (TypeError, ValueError):
                continue
            if balance_id > 0:
                entries.append((balance_id, max(0.0, amount), value))

        selected: tuple[int, float, dict[str, Any]] | None = None
        if SETTINGS.balance_id:
            selected = next((entry for entry in entries if entry[0] == SETTINGS.balance_id), None)
            if selected is None:
                raise ValueError(f"баланс LZT {SETTINGS.balance_id} не найден")
        elif entries:
            selected = max(entries, key=lambda entry: entry[1])
        if selected is None:
            raise ValueError("баланс для покупки аккаунтов LZT не найден")

        balance_id, amount, details = selected
        _last_lzt_balance = {
            "balance_id": balance_id,
            "amount": amount,
            "title": str(details.get("title") or details.get("custom_title") or ""),
            "checked_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        }
        logger.info("LZT-FP: purchase balance checked balance_id=%s amount=%.2f", balance_id, amount)
        return balance_id, amount

    @staticmethod
    def resolve_balance_id() -> int | None:
        """Resolve the first positive account balance unless one is configured."""
        try:
            balance_id, _amount = LZTAccountOperations.get_purchase_balance()
        except Exception as exc:
            logger.warning("LZT-FP: could not resolve purchase balance: %s", type(exc).__name__)
            return None
        logger.info("LZT-FP: selected purchase balance_id=%s", balance_id)
        return balance_id

    @staticmethod
    def get_guard_code(item_id: int | str) -> dict[str, Any]:
        return _lzt_request(f"/{_require_item_id(item_id)}/guard-code")

    @staticmethod
    def list_sda_confirmations(item_id: int | str) -> dict[str, Any]:
        return _lzt_request(
            f"/{_require_item_id(item_id)}/confirm-sda", method="POST", json_body={}
        )

    @staticmethod
    def confirm_sda(item_id: int | str, confirmation_id: int | str,
                   nonce: int | str) -> dict[str, Any]:
        return _lzt_request(
            f"/{_require_item_id(item_id)}/confirm-sda", method="POST",
            params=[("id", str(int(confirmation_id))), ("nonce", str(int(nonce)))],
        )

    @staticmethod
    def get_email_code(item_id: int | str) -> dict[str, Any]:
        return _lzt_request(f"/{_require_item_id(item_id)}/email-code")

    @staticmethod
    def get_letters(item_id: int | str, limit: int = 20) -> dict[str, Any]:
        return _lzt_request(
            f"/{_require_item_id(item_id)}/letters",
            params=[("limit", str(min(50, max(10, int(limit)))))]
        )

    @staticmethod
    def get_mafile(item_id: int | str) -> dict[str, Any]:
        # LZT explicitly cancels the active guarantee for this operation.
        logger.warning("LZT-FP: maFile requested for item=%s; guarantee may be cancelled", item_id)
        return _lzt_request(f"/{_require_item_id(item_id)}/mafile")

    @staticmethod
    def refuse_guarantee(item_id: int | str) -> dict[str, Any]:
        """Explicitly refuse LZT's guarantee before requesting resale data."""
        logger.warning("LZT-FP: refusing guarantee for item=%s before full access preparation", item_id)
        return _lzt_request(f"/{_require_item_id(item_id)}/refuse-guarantee", method="POST", json_body={})

    @staticmethod
    def get_temp_email_password(item_id: int | str) -> dict[str, Any]:
        logger.warning("LZT-FP: temporary email password requested for item=%s; guarantee cancelled", item_id)
        return _lzt_request(f"/{_require_item_id(item_id)}/temp-email-password")

    @staticmethod
    def remove_mafile(item_id: int | str) -> dict[str, Any]:
        logger.warning("LZT-FP: maFile removal requested for item=%s; authenticator will be unlinked", item_id)
        return _lzt_request(f"/{_require_item_id(item_id)}/mafile", method="DELETE")


def _require_item_id(value: int | str) -> int:
    item_id = _item_id({"item_id": value})
    if not item_id:
        raise ValueError("item_id должен быть положительным числом")
    return int(item_id)


def _credential_fields(data: Any, prefix: str) -> dict[str, str]:
    if not isinstance(data, dict):
        return {}
    result: dict[str, str] = {}
    mapping = {
        "login": "login",
        "password": "password",
        "oldPassword": "old_password",
    }
    for source, target in mapping.items():
        value = data.get(source)
        if value not in (None, ""):
            result[f"{prefix}_{target}"] = str(value)
    return result


_BACKUP_EMAIL_LABEL_RE = re.compile(
    r"(?i)(?:данные\s+от\s+резервн(?:ой|ую)\s+почт(?:ы|у)|"
    r"(?:backup|recovery|reserve|secondary)\s+email(?:\s+credentials?)?)"
    r"\s*[:=-]\s*([^\s:<>]+)\s*:\s*([^\s<>]+)"
)
_BACKUP_EMAIL_KEY_ALIASES = {
    "backupemail", "backupemaildata", "backupmail", "backupmaildata",
    "recoveryemail", "recoveryemaildata", "recoverymail", "recoverymaildata",
    "reserveemail", "reserveemaildata", "reserveemailaddress",
    "secondaryemail", "secondaryemaildata", "additionalemail", "additionalemaildata",
}
_BACKUP_EMAIL_LOGIN_KEYS = {
    "backupemaillogin", "backupemailaddress", "backupemailusername",
    "recoveryemaillogin", "recoveryemailaddress", "recoveryemailusername",
    "reserveemaillogin", "reserveemailaddress", "secondaryemaillogin",
    "secondaryemailaddress", "additionalemaillogin", "additionalemailaddress",
}
_BACKUP_EMAIL_PASSWORD_KEYS = {
    "backupemailpassword", "backupmailpassword", "recoveryemailpassword",
    "recoverymailpassword", "reserveemailpassword", "secondaryemailpassword",
    "additionalemailpassword",
}


def _normalized_key(value: Any) -> str:
    return re.sub(r"[^a-z0-9]", "", str(value).casefold())


def _credential_pair(value: Any) -> tuple[str, str]:
    if isinstance(value, dict):
        login = _find_nested_value(
            value, {"login", "email", "address", "username", "user", "mail"}
        )
        password = _find_nested_value(value, {"password", "pass", "passwd"})
        if login not in (None, "") and password not in (None, ""):
            return str(login).strip(), str(password).strip()
    elif isinstance(value, str):
        match = re.fullmatch(r"\s*([^\s:<>]+)\s*:\s*([^\s<>]+)\s*", value)
        if match and "@" in match.group(1):
            return match.group(1).strip(), match.group(2).strip()
    return "", ""


def _extract_backup_email_credentials(payload: Any) -> dict[str, str]:
    """Extract optional recovery-mail credentials without retaining raw blobs."""
    structured_login = ""
    structured_password = ""
    labelled_pair: tuple[str, str] = ("", "")

    def visit(value: Any) -> None:
        nonlocal structured_login, structured_password, labelled_pair
        if isinstance(value, dict):
            for key, child in value.items():
                normalized = _normalized_key(key)
                if normalized in _BACKUP_EMAIL_LOGIN_KEYS and child not in (None, ""):
                    structured_login = str(child).strip()
                elif normalized in _BACKUP_EMAIL_PASSWORD_KEYS and child not in (None, ""):
                    structured_password = str(child).strip()
                elif normalized in _BACKUP_EMAIL_KEY_ALIASES:
                    login, password = _credential_pair(child)
                    if login and password:
                        structured_login, structured_password = login, password
                visit(child)
        elif isinstance(value, list):
            for child in value:
                visit(child)
        elif isinstance(value, str) and not labelled_pair[0]:
            match = _BACKUP_EMAIL_LABEL_RE.search(value)
            if match:
                labelled_pair = (match.group(1).strip(), match.group(2).strip())

    visit(payload)
    login, password = (structured_login, structured_password)
    if not (login and password):
        login, password = labelled_pair
    if not (login and password and "@" in login):
        return {}
    return {
        "backup_email_login": login,
        "backup_email_password": password,
    }


def _find_nested_value(payload: Any, keys: set[str]) -> Any:
    """Find a value in known LZT response wrappers without exposing it in logs."""
    normalized_keys = {str(key).casefold() for key in keys}
    if isinstance(payload, dict):
        for key, value in payload.items():
            if str(key).casefold() in normalized_keys and value not in (None, "", [], {}):
                return value
        for value in payload.values():
            found = _find_nested_value(value, normalized_keys)
            if found not in (None, "", [], {}):
                return found
    elif isinstance(payload, list):
        for value in payload:
            found = _find_nested_value(value, normalized_keys)
            if found not in (None, "", [], {}):
                return found
    return None


def _extract_temp_email_password(payload: Any) -> str:
    """Handle both documented and wrapped temp-email-password responses."""
    password = _find_nested_value(
        payload,
        {"password", "email_password", "emailPassword", "account_password"},
    )
    if isinstance(password, (str, int, float)) and str(password):
        return str(password)
    account = _find_nested_value(payload, {"account"})
    if isinstance(account, (str, int, float)) and str(account):
        return str(account)
    if isinstance(account, (dict, list)):
        password = _find_nested_value(
            account,
            {"password", "email_password", "emailPassword", "account_password", "account"},
        )
        if isinstance(password, (str, int, float)) and str(password):
            return str(password)
    return ""


def _extract_mafile(payload: Any) -> dict[str, Any] | None:
    """Handle root and wrapped maFile responses from the Market API."""
    mafile = _find_nested_value(payload, {"maFile", "ma_file", "mafile"})
    return mafile if isinstance(mafile, dict) and mafile else None


def _store_purchased_credentials(item_id: str, payload: dict[str, Any],
                                 preset_key: str = "") -> dict[str, Any]:
    """Persist only the credential fields needed by future delivery logic.

    LZT returns several duplicate/raw/encoded forms. Raw and encoded blobs are
    deliberately discarded; credentials are kept in a separate 0600 file.
    """
    item = payload.get("item", payload) if isinstance(payload, dict) else {}
    item = item if isinstance(item, dict) else {}
    credentials: dict[str, Any] = {
        "item_id": int(item_id),
        "stored_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "preset_key": preset_key,
        "email_login_url": str(item.get("emailLoginUrl") or ""),
    }
    account_fields = _credential_fields(item.get("loginData"), "account")
    credentials.update(account_fields)
    # Keep the old names for Steam/Dota records and expose one generic pair
    # for Riot accounts, whose login is not a Steam login.
    credentials.update({
        "steam_login": account_fields.get("account_login", ""),
        "steam_password": account_fields.get("account_password", ""),
    })
    credentials.update(_credential_fields(item.get("emailLoginData"), "email"))
    credentials.update(_extract_backup_email_credentials(payload))
    temp_email = item.get("temp_email")
    if temp_email not in (None, ""):
        credentials["temp_email"] = str(temp_email)
    credentials = {key: value for key, value in credentials.items() if value not in (None, "")}
    stored_data = _load_credentials()
    stored = stored_data.get("accounts", {}).get(str(item_id), {})
    if isinstance(stored, dict):
        # GET /item may hide fields that were exposed by the purchase response
        # or by the guarantee-cancelling post-purchase requests.
        merged_credentials = dict(stored)
        merged_credentials.update(credentials)
        credentials = merged_credentials
    if not credentials.get("account_login") or not credentials.get("account_password"):
        raise ValueError("LZT не вернул логин и пароль аккаунта после покупки")
    stored_data.setdefault("accounts", {})[str(item_id)] = credentials
    _save_credentials(stored_data)
    return {
        "has_account_login": bool(credentials.get("account_login")),
        "has_account_password": bool(credentials.get("account_password")),
        "has_steam_login": bool(credentials.get("steam_login")),
        "has_steam_password": bool(credentials.get("steam_password")),
        "has_email_login": bool(credentials.get("email_login")),
        "has_email_password": bool(credentials.get("email_password")),
        "has_email_login_url": bool(credentials.get("email_login_url")),
        "has_backup_email_login": bool(credentials.get("backup_email_login")),
        "has_backup_email_password": bool(credentials.get("backup_email_password")),
        "has_mafile": bool(credentials.get("mafile") or item.get("steam_mfa") or item.get("has_mafile")),
    }


def _update_stored_credentials(item_id: str, updates: dict[str, Any]) -> dict[str, Any]:
    """Merge post-purchase LZT data without replacing already saved secrets."""
    data = _load_credentials()
    credentials = data.setdefault("accounts", {}).setdefault(str(item_id), {"item_id": int(item_id)})
    if not isinstance(credentials, dict):
        credentials = {"item_id": int(item_id)}
        data["accounts"][str(item_id)] = credentials
    for key, value in updates.items():
        if value not in (None, "", {}, []):
            credentials[key] = value
    credentials["stored_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    _save_credentials(data)
    return credentials


def _credential_summary(credentials: dict[str, Any], item: dict[str, Any] | None = None) -> dict[str, Any]:
    item = item if isinstance(item, dict) else {}
    return {
        "has_account_login": bool(credentials.get("account_login") or credentials.get("steam_login")),
        "has_account_password": bool(credentials.get("account_password") or credentials.get("steam_password")),
        "has_steam_login": bool(credentials.get("steam_login")),
        "has_steam_password": bool(credentials.get("steam_password")),
        "has_email_login": bool(credentials.get("email_login")),
        "has_email_password": bool(credentials.get("email_password")),
        "has_email_login_url": bool(credentials.get("email_login_url")),
        "has_backup_email_login": bool(credentials.get("backup_email_login")),
        "has_backup_email_password": bool(credentials.get("backup_email_password")),
        "has_mafile": bool(credentials.get("mafile") or item.get("steam_mfa") or item.get("has_mafile")),
    }


def _account_credentials_ready(credentials: dict[str, Any]) -> bool:
    return bool(
        (credentials.get("account_login") or credentials.get("steam_login"))
        and (credentials.get("account_password") or credentials.get("steam_password"))
    )


def _prepare_full_access(item_id: str, purchased: dict[str, Any], preset_key: str = "") -> dict[str, Any]:
    """Cancel the guarantee and collect the credentials needed for delivery.

    Some accounts expose mailbox credentials only after the guarantee is
    cancelled. The same flow is used for Dota and Riot accounts; Riot accounts
    do not require Steam Guard or a maFile.
    """
    item = purchased.get("item", purchased) if isinstance(purchased, dict) else {}
    item = item if isinstance(item, dict) else {}
    _store_purchased_credentials(item_id, purchased, preset_key)
    credentials = _credentials_for_item(item_id)

    # Keep the explicit refusal separate from the data requests. This mirrors
    # the browser flow and also unlocks endpoints that reject guaranteed items.
    try:
        LZTAccountOperations.refuse_guarantee(item_id)
    except LZTAPIError as exc:
        # The item may already have had its guarantee cancelled by a previous
        # attempt. The data requests below remain the source of truth.
        logger.warning(
            "LZT-FP: explicit guarantee refusal failed item=%s status=%s; continuing",
            item_id, exc.status_code,
        )

    temp_email = str(credentials.get("temp_email") or item.get("temp_email") or credentials.get("email_login") or "")
    email_expected = bool(
        temp_email
        or item.get("emailLoginUrl")
        or item.get("canViewTempEmail")
        or item.get("canViewEmailLoginData")
    )
    email_optional = _is_valorant_preset_key(preset_key)
    if email_expected and not credentials.get("email_password"):
        try:
            email_payload = LZTAccountOperations.get_temp_email_password(item_id)
            email_password = _extract_temp_email_password(email_payload)
            if not email_password:
                raise ValueError(
                    "LZT вернул ответ без пароля временной почты после отказа от гарантии"
                )
            updates = {"email_login": temp_email, "email_password": str(email_password)}
            _update_stored_credentials(item_id, updates)
            credentials = _credentials_for_item(item_id)
        except Exception as exc:
            if not email_optional:
                raise
            logger.warning(
                "LZT-FP: optional email credentials unavailable item=%s error=%s; continuing with account login",
                item_id, _exception_detail(exc),
            )
    elif email_expected and temp_email and not credentials.get("email_login"):
        _update_stored_credentials(item_id, {"email_login": temp_email})
        credentials = _credentials_for_item(item_id)

    preset = _load_presets().get(preset_key, {}) if preset_key else {}
    preset_filters = preset.get("filters", {}) if isinstance(preset, dict) else {}
    mafile_expected = bool(
        item.get("steam_mfa")
        or item.get("has_mafile")
        or (isinstance(preset_filters, dict) and preset_filters.get("mafile") == "yes")
    )
    if mafile_expected and not credentials.get("mafile"):
        mafile_payload = LZTAccountOperations.get_mafile(item_id)
        mafile = _extract_mafile(mafile_payload)
        if mafile is None:
            raise ValueError("LZT не вернул maFile после отказа от гарантии")
        _update_stored_credentials(item_id, {"mafile": mafile})
        credentials = _credentials_for_item(item_id)

    summary = _credential_summary(credentials, item)
    if email_expected and not (summary["has_email_login"] and summary["has_email_password"]):
        if not email_optional:
            raise ValueError("полный доступ к временной почте не получен")
        logger.warning(
            "LZT-FP: continuing without optional email credentials item=%s",
            item_id,
        )
    if not summary["has_account_login"] or not summary["has_account_password"]:
        raise ValueError("полный доступ к логину и паролю аккаунта не получен")
    if mafile_expected and not summary["has_mafile"]:
        raise ValueError("полный доступ к maFile не получен")
    logger.info(
        "LZT-FP: full access prepared item=%s email=%s mafile=%s",
        item_id, summary["has_email_login"] and summary["has_email_password"], summary["has_mafile"],
    )
    return summary


def _purchase_error_details(exc: Exception, *, order_id: str = "") -> dict[str, Any]:
    details: dict[str, Any] = {
        "error_type": type(exc).__name__,
        "error_detail": _exception_detail(exc),
    }
    if order_id:
        details["order_id"] = str(order_id)
    if isinstance(exc, LZTAPIError):
        details["api_status"] = exc.status_code
        if exc.path:
            details["api_path"] = exc.path
    return details


def _record_purchase(item_id: str, *, status: str, price: Any = None,
                     preset_key: str = "", details: dict[str, Any] | None = None) -> None:
    data = _load_purchases()
    operations = data.setdefault("operations", {})
    record = operations.setdefault(item_id, {"item_id": int(item_id)})
    record.update({
        "item_id": int(item_id),
        "status": status,
        "updated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    })
    if price is not None:
        record["price"] = price
    if preset_key:
        record["preset_key"] = preset_key
    if details:
        record.update(details)
    _save_purchases(data)


def _mark_account_purchased(item_id: str, *, preset_key: str = "",
                            capabilities: dict[str, Any] | None = None) -> None:
    data = _load_accounts()
    accounts = data.setdefault("accounts", {})
    record = accounts.setdefault(item_id, {"item_id": int(item_id)})
    record.update({
        "item_id": int(item_id),
        "status": "purchased",
        "purchased_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "preset_key": preset_key,
    })
    if capabilities:
        record["capabilities"] = capabilities
    _save_accounts(data)


def _order_message(kind: str, locale: str = "ru") -> str:
    data = _load_funpay_settings()
    messages = data.get("order_messages", {})
    defaults = {
        "waiting": "⏳ Заказ получен. Аккаунт готовится к передаче.",
        "ready": "✅ Аккаунт готов к выдаче. Используйте команду !help для доступных действий.",
        "failed": "❌ Не удалось автоматически подготовить аккаунт. Администратор проверит заказ вручную.",
        "refund_conflict": "⚠️ Возврат обнаружен после начала подготовки аккаунта. Заказ передан администратору на проверку.",
        "refunded": "ℹ️ Заказ отменён или возвращён.",
        "closed": "✅ Заказ завершён.",
    }
    value = messages.get(kind) if isinstance(messages, dict) else None
    return str(value or defaults.get(kind, ""))


def _send_order_message(order_id: str, kind: str) -> bool:
    """Send a lifecycle message and persist its message id for delivery audit."""
    if not _cardinal:
        return False
    record = _load_orders().get("orders", {}).get(str(order_id), {})
    if not isinstance(record, dict) or not record.get("chat_id"):
        return False
    result = _cardinal.send_message(record["chat_id"], _order_message(kind))
    if not result:
        return False
    message_ids = [
        int(getattr(message, "id", 0) or 0)
        for message in result
        if int(getattr(message, "id", 0) or 0) > 0
    ]
    updates: dict[str, Any] = {}
    if message_ids:
        updates["last_bot_message_id"] = max(message_ids)
        if kind == "waiting" and not record.get("delivery_audit_start_message_id"):
            updates["delivery_audit_start_message_id"] = min(message_ids)
    if updates:
        try:
            _update_order_record(order_id, **updates)
        except Exception:
            logger.exception(
                "LZT-FP: could not persist lifecycle message audit order=%s kind=%s",
                order_id, kind,
            )
    return True


def _is_lzt_account_validation_failure(exc: Exception) -> bool:
    """Return true only for LZT's explicit account-check rejection response."""
    if not isinstance(exc, LZTAPIError) or not 400 <= exc.status_code < 500:
        return False
    if not exc.path.endswith("/fast-buy"):
        return False
    detail = _exception_detail(exc).casefold()
    return any(all(marker in detail for marker in markers)
               for markers in LZT_ACCOUNT_VALIDATION_ERROR_MARKERS)


def _contains_account_data(payload: Any) -> bool:
    """Detect account secrets without logging or persisting the payload."""
    if isinstance(payload, str):
        return bool(_extract_backup_email_credentials(payload))
    if isinstance(payload, dict):
        sensitive_keys = {
            "logindata", "emaillogindata", "mafile", "ma_file",
            "password", "account_password", "steam_password", "email_password",
            "encodedpassword", "encodedoldpassword", "encodedraw", "oldpassword",
            "login", "account_login", "steam_login", "email_login",
            "backup_email_login", "backup_email_password", "backupemail",
            "backupemaildata", "recoveryemail", "recoveryemaildata",
        }
        normalized_sensitive_keys = {_normalized_key(key) for key in sensitive_keys}
        for key, value in payload.items():
            if _normalized_key(key) in normalized_sensitive_keys and value not in (None, "", {}, []):
                return True
            if _contains_account_data(value):
                return True
    elif isinstance(payload, list):
        return any(_contains_account_data(value) for value in payload)
    return False


def _stored_account_data_exists(item_id: str) -> bool:
    credentials = _credentials_for_item(item_id)
    if any(value not in (None, "", {}, []) for key, value in credentials.items()
           if key not in {"item_id", "stored_at", "preset_key"}):
        return True
    account = _load_accounts().get("accounts", {}).get(str(item_id))
    return isinstance(account, dict) and (
        str(account.get("status") or "").casefold() == "purchased"
        or bool(account.get("purchased_at"))
    )


def _chat_delivery_audit_is_clean(record: dict[str, Any]) -> tuple[bool, str]:
    """Reject refunds when chat history cannot prove that no data was sent."""
    if not _cardinal or not _cardinal.account:
        return False, "FunPay API не инициализирован"
    start_id = _int(record.get("delivery_audit_start_message_id"), 0)
    if start_id <= 0:
        return False, "нет контрольного ID сообщения начала заказа"
    chat_id = str(record.get("chat_id") or "")
    if not chat_id:
        return False, "у заказа нет chat_id"
    try:
        history = _cardinal.account.get_chat_history(
            chat_id,
            interlocutor_username=str(record.get("buyer") or "") or None,
        )
    except Exception as exc:
        return False, f"не удалось проверить историю чата: {type(exc).__name__}"
    if not history:
        return False, "история чата пуста или недоступна"

    allowed_messages = {
        _order_message(kind).casefold().strip()
        for kind in ("waiting", "failed", "ready", "refund_conflict", "refunded", "closed")
    }
    seller_id = int(_cardinal.account.id)
    for message in history:
        message_id = _int(getattr(message, "id", 0), 0)
        if message_id < start_id or int(getattr(message, "author_id", 0) or 0) != seller_id:
            continue
        text = str(getattr(message, "text", "") or "").casefold().strip()
        if not text:
            return False, "после принятия заказа найдено сообщение продавца без текста"
        if any(marker in text for marker in DELIVERY_DATA_MARKERS):
            return False, "в истории найдено сообщение продавца с признаками данных аккаунта"
        if text not in allowed_messages and not any(
            allowed and text.endswith(allowed) for allowed in allowed_messages
        ):
            return False, "в истории найдено неизвестное сообщение продавца"
    return True, ""


def _auto_refund_safety_check(order_id: str, item_id: str) -> tuple[bool, str]:
    """Require independent local, FunPay, LZT, and chat evidence before refund."""
    record = _load_orders().get("orders", {}).get(str(order_id))
    if not isinstance(record, dict) or str(record.get("item_id") or "") != str(item_id):
        return False, "заказ не найден или не привязан к item"
    operation = _load_purchases().get("operations", {}).get(str(item_id), {})
    if not isinstance(operation, dict) or operation.get("status") != "purchase_failed":
        return False, "состояние покупки не подтверждает детерминированный отказ"
    if operation.get("credentials_stored"):
        return False, "операция помечена как сохранившая credentials"
    if any(record.get(key) for key in (
        "credentials_stored", "delivery_attempted_at", "delivery_confirmed_at",
        "issued_at", "delivery_message_id",
    )):
        return False, "в заказе есть признак подготовки или выдачи"
    if _stored_account_data_exists(item_id):
        return False, "для item существуют сохранённые данные аккаунта"
    chat_clean, chat_reason = _chat_delivery_audit_is_clean(record)
    if not chat_clean:
        return False, chat_reason
    if not _cardinal or not _cardinal.account:
        return False, "FunPay API не инициализирован"
    try:
        order = _cardinal.account.get_order(str(order_id), include_details=False)
    except Exception as exc:
        return False, f"не удалось проверить статус заказа FunPay: {type(exc).__name__}"
    if getattr(order, "status", None) != OrderStatuses.PAID:
        return False, f"статус заказа FunPay изменился на {getattr(order, 'status', None)}"
    try:
        payload = LZTAccountOperations.get_item(item_id)
    except Exception as exc:
        return False, f"не удалось повторно проверить item LZT: {type(exc).__name__}"
    item = payload.get("item", payload) if isinstance(payload, dict) else {}
    if not isinstance(item, dict) or str(item.get("item_state") or "").casefold() not in {"active", "available"}:
        return False, "после отказа LZT item не подтверждён как активный"
    if _contains_account_data(payload):
        return False, "повторная карточка LZT содержит данные аккаунта"
    return True, ""


def _try_auto_refund_after_validation_failure(order_id: str, item_id: str,
                                              exc: Exception) -> bool:
    """Refund only after every no-delivery guard passes and refund is verified."""
    if not _is_lzt_account_validation_failure(exc):
        return False
    safe, reason = _auto_refund_safety_check(order_id, item_id)
    if not safe:
        logger.error(
            "LZT-FP: auto-refund blocked by no-delivery guard order=%s item=%s reason=%s",
            order_id, item_id, reason,
        )
        return False
    _update_order_record(
        order_id,
        status="auto_refund_pending",
        refund_reason=_exception_detail(exc),
        refund_guard_checked_at=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    )
    safe, reason = _auto_refund_safety_check(order_id, item_id)
    if not safe:
        logger.error(
            "LZT-FP: auto-refund recheck blocked order=%s item=%s reason=%s",
            order_id, item_id, reason,
        )
        return False
    try:
        _cardinal.account.refund(str(order_id))
    except Exception as exc_refund:
        logger.exception("LZT-FP: automatic FunPay refund failed order=%s", order_id)
        return False

    _update_order_record(
        order_id,
        status="refund_verification_pending",
        refund_requested_at=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    )
    for attempt in range(AUTO_REFUND_VERIFY_ATTEMPTS):
        try:
            current = _cardinal.account.get_order(str(order_id), include_details=False)
        except Exception:
            logger.exception(
                "LZT-FP: refund verification failed order=%s attempt=%s",
                order_id, attempt + 1,
            )
            break
        if getattr(current, "status", None) == OrderStatuses.REFUNDED:
            _update_catalog_item_status(item_id, "manual_review", order_id=order_id)
            _release_catalog_reservation(item_id, order_id)
            _update_order_record(
                order_id,
                status="refunded",
                auto_refunded=True,
                refunded_at=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            )
            if not _send_order_message(order_id, "refunded"):
                logger.error("LZT-FP: refund confirmed but notification failed order=%s", order_id)
            logger.warning(
                "LZT-FP: automatic refund completed after LZT account validation failure order=%s",
                order_id,
            )
            return True
        if getattr(current, "status", None) != OrderStatuses.PAID:
            break
        if attempt + 1 < AUTO_REFUND_VERIFY_ATTEMPTS:
            time.sleep(AUTO_REFUND_VERIFY_DELAY_SECONDS)

    logger.error(
        "LZT-FP: refund was requested but not confirmed order=%s; manual review required",
        order_id,
    )
    return False


def _configured_lot_ids() -> list[str]:
    result: list[str] = []
    for preset in _load_presets().values():
        config = preset.get("funpay", {}) if isinstance(preset, dict) else {}
        lot_ids = config.get("lot_ids", []) if isinstance(config, dict) else []
        if not isinstance(lot_ids, list):
            continue
        for raw_id in lot_ids:
            lot_id = str(_int(raw_id, 0))
            if lot_id != "0" and lot_id not in result:
                result.append(lot_id)
    return result


def _resolve_order_lot_id(order: Any) -> str | None:
    """Resolve a paid order to a configured lot without guessing ambiguously."""
    configured = _configured_lot_ids()
    text = " ".join(str(getattr(order, name, "") or "") for name in ("description", "html"))
    explicit = re.findall(r"(?:offer(?:=|/id=)|lot_id=)(\d+)", text)
    explicit_matches = [item for item in explicit if item in configured]
    if len(set(explicit_matches)) == 1:
        return explicit_matches[0]
    if len(set(explicit_matches)) > 1:
        return None

    subcategory = getattr(getattr(order, "subcategory", None), "id", None)
    if subcategory is not None and _cardinal and _cardinal.account:
        category_matches: list[str] = []
        for lot_id in configured:
            try:
                fields = _cardinal.account.get_lot_fields(int(lot_id))
                actual = getattr(getattr(fields, "subcategory", None), "id", None)
                title = str(getattr(fields, "title_ru", "") or "")
                description = str(getattr(fields, "description_ru", "") or "")
                order_text = str(getattr(order, "description", "") or "")
                if actual is not None and int(actual) != int(subcategory):
                    continue
                if title and title in order_text or description and description in order_text:
                    category_matches.append(lot_id)
            except Exception as exc:
                logger.warning("LZT-FP: order lot probe failed lot=%s: %s", lot_id, exc)
        if len(set(category_matches)) == 1:
            return category_matches[0]

    if len(configured) == 1:
        return configured[0]
    return None


def _catalog_record_for_lot(lot_id: str) -> dict[str, Any] | None:
    for record in _load_catalog().get("items", {}).values():
        if isinstance(record, dict) and str(record.get("funpay_lot_id") or "") == str(lot_id):
            return record
    return None


def _catalog_record_for_item(item_id: str) -> tuple[dict[str, Any] | None, str | None]:
    catalog = _load_catalog()
    items = catalog.get("items", {})
    if not isinstance(items, dict):
        return None, None
    for key, record in items.items():
        if not isinstance(record, dict):
            continue
        if _item_id(record.get("metadata", {})) == str(item_id):
            return record, str(key)
    return None, None


def _reserve_catalog_item(lot_id: str, item_id: str, order_id: str) -> str:
    """Atomically reserve a catalog candidate for one paid FunPay order."""
    with _lock:
        catalog = _load_catalog()
        items = catalog.get("items", {})
        if not isinstance(items, dict):
            raise ValueError("каталог кандидатов повреждён")
        for key, record in items.items():
            if not isinstance(record, dict):
                continue
            metadata = record.get("metadata", {})
            if _item_id(metadata) != str(item_id):
                continue
            bound_lot = str(record.get("funpay_lot_id") or "")
            if bound_lot != str(lot_id):
                raise ValueError(f"кандидат #{item_id} не привязан к лоту {lot_id}")
            reservation = record.get("reservation", {})
            existing_order = str(reservation.get("order_id") or "") if isinstance(reservation, dict) else ""
            if (
                record.get("status") not in {None, "candidate"}
                and existing_order != str(order_id)
            ):
                raise ValueError(f"кандидат #{item_id} заблокирован состоянием {record.get('status')}")
            preset_keys = record.get("preset_keys", [])
            preset_key = str(preset_keys[0]) if isinstance(preset_keys, list) and preset_keys else ""
            record["status"] = "reserved"
            record["reservation"] = {
                "order_id": str(order_id),
                "lot_id": str(lot_id),
                "reserved_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            }
            items[key] = record
            _save_catalog(catalog)
            return preset_key
    raise ValueError(f"кандидат #{item_id} не найден в каталоге")


def _update_catalog_item_status(item_id: str, status: str, *, order_id: str = "") -> None:
    with _lock:
        catalog = _load_catalog()
        items = catalog.get("items", {})
        if not isinstance(items, dict):
            return
        changed = False
        for record in items.values():
            if not isinstance(record, dict) or _item_id(record.get("metadata", {})) != str(item_id):
                continue
            record["status"] = status
            if order_id:
                record["sold_order_id"] = str(order_id)
            record["status_updated_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
            changed = True
        if changed:
            _save_catalog(catalog)


def _release_catalog_reservation(item_id: str, order_id: str) -> None:
    with _lock:
        catalog = _load_catalog()
        items = catalog.get("items", {})
        if not isinstance(items, dict):
            return
        changed = False
        for record in items.values():
            if not isinstance(record, dict) or _item_id(record.get("metadata", {})) != str(item_id):
                continue
            reservation = record.get("reservation", {})
            if not isinstance(reservation, dict) or str(reservation.get("order_id") or "") != str(order_id):
                continue
            record.pop("reservation", None)
            if record.get("status") == "reserved":
                record["status"] = "candidate"
            changed = True
        if changed:
            _save_catalog(catalog)


def _save_funpay_order(order: Any, lot_id: str, item_id: str | None,
                       *, status: str = "awaiting_purchase",
                       preset_key: str = "") -> dict[str, Any]:
    data = _load_orders()
    orders = data.setdefault("orders", {})
    order_id = str(getattr(order, "id", ""))
    existing = orders.get(order_id)
    if isinstance(existing, dict):
        return existing
    record = {
        "order_id": order_id,
        "lot_id": str(lot_id),
        "item_id": int(item_id) if item_id and str(item_id).isdigit() else None,
        "buyer_id": _int(getattr(order, "buyer_id", 0), 0),
        "buyer": str(getattr(order, "buyer_username", "") or ""),
        "chat_id": str(getattr(order, "chat_id", "") or ""),
        "price": getattr(order, "price", None),
        "currency": str(getattr(getattr(order, "currency", None), "name", getattr(order, "currency", ""))),
        "status": status,
        "preset_key": preset_key,
        "created_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "updated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    orders[order_id] = record
    _save_orders(data)
    return record


def _update_order_record(order_id: str, *, status: str | None = None,
                        **updates: Any) -> dict[str, Any] | None:
    data = _load_orders()
    record = data.get("orders", {}).get(str(order_id))
    if not isinstance(record, dict):
        return None
    if status is not None:
        record["status"] = status
    record.update(updates)
    record["updated_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    _save_orders(data)
    return record


def _order_is_still_paid(order_id: str) -> bool:
    if not _cardinal or not _cardinal.account:
        raise RuntimeError("FunPay API не инициализирован")
    current = _cardinal.account.get_order(str(order_id), include_details=False)
    return getattr(current, "status", None) == OrderStatuses.PAID


def _deactivate_funpay_lot(lot_id: str) -> None:
    """Close the sold pool slot before another buyer can receive it."""
    if not _cardinal or not _cardinal.account:
        raise RuntimeError("FunPay API не инициализирован")
    def prepare_fields(fields: Any) -> None:
        fields.amount = 0
        fields.active = False

    _save_funpay_lot_with_retry(int(lot_id), prepare_fields)


def _send_order_failure(order_id: str, item_id: str | None, detail: str,
                        *, block_item: bool = True) -> None:
    current = _load_orders().get("orders", {}).get(str(order_id), {})
    if isinstance(current, dict) and current.get("status") in {"refunded", "refund_conflict"}:
        logger.error("LZT-FP: keeping terminal refund state order=%s detail=%s", order_id, detail)
        return
    record = _update_order_record(order_id, status="manual_review", failure=detail)
    if item_id and block_item:
        _update_catalog_item_status(item_id, "manual_review", order_id=order_id)
    if record and not _send_order_message(order_id, "failed"):
        logger.error("LZT-FP: failed to notify order failure order=%s", order_id)
    logger.error("LZT-FP: automatic order processing requires manual review order=%s detail=%s", order_id, detail)


def _auto_purchase_worker(order_id: str, item_id: str, preset_key: str) -> None:
    """Buy, persist, and deliver one reserved LZT item for a paid order."""
    if not SETTINGS.auto_purchase_after_paid:
        return
    _purchase_lock.acquire()
    try:
        record = _load_orders().get("orders", {}).get(str(order_id))
        if not isinstance(record, dict) or record.get("status") != "awaiting_purchase":
            return
        if str(record.get("item_id") or "") != str(item_id):
            _send_order_failure(order_id, item_id, "заказ не содержит ожидаемый item_id")
            return
        try:
            if not _order_is_still_paid(order_id):
                _update_order_record(order_id, status="refunded")
                _release_catalog_reservation(item_id, order_id)
                return
        except Exception as exc:
            _send_order_failure(order_id, item_id, f"не удалось подтвердить оплату FunPay: {type(exc).__name__}")
            return

        credentials = _credentials_for_item(item_id)
        operation = _load_purchases().get("operations", {}).get(str(item_id), {})
        operation_status = operation.get("status") if isinstance(operation, dict) else None
        if operation_status in {
            "purchase_started", "purchase_response_received", "purchase_unknown",
            "full_access_failed",
        }:
            detail = (
                "предыдущая покупка завершилась, но полный доступ не был подготовлен"
                if operation_status == "full_access_failed"
                else "предыдущая покупка прервалась после списания или могла списать баланс"
            )
            _send_order_failure(order_id, item_id, detail)
            return
        if operation_status == "purchased" and _account_credentials_ready(credentials):
            try:
                prepared = _prepare_full_access(item_id, LZTAccountOperations.get_item(item_id), preset_key)
            except Exception as exc:
                _record_purchase(
                    item_id,
                    status="full_access_failed",
                    preset_key=preset_key,
                    details={"order_id": str(order_id), "full_access_error": _exception_detail(exc)},
                )
                _send_order_failure(order_id, item_id, f"не удалось получить полный доступ к аккаунту: {_exception_detail(exc)}")
                return
            _mark_account_purchased(item_id, preset_key=preset_key, capabilities=prepared)
            _record_purchase(
                item_id,
                status="purchased",
                preset_key=preset_key,
                details={"order_id": str(order_id), "full_access_prepared": True, "capabilities": prepared},
            )
            _update_order_record(order_id, status="ready")
            ok, detail = _deliver_order(item_id, order_id)
            if not ok:
                logger.error("LZT-FP: automatic delivery pending order=%s detail=%s", order_id, detail)
            return

        _update_order_record(order_id, status="purchase_checking")
        # FastBuy performs the actual validity check. GET is used only to read
        # the current state and price without consuming the check quota.
        checked = LZTAccountOperations.get_item(item_id)
        item = checked.get("item", checked) if isinstance(checked, dict) else {}
        item = item if isinstance(item, dict) else {}
        state = str(item.get("item_state") or "").lower()
        if state and state not in {"active", "available"}:
            _send_order_failure(order_id, item_id, f"аккаунт LZT недоступен: {state}")
            return
        raw_price = _item_field(item, "rub_price", "price", default=None)
        if raw_price in (None, ""):
            _send_order_failure(order_id, item_id, "LZT не вернул актуальную цену")
            return
        price = float(str(raw_price).replace(",", "."))
        paid_price = float(str(record.get("price") or 0).replace(",", "."))
        if paid_price > 0 and price > paid_price + 0.01:
            _send_order_failure(order_id, item_id, f"цена LZT {price:g} выше оплаты FunPay {paid_price:g}")
            return

        balance_id = LZTAccountOperations.resolve_balance_id()
        _record_purchase(
            item_id,
            status="purchase_started",
            price=price,
            preset_key=preset_key,
            details={"order_id": str(order_id), "checked_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())},
        )
        _update_order_record(order_id, status="purchase_started", lzt_price=price)
        try:
            # FastBuy is the official atomic flow: it validates the item and then buys it.
            purchased = LZTAccountOperations.fast_buy(item_id, price, balance_id)
        except Exception as exc:
            deterministic_failure = isinstance(exc, LZTAPIError) and 400 <= exc.status_code < 500
            validation_failure = _is_lzt_account_validation_failure(exc)
            _record_purchase(
                item_id,
                status="purchase_failed" if deterministic_failure else "purchase_unknown",
                price=price,
                preset_key=preset_key,
                details=_purchase_error_details(exc, order_id=order_id),
            )
            if validation_failure and _try_auto_refund_after_validation_failure(order_id, item_id, exc):
                return
            if deterministic_failure:
                if not validation_failure:
                    _release_catalog_reservation(item_id, order_id)
            _send_order_failure(
                order_id,
                item_id,
                "ошибка покупки через FastBuy; повторная автоматическая покупка запрещена: "
                f"{_exception_detail(exc)}",
                block_item=validation_failure or not deterministic_failure,
            )
            return

        _record_purchase(item_id, status="purchase_response_received", price=price, preset_key=preset_key,
                         details={"order_id": str(order_id)})
        try:
            capability_summary = _prepare_full_access(item_id, purchased, preset_key)
        except Exception as exc:
            _record_purchase(item_id, status="full_access_failed", price=price, preset_key=preset_key,
                             details={"order_id": str(order_id), "full_access_error": _exception_detail(exc)})
            _send_order_failure(order_id, item_id, f"аккаунт куплен, но полный доступ не получен: {_exception_detail(exc)}")
            return

        purchased_item = purchased.get("item", purchased) if isinstance(purchased, dict) else {}
        purchased_item = purchased_item if isinstance(purchased_item, dict) else {}
        _mark_account_purchased(item_id, preset_key=preset_key, capabilities=capability_summary)
        _record_purchase(
            item_id,
            status="purchased",
            price=price,
            preset_key=preset_key,
            details={
                "order_id": str(order_id),
                "lzt_status": str(purchased.get("status") or "ok"),
                "item_state": str(purchased_item.get("item_state") or ""),
                "credentials_stored": True,
                "capabilities": capability_summary,
            },
        )
        _update_catalog_item_status(item_id, "sold", order_id=order_id)
        try:
            _deactivate_funpay_lot(str(record.get("lot_id")))
        except Exception:
            logger.exception("LZT-FP: sold FunPay lot could not be deactivated order=%s", order_id)
        _safe_balance_check("after automatic purchase")

        try:
            if not _order_is_still_paid(order_id):
                _update_order_record(
                    order_id,
                    status="refund_after_purchase",
                    credentials_stored=True,
                )
                _update_catalog_item_status(item_id, "manual_review", order_id=order_id)
                if record.get("chat_id"):
                    _cardinal.send_message(record["chat_id"], _order_message("refund_conflict"))
                logger.error("LZT-FP: order was refunded before automatic delivery order=%s", order_id)
                return
        except Exception as exc:
            _send_order_failure(order_id, item_id, f"не удалось проверить оплату перед выдачей: {type(exc).__name__}")
            return

        _update_order_record(order_id, status="ready", credentials_stored=True)
        ok, detail = _deliver_order(item_id, order_id)
        if not ok:
            logger.error("LZT-FP: automatic delivery pending order=%s detail=%s", order_id, detail)
    except Exception as exc:
        logger.exception("LZT-FP: automatic purchase failed order=%s item=%s", order_id, item_id)
        operation = _load_purchases().get("operations", {}).get(str(item_id), {})
        if isinstance(operation, dict) and operation.get("status") in {"purchase_started", "purchase_response_received"}:
            _send_order_failure(order_id, item_id, "неопределённое состояние покупки; повтор запрещён")
        else:
            _send_order_failure(order_id, item_id, f"ошибка автоматической обработки: {type(exc).__name__}")
    finally:
        _purchase_lock.release()


def _orders_for_item(item_id: str, statuses: set[str] | None = None) -> list[dict[str, Any]]:
    result = []
    for record in _load_orders().get("orders", {}).values():
        if not isinstance(record, dict) or str(record.get("item_id") or "") != str(item_id):
            continue
        if statuses and record.get("status") not in statuses:
            continue
        result.append(record)
    return result


def _normalise_filters(raw: Any) -> dict[str, Any]:
    if not isinstance(raw, dict):
        raise ValueError("фильтры должны быть JSON-объектом")
    result = dict(raw)
    if "game" in result and "game[]" not in result:
        result["game[]"] = result.pop("game")
    if "game[]" in result and not isinstance(result["game[]"], list):
        result["game[]"] = [result["game[]"]]
    if isinstance(result.get("mafile"), bool):
        result["mafile"] = "yes" if result["mafile"] else "no"
    if result.get("mafile") not in {None, "yes", "no", "nomatter"}:
        raise ValueError("mafile должен быть yes, no или nomatter")
    return result


def _search_preset(preset: dict[str, Any], limit: int, *, verify_items: bool = False) -> tuple[list[dict[str, Any]], int, str]:
    filters = _normalise_filters(preset.get("filters", {}))
    filters.setdefault("order_by", "price")
    minimum_offline_days = max(0, _int(filters.get("daybreak"), 0))
    is_valorant = str(preset.get("category") or "").casefold() == "riot"
    results: list[dict[str, Any]] = []
    total = 0
    search_url = ""
    for page in range(1, SEARCH_MAX_PAGES + 1):
        page_filters = dict(filters)
        page_filters["page"] = page
        payload = _lzt_request(f"/{preset.get('category', 'steam')}", params=_query_pairs(page_filters), search=True)
        page_items = payload.get("items", [])
        if not isinstance(page_items, list):
            raise LZTAPIError(200, "LZT API вернул некорректный список товаров")
        if not verify_items:
            results.extend(item for item in page_items if isinstance(item, dict))
        else:
            for search_item in page_items:
                if not isinstance(search_item, dict):
                    continue
                item_key = _item_id(search_item)
                if not item_key:
                    continue
                if _purchase_state_blocks_catalog(item_key):
                    logger.info(
                        "LZT-FP: item=%s skipped during search because its purchase state is blocked",
                        item_key,
                    )
                    continue
                try:
                    detail = _detail_payload(_lzt_request(f"/{item_key}"))
                    if not _item_id(detail):
                        logger.warning("LZT-FP: item=%s returned no item_id; skipped", item_key)
                        continue
                    state = str(_item_field(detail, "item_state", default="")).lower()
                    if state and state != "active":
                        logger.info("LZT-FP: item=%s state=%s; skipped", item_key, state)
                        continue
                    if minimum_offline_days:
                        activity_fields = (
                            ("riot_last_activity", "account_last_activity")
                            if is_valorant else ("steam_last_activity",)
                        )
                        last_activity = _item_field(detail, *activity_fields, default=0)
                        try:
                            offline_days = (time.time() - float(last_activity)) / 86400
                        except (TypeError, ValueError):
                            offline_days = -1
                        if offline_days < minimum_offline_days:
                            logger.info(
                                "LZT-FP: item=%s last_activity_age=%.1f days; required=%s; skipped",
                                item_key, offline_days, minimum_offline_days,
                            )
                            continue
                    if filters.get("mafile") == "yes" and not bool(_item_field(detail, "steam_mfa", default=0)):
                        logger.info("LZT-FP: item=%s has no active steam_mfa; skipped", item_key)
                        continue
                    if filters.get("mafile") == "no" and bool(_item_field(detail, "steam_mfa", default=0)):
                        logger.info("LZT-FP: item=%s has steam_mfa; skipped", item_key)
                        continue
                    merged_item = dict(search_item)
                    merged_item.update(detail)
                    if is_valorant:
                        _enrich_valorant_metadata(merged_item)
                        if str(merged_item.get("valorant_rank_ru", "")).casefold() in {
                            "не указан", "без ранга", "unranked", "not specified",
                        }:
                            logger.info("LZT-FP: item=%s has no usable last Valorant rank; skipped", item_key)
                            continue
                    results.append(merged_item)
                except LZTAPIError as exc:
                    if exc.status_code in {404, 410}:
                        logger.info("LZT-FP: item=%s is no longer available; skipped", item_key)
                        continue
                    raise
        total = _int(payload.get("totalItems"), len(results))
        search_url = str(payload.get("searchUrl") or "")
        if len(results) >= limit or not payload.get("hasNextPage") or not page_items:
            break
    def price_key(item: dict[str, Any]) -> tuple[int, float, str]:
        raw_price = _item_field(item, "rub_price", "price", default=None)
        try:
            return (0, float(raw_price), str(_item_field(item, "item_id", default="")))
        except (TypeError, ValueError):
            return (1, 0.0, str(_item_field(item, "item_id", default="")))

    if is_valorant:
        for item in results:
            _enrich_valorant_metadata(item)
    results.sort(key=price_key)
    return results[:limit], total, search_url


def _item_field(item: dict[str, Any], *keys: str, default: Any = "") -> Any:
    for key in keys:
        value = item.get(key)
        if value is not None and value != "":
            return value
    return default


def _item_id(item: dict[str, Any]) -> str:
    value = _item_field(item, "item_id", "id", default="")
    value = str(value).strip()
    return value if value.isdigit() else ""


def _format_timestamp(value: Any) -> str:
    try:
        timestamp = int(float(value))
    except (TypeError, ValueError):
        return "не указана"
    if timestamp <= 0:
        return "не указана"
    return time.strftime("%d.%m.%Y %H:%M UTC", time.gmtime(timestamp))


def _detail_payload(payload: dict[str, Any]) -> dict[str, Any]:
    for key in ("item", "data"):
        value = payload.get(key)
        if isinstance(value, dict) and (_item_id(value) or "title" in value):
            return value
    return payload


def _valorant_rank_pair(value: Any) -> tuple[str, str]:
    raw = " ".join(str(value or "").strip().split())
    if not raw:
        return "Не указан", "Not specified"
    base, separator, number = raw.rpartition(" ")
    if separator and number.isdigit():
        suffix = f" {number}"
    else:
        base, suffix = raw, ""
    key = base.casefold()
    if key in VALORANT_RANK_TRANSLATIONS_RU_EN:
        en = VALORANT_RANK_TRANSLATIONS_RU_EN[key]
        ru = base.capitalize()
    elif key in VALORANT_RANK_TRANSLATIONS_EN_RU:
        ru = VALORANT_RANK_TRANSLATIONS_EN_RU[key]
        en = base
    else:
        return raw, raw
    return ru + suffix, en + suffix


def _valorant_agent_names(item: dict[str, Any]) -> list[str]:
    inventory = item.get("valorantInventory")
    if not isinstance(inventory, dict):
        return []
    raw_agents = inventory.get("Agent", inventory.get("agent", []))
    if not isinstance(raw_agents, list):
        return []
    names: list[str] = []
    for entry in raw_agents:
        if isinstance(entry, dict):
            name = entry.get("displayName") or entry.get("name") or entry.get("title")
            if name:
                names.append(str(name))
            continue
        agent_id = str(entry or "").strip().casefold()
        if not agent_id:
            continue
        names.append(VALORANT_AGENT_NAMES.get(agent_id, f"Agent {str(entry)[:8]}"))
    return names


def _valorant_skin_ids(item: dict[str, Any]) -> list[str]:
    inventory = item.get("valorantInventory")
    if not isinstance(inventory, dict):
        return []
    raw_skins = inventory.get("WeaponSkins", inventory.get("weaponSkins", []))
    if not isinstance(raw_skins, list):
        return []
    result: list[str] = []
    for entry in raw_skins:
        if isinstance(entry, dict):
            value = entry.get("uuid") or entry.get("id") or entry.get("skinId")
        else:
            value = entry
        value = str(value or "").strip()
        if value:
            result.append(value)
    return result


def _load_valorant_skin_names(language: str) -> dict[str, str]:
    if language in _valorant_skin_names_loaded:
        return _valorant_skin_names.get(language, {})
    with _valorant_skin_names_lock:
        if language in _valorant_skin_names_loaded:
            return _valorant_skin_names.get(language, {})
        try:
            session = requests.Session()
            if SETTINGS.proxy:
                session.proxies.update({"http": SETTINGS.proxy, "https": SETTINGS.proxy})
            response = session.get(
                VALORANT_SKIN_CATALOG_URL,
                params={"language": language},
                timeout=min(30.0, max(5.0, SETTINGS.timeout_seconds)),
            )
            response.raise_for_status()
            payload = response.json()
            names = {
                str(entry.get("uuid")): str(entry.get("displayName"))
                for entry in payload.get("data", [])
                if isinstance(entry, dict) and entry.get("uuid") and entry.get("displayName")
            }
            _valorant_skin_names[language] = names
            logger.info("LZT-FP: loaded Valorant skin names language=%s count=%s", language, len(names))
        except Exception as exc:
            logger.warning("LZT-FP: Valorant skin names unavailable language=%s error=%s", language, type(exc).__name__)
            _valorant_skin_names[language] = {}
        _valorant_skin_names_loaded.add(language)
        return _valorant_skin_names[language]


def _valorant_skin_name_pairs(item: dict[str, Any], skin_ids: list[str]) -> tuple[list[str], list[str]]:
    existing_ru = item.get("valorant_skin_names_ru")
    existing_en = item.get("valorant_skin_names_en")
    ru_map = _load_valorant_skin_names("ru-RU")
    en_map = _load_valorant_skin_names("en-US")
    names_ru = [
        str(existing_ru[index]) if isinstance(existing_ru, list) and index < len(existing_ru) and existing_ru[index]
        else ru_map.get(skin_id) or en_map.get(skin_id) or skin_id
        for index, skin_id in enumerate(skin_ids)
    ]
    names_en = [
        str(existing_en[index]) if isinstance(existing_en, list) and index < len(existing_en) and existing_en[index]
        else en_map.get(skin_id) or ru_map.get(skin_id) or skin_id
        for index, skin_id in enumerate(skin_ids)
    ]
    return names_ru, names_en


def _enrich_valorant_metadata(item: dict[str, Any]) -> dict[str, Any]:
    """Normalize Riot/Valorant fields used by FunPay templates and forms."""
    region = str(_item_field(item, "riot_valorant_region", "valorant_region", default="EU") or "EU").strip().upper()
    rank_raw = _item_field(item, "valorantLastRankTitle", "riot_valorant_last_rank_title", default="")
    rank_ru, rank_en = _valorant_rank_pair(rank_raw)
    agents = _valorant_agent_names(item)
    if agents:
        agent_count = len(agents)
    else:
        agent_count = _int(_item_field(item, "riot_valorant_agent_count", "valorant_agent_count", default=0), 0)
    level = _int(_item_field(item, "riot_valorant_level", "valorant_level", default=0), 0)
    skin_ids = _valorant_skin_ids(item)
    skin_count = _int(
        _item_field(item, "riot_valorant_skin_count", "valorant_skin_count", default=len(skin_ids)),
        len(skin_ids),
    )
    if skin_ids:
        skin_count = max(skin_count, len(skin_ids))
    if skin_ids:
        skin_names_ru, skin_names_en = _valorant_skin_name_pairs(item, skin_ids)
    else:
        skin_names_ru = item.get("valorant_skin_names_ru") if isinstance(item.get("valorant_skin_names_ru"), list) else []
        skin_names_en = item.get("valorant_skin_names_en") if isinstance(item.get("valorant_skin_names_en"), list) else []
    item["valorant_region"] = region
    item["valorant_server_id"] = VALORANT_SERVER_IDS.get(region, region)
    item["valorant_rank_ru"] = rank_ru
    item["valorant_rank_en"] = rank_en
    item["valorant_agent_count"] = agent_count
    item["valorant_agents"] = agents
    item["valorant_agents_text"] = ", ".join(agents) if agents else "не указаны"
    item["valorant_level"] = level
    item["valorant_skin_ids"] = skin_ids
    item["valorant_skin_count"] = skin_count
    item["valorant_skin_names_ru"] = skin_names_ru
    item["valorant_skin_names_en"] = skin_names_en
    item["valorant_skins_ru_text"] = ", ".join(skin_names_ru) if skin_names_ru else "не указаны"
    item["valorant_skins_en_text"] = ", ".join(skin_names_en) if skin_names_en else "not specified"
    item["valorant_top_skin_ru"] = skin_names_ru[0] if skin_names_ru else "не указан"
    item["valorant_top_skin_en"] = skin_names_en[0] if skin_names_en else "not specified"
    return item


def _purchase_state_blocks_catalog(item_id: str) -> bool:
    operation = _load_purchases().get("operations", {}).get(str(item_id), {})
    if not isinstance(operation, dict):
        return False
    return operation.get("status") in {
        "purchase_started",
        "purchase_response_received",
        "purchase_unknown",
        "purchased",
    }


def _is_riot_preset(preset: Any) -> bool:
    return isinstance(preset, dict) and str(preset.get("category") or "").casefold() == "riot"


def _enforce_valorant_catalog_exclusivity(
    catalog: dict[str, Any], presets: dict[str, dict[str, Any]]
) -> bool:
    changed = False
    for record in catalog.get("items", {}).values():
        if not isinstance(record, dict) or not isinstance(record.get("preset_keys"), list):
            continue
        riot_keys = [
            str(key) for key in record["preset_keys"]
            if _is_riot_preset(presets.get(str(key)))
        ]
        if len(riot_keys) <= 1:
            continue
        owner = "valorant" if "valorant" in riot_keys else sorted(riot_keys)[0]
        retained = [
            key for key in record["preset_keys"]
            if not _is_riot_preset(presets.get(str(key))) or str(key) == owner
        ]
        if retained != record["preset_keys"]:
            record["preset_keys"] = retained
            record["preset_names"] = sorted(
                str(presets.get(str(key), {}).get("name", key)) for key in retained
            )
            changed = True
            logger.warning(
                "LZT-FP: removed overlapping Valorant preset ownership item=%s owner=%s",
                record.get("item_id"), owner,
            )
    return changed


def _catalog_has_other_riot_owner(
    catalog: dict[str, Any], item_id: str, preset_key: str,
    presets: dict[str, dict[str, Any]],
) -> str:
    for record in catalog.get("items", {}).values():
        if not isinstance(record, dict) or str(record.get("item_id") or "") != str(item_id):
            continue
        for owner_key in record.get("preset_keys", []):
            owner_key = str(owner_key)
            if owner_key != preset_key and _is_riot_preset(presets.get(owner_key)):
                return owner_key
    return ""


def _replace_preset_catalog(catalog: dict[str, Any], preset_key: str,
                            preset: dict[str, Any], items: list[dict[str, Any]],
                            presets: dict[str, dict[str, Any]] | None = None) -> None:
    presets = presets or _load_presets()
    catalog_items = catalog.setdefault("items", {})
    previous_for_preset: dict[str, dict[str, Any]] = {}
    for item_key in list(catalog_items):
        record = catalog_items[item_key]
        if not isinstance(record, dict):
            del catalog_items[item_key]
            continue
        preset_keys = set(record.get("preset_keys", []))
        if preset_key not in preset_keys:
            continue
        previous_for_preset[str(item_key)] = dict(record)
        preset_keys.discard(preset_key)
        if preset_keys:
            record["preset_keys"] = sorted(preset_keys)
        else:
            del catalog_items[item_key]

    fetched_at = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    for item in items:
        item_key = _item_id(item)
        if not item_key:
            logger.warning("LZT-FP: skipping catalog item without numeric item_id")
            continue
        if _purchase_state_blocks_catalog(item_key):
            logger.warning(
                "LZT-FP: item=%s excluded from catalog because its purchase state is unresolved or completed",
                item_key,
            )
            continue
        previous = previous_for_preset.get(item_key) or catalog_items.get(item_key)
        if _is_riot_preset(preset):
            owner = _catalog_has_other_riot_owner(catalog, item_key, preset_key, presets)
            if owner:
                logger.info(
                    "LZT-FP: item=%s kept only in Valorant preset=%s; skipped preset=%s",
                    item_key, owner, preset_key,
                )
                continue
            preset_keys = {preset_key}
            preset_names = {str(preset.get("name", preset_key))}
        else:
            preset_keys = set(previous.get("preset_keys", [])) if isinstance(previous, dict) else set()
            preset_names = set(previous.get("preset_names", [])) if isinstance(previous, dict) else set()
            preset_keys.add(preset_key)
        preset_names.add(str(preset.get("name", preset_key)))
        record = {
            "item_id": int(item_key),
            "preset_keys": sorted(preset_keys),
            "preset_names": sorted(preset_names),
            "markup_percent": _preset_markup(preset),
            "fetched_at": fetched_at,
            "status": "candidate",
            "metadata": item,
        }
        if isinstance(previous, dict):
            for binding_key in (
                "funpay_lot_id", "lot_sync_at", "lot_sync_status", "balance_blocked",
                "balance_blocked_at", "balance_reactivated_at", "balance_checked_at",
                "balance_amount", "buyer_price", "internal_price", "lot_payload_hash",
                "lot_sync_active", "lot_sync_amount",
            ):
                if binding_key in previous:
                    record[binding_key] = previous[binding_key]
        catalog_items[item_key] = record


def _refresh_catalog(preset_keys: list[str]) -> tuple[int, int]:
    presets = _load_presets()
    catalog = _load_catalog()
    if _enforce_valorant_catalog_exclusivity(catalog, presets):
        _save_catalog(catalog)
    total_selected = 0
    total_metadata = 0
    run_started = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    catalog["last_run"] = {
        "started_at": run_started,
        "status": "running",
        "preset_keys": preset_keys,
    }
    _save_catalog(catalog)
    try:
        for preset_key in preset_keys:
            preset = presets.get(preset_key)
            if not isinstance(preset, dict) or not preset.get("enabled", True):
                continue
            verified_items, _, _ = _search_preset(
                preset, _preset_limit(preset), verify_items=True
            )
            total_metadata += len(verified_items)
            _replace_preset_catalog(catalog, preset_key, preset, verified_items, presets)
            total_selected += len(verified_items)
            catalog["updated_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
            _save_catalog(catalog)
        catalog["last_run"] = {
            "started_at": run_started,
            "finished_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "status": "success",
            "preset_keys": preset_keys,
            "selected": total_selected,
            "metadata_loaded": total_metadata,
        }
        _save_catalog(catalog)
        return total_selected, total_metadata
    except Exception:
        catalog["last_run"] = {
            "started_at": run_started,
            "finished_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "status": "failed",
            "preset_keys": preset_keys,
            "selected": total_selected,
            "metadata_loaded": total_metadata,
        }
        _save_catalog(catalog)
        raise


def _preset_limit(preset: dict[str, Any]) -> int:
    return min(200, max(1, _int(preset.get("selection_limit"), 10)))


def _preset_markup(preset: dict[str, Any]) -> float:
    return _float(preset.get("markup_percent"), 25.0, minimum=0.0)


def _format_candidate(item: dict[str, Any], markup_percent: float = 25.0) -> str:
    item_id = _item_field(item, "item_id", default="?")
    price = _item_field(item, "rub_price", "price", default="?")
    games = _item_field(item, "steam_dota2_game_count", default="?")
    wins = _item_field(item, "steam_dota2_win_count", default="?")
    behavior = _item_field(item, "steam_dota2_behavior", default="?")
    mmr = _item_field(item, "steam_dota2_solo_mmr", default="не указан")
    last_match = _format_timestamp(_item_field(item, "steam_dota2_last_match_date", default=0))
    last_activity = _format_timestamp(_item_field(item, "steam_last_activity", default=0))
    hours = _item_field(item, "steam_full_games", default={})
    dota_hours = "?"
    try:
        dota_hours = hours.get("list", {}).get("570", {}).get("playtime_forever", "?")
    except AttributeError:
        pass
    title = html.escape(str(_item_field(item, "title", default="Без названия")))
    try:
        markup_price = round(float(price) * (1.0 + markup_percent / 100.0), 2)
    except (TypeError, ValueError):
        markup_price = "?"
    if "valorantInventory" in item or "riot_valorant_level" in item:
        _enrich_valorant_metadata(item)
        return (
            f"<b>#{html.escape(str(item_id))}</b> · {html.escape(str(price))} ₽ → "
            f"<code>{markup_price}</code> ₽\n"
            f"Ранг: <code>{html.escape(str(item.get('valorant_rank_ru', 'Не указан')))}</code> · "
            f"Уровень: <code>{html.escape(str(item.get('valorant_level', 0)))}</code> · "
            f"Регион: <code>{html.escape(str(item.get('valorant_region', '')))}</code>\n"
            f"Агенты ({html.escape(str(item.get('valorant_agent_count', 0)))}): "
            f"<code>{html.escape(str(item.get('valorant_agents_text', 'не указаны')))}</code>\n"
            f"Скины ({html.escape(str(item.get('valorant_skin_count', 0)))}): "
            f"<code>{html.escape(str(item.get('valorant_skins_ru_text', 'не указаны')))}</code>\n{title}"
        )
    return (
        f"<b>#{html.escape(str(item_id))}</b> · {html.escape(str(price))} ₽ → "
        f"<code>{markup_price}</code> ₽\n"
        f"MMR: <code>{html.escape(str(mmr))}</code> · Порядочность: <code>{html.escape(str(behavior))}</code>\n"
        f"Матчей: <code>{html.escape(str(games))}</code> · Побед: <code>{html.escape(str(wins))}</code> · "
        f"Часов: <code>{html.escape(str(dota_hours))}</code>\n"
        f"Последняя игра Dota 2: <code>{html.escape(last_match)}</code>\n"
        f"Последний вход: <code>{html.escape(last_activity)}</code>\n{title}"
    )


class CBT:
    ROOT = f"{GLOBAL_CBT.PLUGIN_SETTINGS}:{UUID}"
    MAIN = "lztfp_main"
    SETTINGS = "lztfp_settings"
    PRESETS = "lztfp_presets"
    PRESET = "lztfp_preset"
    PREVIEW = "lztfp_preview"
    CATALOG = "lztfp_catalog"
    REFRESH = "lztfp_refresh"
    EDIT = "lztfp_edit"
    AUTO_PURCHASE = "lztfp_auto_purchase"
    FINANCE = "lztfp_finance"
    LOT_TEMPLATE = "lztfp_lot_template"
    LOT_TEMPLATE_FIELD = "lztfp_lot_template_field"
    LOT_TEMPLATE_JSON = "lztfp_lot_template_json"
    LOT_IDS = "lztfp_lot_ids"
    LOT_VALIDATE = "lztfp_lot_validate"
    LOT_SYNC = "lztfp_lot_sync"
    SELLING = "lztfp_selling"
    FUNPAY = "lztfp_funpay"
    FUNPAY_TEMPLATE_FIELD = "lztfp_funpay_template_field"
    FUNPAY_TEMPLATE_JSON = "lztfp_funpay_template_json"
    DEBUG = "lztfp_debug"
    DEBUG_ITEM = "lztfp_debug_item"
    DEBUG_CODE = "lztfp_debug_code"
    DEBUG_CONFIRMATIONS = "lztfp_debug_confirmations"
    DEBUG_EMAIL_CODE = "lztfp_debug_email_code"
    DEBUG_LETTERS = "lztfp_debug_letters"
    DEBUG_CONFIRM = "lztfp_debug_confirm"
    DEBUG_DANGEROUS = "lztfp_debug_dangerous"
    DEBUG_DANGEROUS_CONFIRM = "lztfp_debug_dangerous_confirm"
    PURCHASE_CHECK = "lztfp_purchase_check"
    PURCHASE_CONFIRM = "lztfp_purchase_confirm"
    DELIVERY = "lztfp_delivery"
    DELIVERY_CONFIRM = "lztfp_delivery_confirm"


def _back(callback: str):
    return K().add(B("⬅️ Назад", callback_data=callback))


def _edit(call, text: str, markup) -> None:
    try:
        _cardinal.telegram.bot.edit_message_text(text, call.message.chat.id, call.message.id, reply_markup=markup)
    except Exception:
        _cardinal.telegram.bot.send_message(call.message.chat.id, text, reply_markup=markup)


def _main_text() -> str:
    catalog = _load_catalog()
    catalog_items = catalog.get("items", {})
    purchases = _load_purchases().get("operations", {})
    return (
        f"<b>🔁 LZT → FunPay Resale v{VERSION}</b>\n\n"
        "Каталог, заполнение привязанных FunPay-лотов и автоматическая покупка с выдачей тестируются в полном цикле.\n\n"
        f"Пресетов: <code>{len(_load_presets())}</code> · В каталоге: <code>{len(catalog_items) if isinstance(catalog_items, dict) else 0}</code> лотов\n"
        f"Покупок: <code>{len(purchases) if isinstance(purchases, dict) else 0}</code>\n"
        f"API-токен: <code>{'задан' if SETTINGS.api_token else 'не задан'}</code>"
    )


def _main_keyboard():
    kb = K(row_width=2)
    kb.add(B("⚙️ Общие настройки", callback_data=CBT.SETTINGS))
    kb.add(B("🗂 Категории продаж", callback_data=CBT.PRESETS))
    kb.add(B("🎯 FunPay", callback_data=CBT.FUNPAY))
    kb.add(B("🛠 Отладка", callback_data=CBT.DEBUG))
    kb.add(B("⬅️ В меню плагинов", callback_data=f"{GLOBAL_CBT.EDIT_PLUGIN}:{UUID}:0"))
    return kb


def _settings_text() -> str:
    balance_text = "не проверен"
    if _last_lzt_balance:
        balance_text = (
            f"{float(_last_lzt_balance.get('amount', 0)):g} ₽ "
            f"(баланс {_last_lzt_balance.get('balance_id')}, {_last_lzt_balance.get('checked_at')})"
        )
    return (
        "<b>⚙️ Общие настройки</b>\n\n"
        f"Токен: <code>{html.escape(_masked_token())}</code>\n"
        f"Язык API: <code>{html.escape(SETTINGS.language)}</code>\n"
        f"Прокси: <code>{html.escape(_masked_proxy())}</code>\n"
        f"Таймаут: <code>{SETTINGS.timeout_seconds:g} с</code>\n"
        f"Мин. задержка запросов: <code>{SETTINGS.min_request_delay_seconds:g} с</code>\n\n"
        f"Баланс LZT для покупки: <code>{SETTINGS.balance_id or 'по умолчанию'}</code>\n\n"
        f"Последняя проверка средств: <code>{html.escape(balance_text)}</code>\n\n"
        f"Автопокупка после оплаты: <code>{'включена' if SETTINGS.auto_purchase_after_paid else 'выключена'}</code>\n\n"
        "Автоматическая покупка выполняется только для лота, заранее связанного с конкретным кандидатом каталога."
    )


def _settings_keyboard():
    kb = K(row_width=2)
    kb.add(B("🔑 API-токен", callback_data=f"{CBT.EDIT}:token"))
    kb.add(B("🌐 Язык", callback_data=f"{CBT.EDIT}:language"))
    kb.add(B("🛡 Прокси", callback_data=f"{CBT.EDIT}:proxy"))
    kb.add(B("⏱ Таймаут", callback_data=f"{CBT.EDIT}:timeout"))
    kb.add(B("⏳ Задержка запросов", callback_data=f"{CBT.EDIT}:delay"))
    kb.add(B("💳 Баланс для покупки", callback_data=f"{CBT.EDIT}:balance_id"))
    kb.add(B(
        f"{'⛔ Выключить' if SETTINGS.auto_purchase_after_paid else '✅ Включить'} автопокупку",
        callback_data=CBT.AUTO_PURCHASE,
    ))
    kb.add(B("⬅️ Назад", callback_data=CBT.MAIN))
    return kb


def _toggle_auto_purchase(call) -> None:
    SETTINGS.auto_purchase_after_paid = not SETTINGS.auto_purchase_after_paid
    _save_settings()
    _edit(call, _settings_text(), _settings_keyboard())
    _cardinal.telegram.bot.answer_callback_query(
        call.id,
        "Автопокупка включена" if SETTINGS.auto_purchase_after_paid else "Автопокупка выключена",
    )


def _presets_keyboard():
    kb = K(row_width=1)
    for key, preset in _load_presets().items():
        kb.add(B(str(preset.get("name", key)), callback_data=f"{CBT.PRESET}:{key}"))
    kb.add(B("📚 Каталог кандидатов", callback_data=CBT.CATALOG))
    kb.add(B("⬅️ Назад", callback_data=CBT.MAIN))
    return kb


def _preset_text(key: str) -> str:
    preset = _load_presets().get(key)
    if not preset:
        return "Пресет не найден."
    filters = json.dumps(preset.get("filters", {}), ensure_ascii=False, indent=2)
    if len(filters) > 2800:
        filters = filters[:2800] + "\n..."
    funpay = preset.get("funpay", {})
    lot_ids = _preset_lot_ids(preset)
    lot_ids_text = ", ".join(str(lot_id) for lot_id in lot_ids) or "не заданы"
    return (
        f"<b>🔎 Пресет: {html.escape(str(preset.get('name', key)))}</b>\n\n"
        f"Категория: <code>{html.escape(str(preset.get('category', 'steam')))}</code>\n"
        f"Статус: <code>{'включён' if preset.get('enabled', True) else 'выключен'}</code>\n"
        f"Продажа: <code>{'включена' if preset.get('selling_enabled', True) else 'выключена'}</code>\n"
        f"Количество кандидатов: <code>{_preset_limit(preset)}</code>\n"
        f"Наценка: <code>{_preset_markup(preset):g}%</code>\n"
        f"FunPay подкатегория: <code>{html.escape(str(funpay.get('subcategory_id') or 'не задана'))}</code>\n"
        f"Пул лотов ({len(lot_ids)}): <code>{html.escape(lot_ids_text)}</code>\n\n"
        "Фильтры LZT:\n<pre>" + html.escape(filters) + "</pre>"
    )


def _preset_keyboard(key: str):
    kb = K(row_width=1)
    preset = _load_presets().get(key, {})
    kb.add(B(
        "⛔ Отключить продажу" if preset.get("selling_enabled", True) else "✅ Включить продажу",
        callback_data=f"{CBT.SELLING}:{key}",
    ))
    kb.add(B("📊 Предпросмотр", callback_data=f"{CBT.PREVIEW}:{key}"))
    kb.add(B("💾 Обновить каталог", callback_data=f"{CBT.REFRESH}:{key}"))
    kb.add(B("✏️ Изменить JSON фильтров", callback_data=f"{CBT.PRESET}:edit:{key}"))
    kb.add(B("💰 Финансы", callback_data=f"{CBT.FINANCE}:{key}"))
    kb.add(B("🔢 Количество кандидатов", callback_data=f"{CBT.FINANCE}:limit:{key}"))
    kb.add(B("🧩 Шаблоны лотов", callback_data=f"{CBT.LOT_TEMPLATE}:{key}"))
    kb.add(B("🆔 Управление ID лотов", callback_data=f"{CBT.LOT_IDS}:{key}"))
    kb.add(B("🔍 Проверить пул FunPay", callback_data=f"{CBT.LOT_VALIDATE}:{key}"))
    kb.add(B("🚀 Заполнить пул FunPay", callback_data=f"{CBT.LOT_SYNC}:{key}"))
    kb.add(B("⬅️ К пресетам", callback_data=CBT.PRESETS))
    return kb


def _toggle_preset_selling(call) -> None:
    key = call.data.split(":", 1)[1]
    presets = _load_presets()
    preset = presets.get(key)
    if not isinstance(preset, dict):
        _cardinal.telegram.bot.answer_callback_query(call.id, "Пресет не найден", show_alert=True)
        return
    preset["selling_enabled"] = not preset.get("selling_enabled", True)
    _save_presets(presets)
    state = "включена" if preset["selling_enabled"] else "выключена"
    _edit(call, _preset_text(key), _preset_keyboard(key))
    _cardinal.telegram.bot.answer_callback_query(call.id, f"Продажа {state}")
    threading.Thread(
        target=_reconcile_presets,
        args=([key],),
        daemon=True,
        name="lztfp-selling-toggle",
    ).start()


LOT_TEMPLATE_FIELDS = (
    ("summary_ru", "Название / краткое описание RU"),
    ("summary_en", "Название / краткое описание EN"),
    ("description_ru", "Подробное описание RU"),
    ("description_en", "Подробное описание EN"),
    ("payment_msg_ru", "Сообщение после оплаты RU"),
    ("payment_msg_en", "Сообщение после оплаты EN"),
)


def _template_value(template: Any, field: str) -> str:
    if not isinstance(template, dict):
        return ""
    return str(template.get(field) or "")


def _template_preview(template: Any, *, inherited: dict[str, Any] | None = None,
                      limit: int = 900) -> str:
    """Render a compact, escaped template preview for Telegram menus."""
    template = template if isinstance(template, dict) else {}
    inherited = inherited if isinstance(inherited, dict) else {}
    lines: list[str] = []
    for field, label in LOT_TEMPLATE_FIELDS:
        value = _template_value(template, field)
        source = ""
        if not value and field in inherited:
            value = _template_value(inherited, field)
            source = " · универсальный"
        if not value:
            value = "(не задано)"
        value = value.replace("\n", " ")
        if len(value) > 130:
            value = value[:127] + "..."
        lines.append(f"{label}: <code>{html.escape(value)}</code>{source}")
    result = "\n".join(lines)
    return result[:limit]


def _effective_template(preset: dict[str, Any] | None = None) -> dict[str, Any]:
    global_template = _load_funpay_settings().get("default_template", {})
    result = dict(global_template) if isinstance(global_template, dict) else {}
    if isinstance(preset, dict):
        config = preset.get("funpay", {})
        local_template = config.get("templates", {}) if isinstance(config, dict) else {}
        if isinstance(local_template, dict):
            result.update(local_template)
    return result


def _template_is_ready(template: dict[str, Any]) -> tuple[bool, str]:
    missing = [
        label for field, label in LOT_TEMPLATE_FIELDS
        if field in {"description_ru", "description_en"} and not _template_value(template, field).strip()
    ]
    if missing:
        return False, "Не заполнены обязательные поля: " + ", ".join(missing)
    return True, ""


def _preset_lot_template_text(key: str) -> str:
    preset = _load_presets().get(key)
    if not isinstance(preset, dict):
        return "Пресет не найден."
    config = preset.get("funpay", {})
    local = config.get("templates", {}) if isinstance(config, dict) else {}
    local = local if isinstance(local, dict) else {}
    universal = _load_funpay_settings().get("default_template", {})
    effective = _effective_template(preset)
    ready, warning = _template_is_ready(effective)
    text = (
        f"<b>🧩 Шаблоны лотов: {html.escape(str(preset.get('name', key)))}</b>\n\n"
        "Поля ниже переопределяют универсальный шаблон только для этого пресета.\n\n"
        + _template_preview(local, inherited=universal)
        + "\n\n"
        + ("✅ Описания RU и EN заполнены." if ready else f"⚠️ {html.escape(warning)}")
        + "\n\nЭффективный шаблон, который будет использован при заполнении лота:\n"
        + _template_preview(effective)
    )
    return text[:4050]


def _preset_lot_template_keyboard(key: str):
    kb = K(row_width=1)
    for field, label in LOT_TEMPLATE_FIELDS:
        kb.add(B(label, callback_data=f"{CBT.LOT_TEMPLATE_FIELD}:{key}:{field}"))
    kb.add(B("🧹 Сбросить локальные поля", callback_data=f"{CBT.LOT_TEMPLATE}:reset:{key}"))
    kb.add(B("🧾 Расширенный JSON пресета", callback_data=f"{CBT.LOT_TEMPLATE_JSON}:{key}"))
    kb.add(B("⬅️ Назад", callback_data=f"{CBT.PRESET}:{key}"))
    return kb


def _funpay_text() -> str:
    data = _load_funpay_settings()
    tags = json.dumps(data.get("lot_tags", []), ensure_ascii=False)
    messages = json.dumps(data.get("order_messages", {}), ensure_ascii=False, indent=2)
    template = data.get("default_template", {})
    ready, warning = _template_is_ready(template if isinstance(template, dict) else {})
    return (
        "<b>🎯 FunPay</b>\n\n"
        "Универсальные настройки связи каталога с лотами FunPay.\n"
        f"Теги: <code>{html.escape(tags[:500])}</code>\n"
        f"Проверять лоты перед сохранением: <code>{'да' if data.get('validate_lots_before_save', True) else 'нет'}</code>\n\n"
        "Универсальный шаблон лота:\n" + _template_preview(template) + "\n"
        + ("✅ Описания RU и EN заполнены." if ready else f"⚠️ {html.escape(warning)}") + "\n\n"
        "Сообщения заказов:\n<pre>" + html.escape(messages[:1200]) + "</pre>"
    )


def _metadata_value(metadata: dict[str, Any], path: Any) -> Any:
    value: Any = metadata
    for part in str(path).split("."):
        if isinstance(value, dict):
            value = value.get(part)
        else:
            return None
    return value


def _numeric_metadata_value(value: Any, default: int = 0) -> int:
    try:
        number = float(str(value).strip().replace(",", "."))
    except (TypeError, ValueError):
        return default
    return int(number) if number >= 0 else default


def _dota_mmr(metadata: dict[str, Any]) -> int:
    mmr = _numeric_metadata_value(_item_field(metadata, "steam_dota2_solo_mmr", default=0))
    return mmr if mmr > 0 else 1500


def _dota_rank(mmr: int, names: tuple[str, ...]) -> str:
    total_stars = max(0, int(mmr)) // 154
    rank_index = total_stars // 5
    if rank_index >= len(names):
        return "ТИТАН" if names is DOTA_RANK_NAMES_RU else "IMMORTAL"
    return f"{names[rank_index]} {total_stars % 5 + 1}"


def _dota_hours(metadata: dict[str, Any]) -> int:
    games = _item_field(metadata, "steam_full_games", default={})
    if isinstance(games, dict):
        value = _metadata_value(games, "list.570.playtime_forever")
    else:
        value = 0
    return _numeric_metadata_value(value)


def _template_replacements(metadata: dict[str, Any]) -> dict[str, Any]:
    if "valorantInventory" in metadata or "riot_valorant_level" in metadata:
        _enrich_valorant_metadata(metadata)
    mmr = _dota_mmr(metadata)
    games = _numeric_metadata_value(_item_field(metadata, "steam_dota2_game_count", default=0))
    behavior = _numeric_metadata_value(_item_field(metadata, "steam_dota2_behavior", default=0))
    hours = _dota_hours(metadata)
    return {
        "item_id": _item_field(metadata, "item_id", "id", default=""),
        "price": _item_field(metadata, "rub_price", "price", default=""),
        "title": _item_field(metadata, "title", default=""),
        "mmr": mmr,
        "behavior": behavior,
        "games": games,
        "matches": games,
        "wins": _item_field(metadata, "steam_dota2_win_count", default=""),
        "hours": hours,
        "region": _item_field(metadata, "steam_country", default=""),
        "level": _item_field(metadata, "steam_level", default=""),
        "rank_ru": _dota_rank(mmr, DOTA_RANK_NAMES_RU),
        "rank_en": _dota_rank(mmr, DOTA_RANK_NAMES_EN),
        "mainpool_ru": "МЕЙНПУЛ",
        "mainpool_en": "MAINPOOL",
        "topups_ru": "БЕЗ ПОПОЛНЕНИЙ",
        "topups_en": "NO TOP-UPS",
        "valorant_region": _item_field(metadata, "valorant_region", "riot_valorant_region", default=""),
        "valorant_server_id": _item_field(metadata, "valorant_server_id", default=""),
        "valorant_rank_ru": _item_field(metadata, "valorant_rank_ru", default="Не указан"),
        "valorant_rank_en": _item_field(metadata, "valorant_rank_en", default="Not specified"),
        "valorant_rank_title_ru": str(_item_field(metadata, "valorant_rank_ru", default="Не указан")).upper(),
        "valorant_rank_title_en": str(_item_field(metadata, "valorant_rank_en", default="Not specified")).upper(),
        "valorant_level": _item_field(metadata, "valorant_level", "riot_valorant_level", default=""),
        "valorant_agent_count": _item_field(metadata, "valorant_agent_count", "riot_valorant_agent_count", default=0),
        "valorant_agents": _item_field(metadata, "valorant_agents_text", default="не указаны"),
        "agents": _item_field(metadata, "valorant_agents_text", default="не указаны"),
        "valorant_skin_count": _item_field(metadata, "valorant_skin_count", "riot_valorant_skin_count", default=0),
        "valorant_skins_ru": _item_field(metadata, "valorant_skins_ru_text", default="не указаны"),
        "valorant_skins_en": _item_field(metadata, "valorant_skins_en_text", default="not specified"),
        "skins_ru": _item_field(metadata, "valorant_skins_ru_text", default="не указаны"),
        "skins_en": _item_field(metadata, "valorant_skins_en_text", default="not specified"),
        "valorant_top_skin_ru": _item_field(metadata, "valorant_top_skin_ru", default="не указан"),
        "valorant_top_skin_en": _item_field(metadata, "valorant_top_skin_en", default="not specified"),
    }


def _render_template_value(value: str, replacements: dict[str, Any]) -> str:
    rendered = value
    for name, replacement in replacements.items():
        rendered = rendered.replace("{" + name + "}", str(replacement))
        rendered = rendered.replace("$" + name, str(replacement))
    return rendered


def _normalise_funpay_field_value(field_name: str, value: Any) -> Any:
    if value in (None, ""):
        return value
    if field_name == "fields[region]":
        text = " ".join(str(value).strip().split())
        return FUNPAY_REGION_ALIASES.get(text.casefold(), "Другой")
    if field_name == "fields[solommr]":
        return str(_numeric_metadata_value(value, 1500) or 1500)
    if field_name in {"fields[decency]", "fields[politeness]", "fields[games]", "fields[time]"}:
        return str(_numeric_metadata_value(value))
    return value


def build_funpay_lot_fields(preset: dict[str, Any], metadata: dict[str, Any],
                            base_fields: dict[str, Any] | None = None,
                            price: float | None = None,
                            amount: int = 1) -> dict[str, Any]:
    """Build a FunPay form payload without sending it to FunPay.

    The form-specific values stay in the preset's ``funpay.field_values``;
    this keeps support for new FunPay categories data-driven.
    """
    config = preset.get("funpay", {}) if isinstance(preset, dict) else {}
    result = dict(base_fields or {})
    values = config.get("field_values", {}) if isinstance(config, dict) else {}
    if isinstance(values, dict):
        result.update({str(key): value for key, value in values.items()})
    if isinstance(config, dict) and config.get("offer_type") and not result.get("fields[type]"):
        result["fields[type]"] = str(config["offer_type"])
    metadata_map = config.get("metadata_map", {}) if isinstance(config, dict) else {}
    if isinstance(metadata_map, dict):
        for field_name, metadata_path in metadata_map.items():
            value = _metadata_value(metadata, metadata_path)
            if value is not None and value != "":
                result[str(field_name)] = _normalise_funpay_field_value(str(field_name), value)
    for field_name, value in list(result.items()):
        result[field_name] = _normalise_funpay_field_value(str(field_name), value)

    global_template = _load_funpay_settings().get("default_template", {})
    local_template = config.get("templates", {}) if isinstance(config, dict) else {}
    template = dict(global_template) if isinstance(global_template, dict) else {}
    if isinstance(local_template, dict):
        template.update(local_template)
    template_values = _template_replacements(metadata)
    for key, value in template.items():
        if not isinstance(value, str):
            continue
        template[key] = _render_template_value(value, template_values)
    field_map = {
        "summary_ru": "fields[summary][ru]",
        "summary_en": "fields[summary][en]",
        "description_ru": "fields[desc][ru]",
        "description_en": "fields[desc][en]",
        "payment_msg_ru": "fields[payment_msg][ru]",
        "payment_msg_en": "fields[payment_msg][en]",
    }
    for source, target in field_map.items():
        if template.get(source) is not None:
            result[target] = template[source]
    for summary_field in ("fields[summary][ru]", "fields[summary][en]"):
        if summary_field in result:
            result[summary_field] = _fit_funpay_summary(result[summary_field])
    if price is not None:
        result["price"] = str(price)
    result["amount"] = str(max(0, int(amount)))
    return result


def _funpay_payload_hash(payload: dict[str, Any]) -> str:
    """Return a stable fingerprint for the values sent to FunPay."""
    encoded = json.dumps(
        payload,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
        default=str,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _funpay_lot_matches_payload(lot_fields: Any, payload: dict[str, Any],
                                *, active: bool, amount: int) -> bool:
    """Check an existing lot before migrating a record without a hash."""
    fields = getattr(lot_fields, "fields", {})
    if not isinstance(fields, dict):
        return False
    for field_name, expected in payload.items():
        if field_name in {"price", "amount"} or expected is None:
            continue
        actual = fields.get(str(field_name), "")
        if str(actual) != str(expected):
            return False
    try:
        if abs(float(getattr(lot_fields, "price", 0.0)) - float(payload.get("price", 0.0))) > 0.001:
            return False
    except (TypeError, ValueError):
        return False
    try:
        if int(getattr(lot_fields, "amount", -1)) != int(amount):
            return False
    except (TypeError, ValueError):
        return False
    return bool(getattr(lot_fields, "active", False)) == bool(active)


def _apply_funpay_payload_to_lot(lot_fields: Any, payload: dict[str, Any],
                                 *, active: bool, amount: int) -> None:
    """Apply a generated payload to an existing FunPay ``LotFields`` object.

    ``LotFields`` owns the form-specific values in ``fields``. Keeping this
    adapter here makes new FunPay subcategories data-driven: the preset only
    needs to know the field names returned by that subcategory's edit form.
    Empty values for the six text fields are applied deliberately: this lets
    a preset clear an old payment message or description when requested.
    """
    for key, value in payload.items():
        if key in {"price", "amount"} or value is None or value == "":
            continue
        lot_fields.fields[str(key)] = str(value)
    text_fields = {
        "fields[summary][ru]": "title_ru",
        "fields[summary][en]": "title_en",
        "fields[desc][ru]": "description_ru",
        "fields[desc][en]": "description_en",
        "fields[payment_msg][ru]": "payment_msg_ru",
        "fields[payment_msg][en]": "payment_msg_en",
    }
    for field_name, attribute in text_fields.items():
        value = payload.get(field_name)
        if field_name in payload and value is not None:
            lot_fields.fields[field_name] = str(value)
            setattr(lot_fields, attribute, str(value))
    if payload.get("price") not in (None, ""):
        lot_fields.price = float(payload["price"])
    lot_fields.amount = max(0, int(amount))
    lot_fields.active = bool(active and amount > 0)
    if lot_fields.auto_delivery is not None:
        # Credentials must never be placed in FunPay's built-in secret list.
        lot_fields.auto_delivery = False
        lot_fields.secrets = []
    if lot_fields.deactivate_after_sale is not None:
        lot_fields.deactivate_after_sale = False


def _catalog_records_for_preset(catalog: dict[str, Any], preset_key: str) -> list[dict[str, Any]]:
    records = []
    raw_items = catalog.get("items", {}) if isinstance(catalog, dict) else {}
    if not isinstance(raw_items, dict):
        return records
    for record in raw_items.values():
        if not isinstance(record, dict) or preset_key not in record.get("preset_keys", []):
            continue
        if record.get("status") not in {None, "candidate"}:
            continue
        if _item_id(record.get("metadata", {})):
            records.append(record)
    def price_key(record: dict[str, Any]) -> tuple[int, float, str]:
        raw = _item_field(record.get("metadata", {}), "rub_price", "price", default="")
        try:
            return (0, float(str(raw).replace(",", ".")), _item_id(record.get("metadata", {})))
        except (TypeError, ValueError):
            return (1, 0.0, _item_id(record.get("metadata", {})))
    records.sort(key=price_key)
    return records


def _funpay_buyer_coefficient(preset: dict[str, Any]) -> float:
    config = preset.get("funpay", {}) if isinstance(preset, dict) else {}
    if not isinstance(config, dict) or config.get("price_mode") != "buyer":
        return 1.0
    configured = config.get("commission_percent")
    if configured not in (None, ""):
        return 1.0 + max(0.0, _float(configured, 0.0, minimum=0.0)) / 100.0
    subcategory_id = _int(config.get("subcategory_id"), 0)
    if not _cardinal or not _cardinal.account or subcategory_id <= 0:
        raise RuntimeError("FunPay API не инициализирован для расчёта комиссии")
    result = _cardinal.account.calc(
        SubCategoryTypes.COMMON, subcategory_id=subcategory_id, price=1000
    )
    coefficient = float(result.commission_coefficient)
    if coefficient <= 0:
        raise ValueError("FunPay вернул некорректный коэффициент комиссии")
    return coefficient


def _funpay_internal_price(buyer_price: float, coefficient: float) -> float:
    if coefficient <= 1.0:
        return round(buyer_price, 2)
    return round(buyer_price / coefficient, 2)


def _set_funpay_lot_availability(lot_id: Any, *, active: bool, amount: int) -> None:
    if not _cardinal or not _cardinal.account:
        raise RuntimeError("FunPay API не инициализирован")
    def prepare_fields(fields: Any) -> None:
        _apply_funpay_payload_to_lot(fields, {}, active=active, amount=amount)

    _save_funpay_lot_with_retry(_int(lot_id, 0), prepare_fields)


def _check_lzt_balance_and_update_lots() -> dict[str, Any]:
    """Deactivate only catalog-bound lots whose source price exceeds LZT funds."""
    balance_id, balance_amount = LZTAccountOperations.get_purchase_balance()
    catalog = _load_catalog()
    presets = _load_presets()
    disabled_presets: set[str] = set()
    blocked = 0
    reactivated = 0
    checked = 0
    for record in catalog.get("items", {}).values():
        if not isinstance(record, dict) or record.get("status") != "candidate":
            continue
        lot_id = record.get("funpay_lot_id")
        if not lot_id:
            continue
        preset_keys = record.get("preset_keys", [])
        preset_key = next((key for key in preset_keys if key in presets), None) \
            if isinstance(preset_keys, list) else None
        preset = presets.get(preset_key, {}) if preset_key else {}
        if isinstance(preset, dict) and not preset.get("selling_enabled", True):
            already_disabled = (
                record.get("lot_sync_status") == "sales_disabled"
                and record.get("lot_sync_active") is False
                and record.get("lot_sync_amount") == 0
            )
            if not already_disabled:
                _set_funpay_lot_availability(lot_id, active=False, amount=0)
            record["lot_sync_status"] = "sales_disabled"
            record["lot_sync_active"] = False
            record["lot_sync_amount"] = 0
            disabled_presets.add(str(preset_key))
            continue
        metadata = record.get("metadata", {})
        try:
            source_price = float(str(_item_field(metadata, "rub_price", "price", default="")).replace(",", "."))
        except (TypeError, ValueError):
            continue
        checked += 1
        should_block = source_price > balance_amount + 0.009
        was_blocked = bool(record.get("balance_blocked"))
        desired_active = not should_block
        desired_amount = 1 if desired_active else 0
        known_active = record.get("lot_sync_active")
        legacy_availability = known_active is None and record.get("lot_sync_amount") is None
        if known_active is None:
            known_active = not was_blocked and record.get("lot_sync_status") != "sales_disabled"
        availability_changed = bool(known_active) != desired_active
        if not legacy_availability:
            availability_changed = availability_changed or record.get("lot_sync_amount") != desired_amount
        if availability_changed:
            _set_funpay_lot_availability(
                lot_id, active=desired_active, amount=desired_amount
            )
            if desired_active:
                record["balance_reactivated_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
                reactivated += 1
            else:
                record["balance_blocked_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
                blocked += 1
        record["balance_blocked"] = should_block
        record["lot_sync_active"] = desired_active
        record["lot_sync_amount"] = desired_amount
        record["balance_checked_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        record["balance_amount"] = balance_amount
        if should_block:
            record["lot_sync_status"] = "balance_blocked"
        elif record.get("lot_sync_status") == "balance_blocked":
            record["lot_sync_status"] = "active"
    _save_catalog(catalog)
    logger.info(
        "LZT-FP: balance lot check completed balance_id=%s amount=%.2f checked=%s blocked=%s reactivated=%s",
        balance_id, balance_amount, checked, blocked, reactivated,
    )
    return {
        "balance_id": balance_id,
        "balance": balance_amount,
        "checked": checked,
        "blocked": blocked,
        "reactivated": reactivated,
        "sales_disabled": len(disabled_presets),
    }


def _safe_balance_check(reason: str) -> None:
    try:
        _check_lzt_balance_and_update_lots()
    except Exception as exc:
        logger.warning("LZT-FP: balance check failed reason=%s error=%s", reason, _exception_detail(exc))


def _balance_monitor_worker() -> None:
    while not _balance_monitor_stop.is_set():
        _safe_balance_check("hourly")
        if _balance_monitor_stop.wait(3600):
            return


def _start_balance_monitor() -> None:
    global _balance_monitor_thread
    if _balance_monitor_thread and _balance_monitor_thread.is_alive():
        return
    _balance_monitor_stop.clear()
    _balance_monitor_thread = threading.Thread(
        target=_balance_monitor_worker, daemon=True, name="lztfp-balance-monitor"
    )
    _balance_monitor_thread.start()


def _reconcile_presets(preset_keys: list[str]) -> list[str]:
    results: list[str] = []
    with _lot_reconcile_lock:
        for preset_key in preset_keys:
            try:
                bound, disabled, _messages = _sync_funpay_lot_pool(preset_key)
                results.append(f"{preset_key}: {bound} привязано, {disabled} отключено")
            except Exception as exc:
                logger.error(
                    "LZT-FP: automatic lot reconciliation failed preset=%s: %s",
                    preset_key,
                    _short_exception(exc),
                )
                results.append(f"{preset_key}: ошибка {exc}")
    return results


def _catalog_monitor_worker() -> None:
    while not _catalog_monitor_stop.is_set():
        presets = _load_presets()
        preset_keys = [
            key for key, preset in presets.items()
            if isinstance(preset, dict) and preset.get("enabled", True)
        ]
        if preset_keys and _refresh_lock.acquire(blocking=False):
            try:
                _refresh_catalog(preset_keys)
                _reconcile_presets(preset_keys)
            except Exception:
                logger.exception("LZT-FP: scheduled catalog refresh failed")
            finally:
                _refresh_lock.release()
        _safe_balance_check("catalog refresh")
        if _catalog_monitor_stop.wait(CATALOG_REFRESH_INTERVAL_SECONDS):
            return


def _start_catalog_monitor() -> None:
    global _catalog_monitor_thread
    if _catalog_monitor_thread and _catalog_monitor_thread.is_alive():
        return
    _catalog_monitor_stop.clear()
    _catalog_monitor_thread = threading.Thread(
        target=_catalog_monitor_worker, daemon=True, name="lztfp-catalog-monitor"
    )
    _catalog_monitor_thread.start()


def _lot_id_from_shortcut(lot: Any) -> int:
    return _int(getattr(lot, "id", getattr(lot, "lot_id", 0)), 0)


def _owned_funpay_lot_ids(account: Any, subcategory_id: int) -> set[int]:
    return {
        _lot_id_from_shortcut(lot)
        for lot in account.get_my_subcategory_lots(subcategory_id)
        if _lot_id_from_shortcut(lot) > 0
    }


def _visible_funpay_lot_ids(account: Any, subcategory_id: int) -> set[int]:
    result = _owned_funpay_lot_ids(account, subcategory_id)
    try:
        result.update(
            _lot_id_from_shortcut(lot)
            for lot in account.get_subcategory_public_lots(
                SubCategoryTypes.COMMON, subcategory_id
            )
            if _lot_id_from_shortcut(lot) > 0
        )
    except Exception as exc:
        logger.debug("LZT-FP: public FunPay lot lookup failed: %s", exc)
    return result


def _preset_lot_ids(preset: dict[str, Any]) -> list[int]:
    config = preset.get("funpay", {}) if isinstance(preset, dict) else {}
    raw_ids = config.get("lot_ids", []) if isinstance(config, dict) else []
    result: list[int] = []
    seen: set[int] = set()
    if not isinstance(raw_ids, list):
        return result
    for raw_id in raw_ids:
        lot_id = _int(raw_id, 0)
        if lot_id > 0 and lot_id not in seen:
            result.append(lot_id)
            seen.add(lot_id)
    return result


def _preset_retired_lot_ids(preset: dict[str, Any]) -> list[int]:
    config = preset.get("funpay", {}) if isinstance(preset, dict) else {}
    raw_ids = config.get("retired_lot_ids", []) if isinstance(config, dict) else []
    result: list[int] = []
    seen: set[int] = set()
    if not isinstance(raw_ids, list):
        return result
    for raw_id in raw_ids:
        lot_id = _int(raw_id, 0)
        if lot_id > 0 and lot_id not in seen:
            result.append(lot_id)
            seen.add(lot_id)
    return result


def _lot_ids_claimed_by_other_presets(
    presets: dict[str, dict[str, Any]], preset_key: str, subcategory_id: int,
) -> set[int]:
    claimed: set[int] = set()
    for other_key, other_preset in presets.items():
        if other_key == preset_key or not isinstance(other_preset, dict):
            continue
        other_config = other_preset.get("funpay", {})
        if not isinstance(other_config, dict) or _int(other_config.get("subcategory_id"), 0) != subcategory_id:
            continue
        claimed.update(_preset_lot_ids(other_preset))
    return claimed


def _is_missing_funpay_lot_error(exc: Exception) -> bool:
    status_code = getattr(exc, "status_code", None)
    if status_code in {404, 410}:
        return True
    error_message = str(getattr(exc, "error_message", "") or exc).casefold()
    return any(
        phrase in error_message
        for phrase in ("предложение не найдено", "лот не найден", "offer not found", "lot not found")
    )


def _prune_missing_preset_lots(
    presets: dict[str, Any], preset_key: str, preset: dict[str, Any], subcategory_id: int
) -> tuple[list[int], list[int]]:
    """Remove configured IDs that are absent from FunPay's current subcategory."""
    configured = _preset_lot_ids(preset)
    if not configured:
        return [], []
    if not _cardinal or not _cardinal.account:
        raise RuntimeError("FunPay API не инициализирован")
    owned = _owned_funpay_lot_ids(_cardinal.account, subcategory_id)
    existing = [lot_id for lot_id in configured if lot_id in owned]
    missing = [lot_id for lot_id in configured if lot_id not in owned]
    if missing:
        config = preset.setdefault("funpay", {})
        config["lot_ids"] = existing
        _save_presets(presets)
        logger.warning(
            "LZT-FP: removed missing FunPay lot IDs preset=%s subcategory=%s ids=%s",
            preset_key, subcategory_id, ",".join(str(lot_id) for lot_id in missing),
        )
    return existing, missing


def _deactivate_and_prune_lots(
    presets: dict[str, Any], preset: dict[str, Any], lot_ids: list[int],
    keep_ids: set[int] | None = None,
) -> tuple[list[int], int]:
    """Deactivate unused lots and remove only successfully handled IDs from config."""
    keep_ids = keep_ids or set()
    retained: list[int] = []
    removed = 0
    for lot_id in lot_ids:
        if lot_id in keep_ids:
            retained.append(lot_id)
            continue
        try:
            _set_funpay_lot_availability(lot_id, active=False, amount=0)
        except Exception as exc:
            if _is_missing_funpay_lot_error(exc):
                removed += 1
                continue
            retained.append(lot_id)
            logger.warning(
                "LZT-FP: unused FunPay lot %s was not deactivated; keeping ID for retry: %s",
                lot_id, _short_exception(exc),
            )
            continue
        removed += 1
    config = preset.setdefault("funpay", {})
    if config.get("lot_ids") != retained:
        config["lot_ids"] = retained
        _save_presets(presets)
    return retained, removed


def _deactivate_retired_preset_lots(preset: dict[str, Any]) -> int:
    deactivated = 0
    for lot_id in _preset_retired_lot_ids(preset):
        try:
            _set_funpay_lot_availability(lot_id, active=False, amount=0)
        except Exception as exc:
            # A retired lot may have been deleted by FunPay. It must not
            # prevent the current candidate pool from being reconciled.
            logger.warning(
                "LZT-FP: retired lot %s is unavailable; continuing reconcile: %s",
                lot_id,
                _short_exception(exc),
            )
            continue
        deactivated += 1
    return deactivated


def _deactivate_preset_lots(preset: dict[str, Any]) -> int:
    deactivated = 0
    for lot_id in _preset_lot_ids(preset):
        _set_funpay_lot_availability(lot_id, active=False, amount=0)
        deactivated += 1
    deactivated += _deactivate_retired_preset_lots(preset)
    return deactivated


def _create_funpay_lot(preset: dict[str, Any], metadata: dict[str, Any],
                       subcategory_id: int, balance_amount: float,
                       buyer_coefficient: float) -> int:
    """Create one lot and resolve its ID by comparing the subcategory list."""
    account = _cardinal.account
    if FUNPAY_LOT_CREATE_DELAY_SECONDS > 0:
        time.sleep(FUNPAY_LOT_CREATE_DELAY_SECONDS)
    before = _visible_funpay_lot_ids(account, subcategory_id)
    try:
        lot_fields = account.get_lot_fields(node_id=subcategory_id)
    except Exception as exc:
        template_lot_ids = _preset_lot_ids(preset)
        if not template_lot_ids:
            raise
        # FunPay occasionally returns an unparsable empty editor form for a
        # category. Reuse an existing lot from the same preset as a form
        # template, but reset its offer ID so the save creates a new lot.
        template_lot_id = template_lot_ids[0]
        lot_fields = account.get_lot_fields(template_lot_id)
        lot_fields.lot_id = 0
        logger.warning(
            "LZT-FP: empty lot form unavailable for subcategory=%s; using lot=%s as create template: %s",
            subcategory_id, template_lot_id, _short_exception(exc),
        )
    actual = getattr(getattr(lot_fields, "subcategory", None), "id", None)
    if actual is not None and int(actual) != subcategory_id:
        raise ValueError(f"новый лот: категория {actual}, ожидалась {subcategory_id}")
    source_price = _float(
        str(_item_field(metadata, "rub_price", "price", default="")).replace(",", "."),
        -1.0,
        minimum=-1.0,
    )
    if source_price < 0:
        raise ValueError(f"кандидат #{_item_id(metadata)} имеет некорректную цену")
    display_price = round(source_price * (1.0 + _preset_markup(preset) / 100.0), 2)
    affordable = source_price <= balance_amount + 0.009
    internal_price = _funpay_internal_price(display_price, buyer_coefficient)
    payload = build_funpay_lot_fields(preset, metadata, price=internal_price, amount=1)
    _apply_funpay_payload_to_lot(
        lot_fields, payload, active=affordable, amount=1 if affordable else 0
    )
    save_response = _save_funpay_lot_request(lot_fields)
    response_ids: set[int] = set()

    def collect_ids(value: Any) -> None:
        if isinstance(value, dict):
            for key, nested in value.items():
                if str(key).casefold() in {"id", "lot_id", "offer_id", "offerid", "offer"}:
                    candidate = _int(nested, 0)
                    if candidate > 0:
                        response_ids.add(candidate)
                collect_ids(nested)
        elif isinstance(value, list):
            for nested in value:
                collect_ids(nested)
        elif isinstance(value, str):
            for candidate in re.findall(r"(?:offer(?:=|/id=)|lot_id=)(\d+)", value):
                response_ids.add(_int(candidate, 0))

    collect_ids(save_response)
    created: list[int] = []
    for attempt in range(3):
        after = _visible_funpay_lot_ids(account, subcategory_id)
        created = sorted((after - before) | {item for item in response_ids if item > 0})
        if created:
            break
        if attempt < 2:
            time.sleep(1.0)
    if not created:
        raise RuntimeError("FunPay сохранил лот, но его ID не найден в подкатегории")
    return created[-1]


def _sync_funpay_lot_pool(preset_key: str) -> tuple[int, int, list[str]]:
    """Reconcile FunPay lots with the cheapest current LZT candidates."""
    if not _cardinal or not _cardinal.account:
        raise RuntimeError("FunPay API не инициализирован")
    presets = _load_presets()
    preset = presets.get(preset_key)
    if not isinstance(preset, dict):
        raise ValueError("пресет не найден")
    config = preset.get("funpay", {})
    expected = _int(config.get("subcategory_id"), 0) if isinstance(config, dict) else 0
    if expected <= 0:
        raise ValueError("у пресета не задана FunPay подкатегория")
    claimed_by_other = _lot_ids_claimed_by_other_presets(presets, preset_key, expected)
    lot_ids_before_filter = _preset_lot_ids(preset)
    lot_ids = [lot_id for lot_id in lot_ids_before_filter if lot_id not in claimed_by_other]
    if lot_ids != lot_ids_before_filter:
        config["lot_ids"] = lot_ids
        _save_presets(presets)
        logger.warning(
            "LZT-FP: removed FunPay lots claimed by another preset preset=%s ids=%s",
            preset_key,
            ",".join(str(lot_id) for lot_id in set(lot_ids_before_filter) - set(lot_ids)),
        )
    catalog = _load_catalog()
    records = _catalog_records_for_preset(catalog, preset_key)[:_preset_limit(preset)]
    messages: list[str] = []

    lot_ids, missing_lot_ids = _prune_missing_preset_lots(
        presets, preset_key, preset, expected
    )
    if missing_lot_ids:
        messages.append(
            "🧹 Удалены отсутствующие ID лотов: "
            + ", ".join(str(lot_id) for lot_id in missing_lot_ids)
        )

    # IDs from failed historical creations must never become active again.
    _deactivate_retired_preset_lots(preset)

    if not preset.get("selling_enabled", True):
        disabled = _deactivate_preset_lots(preset)
        for record in records:
            if str(record.get("funpay_lot_id") or "") in {str(lot_id) for lot_id in lot_ids}:
                record["lot_sync_status"] = "sales_disabled"
                record["balance_blocked"] = False
        _save_catalog(catalog)
        return 0, disabled, [f"⏸ Продажа отключена, деактивировано лотов: {disabled}"]

    template_ready, template_error = _template_is_ready(_effective_template(preset))
    if not template_ready:
        raise ValueError(f"шаблон FunPay не готов: {template_error}")
    if not records:
        lot_ids, disabled = _deactivate_and_prune_lots(
            presets, preset, lot_ids, keep_ids=set()
        )
        _save_catalog(catalog)
        return 0, disabled, [f"⏸ Кандидатов нет, деактивировано лотов: {disabled}"]

    _balance_id, balance_amount = LZTAccountOperations.get_purchase_balance()
    buyer_coefficient = _funpay_buyer_coefficient(preset)

    # Keep stable candidate-to-lot bindings where possible, then reuse free
    # slots before creating new lots for the remaining candidates.
    by_lot: dict[int, dict[str, Any]] = {}
    used_lots: set[int] = set()
    assigned_item_ids: set[str] = set()
    for record in records:
        lot_id = _int(record.get("funpay_lot_id"), 0)
        if lot_id in lot_ids and lot_id not in used_lots:
            by_lot[lot_id] = record
            used_lots.add(lot_id)
            assigned_item_ids.add(str(_item_id(record.get("metadata", {}))))

    target_lot_ids = [lot_id for lot_id in lot_ids if lot_id in used_lots]
    for lot_id in lot_ids:
        if len(target_lot_ids) >= len(records):
            break
        if lot_id not in used_lots:
            target_lot_ids.append(lot_id)
    lot_ids, removed_surplus = _deactivate_and_prune_lots(
        presets, preset, lot_ids, keep_ids=set(target_lot_ids)
    )
    if removed_surplus:
        messages.append(f"🧹 Лишних лотов выведено из рабочего пула: {removed_surplus}")

    free_lots = [lot_id for lot_id in target_lot_ids if lot_id not in used_lots]
    for record in records:
        item_id = str(_item_id(record.get("metadata", {})))
        if item_id in assigned_item_ids:
            continue
        if free_lots:
            lot_id = free_lots.pop(0)
        else:
            lot_id = _create_funpay_lot(
                preset, record.get("metadata", {}), expected,
                balance_amount, buyer_coefficient,
            )
            lot_ids.append(lot_id)
            target_lot_ids.append(lot_id)
            config["lot_ids"] = lot_ids
            _save_presets(presets)
        by_lot[lot_id] = record
        used_lots.add(lot_id)
        assigned_item_ids.add(item_id)
        # Persist each binding immediately so the queue can resume from this
        # exact point after a process restart.
        record["funpay_lot_id"] = lot_id
        _save_catalog(catalog)

    bound = 0
    disabled = removed_surplus
    for lot_id in lot_ids:
        record = by_lot.get(lot_id)
        try:
            if record is None:
                def prepare_empty_fields(lot_fields: Any) -> None:
                    actual = getattr(getattr(lot_fields, "subcategory", None), "id", None)
                    if actual is not None and int(actual) != expected:
                        raise ValueError(
                            f"лот {lot_id}: категория {actual}, ожидалась {expected}"
                        )
                    _apply_funpay_payload_to_lot(
                        lot_fields, {}, active=False, amount=0
                    )

                _save_funpay_lot_with_retry(lot_id, prepare_empty_fields)
                disabled += 1
                messages.append(f"⏸ <code>{lot_id}</code>: отключён, кандидатов больше нет")
                continue
            metadata = record.get("metadata", {})
            source_price = _float(
                str(_item_field(metadata, "rub_price", "price", default="")).replace(",", "."),
                -1.0,
                minimum=-1.0,
            )
            if source_price < 0:
                raise ValueError(f"кандидат #{_item_id(metadata)} имеет некорректную цену")
            display_price = round(source_price * (1.0 + _preset_markup(preset) / 100.0), 2)
            affordable = source_price <= balance_amount + 0.009
            desired_amount = 1 if affordable else 0
            internal_price = _funpay_internal_price(display_price, buyer_coefficient)
            payload = build_funpay_lot_fields(
                preset, metadata, price=internal_price, amount=1
            )
            payload_hash = _funpay_payload_hash(payload)
            needs_save = not (
                record.get("lot_payload_hash") == payload_hash
                and record.get("lot_sync_active") == affordable
                and record.get("lot_sync_amount") == desired_amount
            )
            if needs_save:
                lot_fields = _cardinal.account.get_lot_fields(lot_id)
                actual = getattr(getattr(lot_fields, "subcategory", None), "id", None)
                if actual is not None and int(actual) != expected:
                    raise ValueError(f"лот {lot_id}: категория {actual}, ожидалась {expected}")
                if not record.get("lot_payload_hash") and _funpay_lot_matches_payload(
                    lot_fields, payload, active=affordable, amount=desired_amount
                ):
                    needs_save = False
                else:
                    def prepare_fields(current_fields: Any) -> None:
                        actual_subcategory = getattr(
                            getattr(current_fields, "subcategory", None), "id", None
                        )
                        if actual_subcategory is not None and int(actual_subcategory) != expected:
                            raise ValueError(
                                f"лот {lot_id}: категория {actual_subcategory}, "
                                f"ожидалась {expected}"
                            )
                        _apply_funpay_payload_to_lot(
                            current_fields, payload,
                            active=affordable, amount=desired_amount,
                        )

                    _, _, save_attempts = _save_funpay_lot_with_retry(
                        lot_id,
                        prepare_fields,
                        initial_fields=lot_fields,
                    )
                    if save_attempts > 1:
                        messages.append(
                            f"🔁 <code>{lot_id}</code>: сохранён после "
                            f"{save_attempts} попыток FunPay"
                        )
            record["funpay_lot_id"] = lot_id
            if needs_save:
                record["lot_sync_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
            record["lot_payload_hash"] = payload_hash
            record["lot_sync_status"] = "active" if affordable else "balance_blocked"
            record["balance_blocked"] = not affordable
            record["lot_sync_active"] = affordable
            record["lot_sync_amount"] = desired_amount
            record["balance_amount"] = balance_amount
            record["buyer_price"] = display_price
            record["internal_price"] = internal_price
            bound += 1
            if needs_save:
                state = "активен" if affordable else "отключён: недостаточно баланса LZT"
                messages.append(
                    f"✅ <code>{lot_id}</code> ← аккаунт <code>#{_item_id(metadata)}</code> · "
                    f"{display_price:g} ₽ для покупателя · {state}"
                )
        except Exception as exc:
            logger.warning(
                "LZT-FP: lot sync skipped lot=%s item=%s: %s",
                lot_id,
                _item_id(record.get("metadata", {})) if record else "none",
                _short_exception(exc),
            )
            if _is_funpay_lot_save_error(exc):
                # Existing-lot saves are retried inside _save_funpay_lot_with_retry.
                # This branch is retained for saves outside that helper.
                detail = _funpay_lot_save_error_detail(exc)
                messages.append(
                    f"⚠️ <code>{lot_id}</code>: FunPay отклонил сохранение"
                    f"{f' ({html.escape(detail)})' if detail else ''}"
                )
            else:
                messages.append(
                    f"⚠️ <code>{lot_id}</code>: не обновлён, повторю в следующем цикле"
                )
        finally:
            _save_catalog(catalog)
    config["lot_ids"] = lot_ids
    _save_presets(presets)
    _save_catalog(catalog)
    return bound, disabled, messages


def _funpay_keyboard():
    kb = K(row_width=1)
    for field, label in LOT_TEMPLATE_FIELDS:
        kb.add(B(label, callback_data=f"{CBT.FUNPAY_TEMPLATE_FIELD}:{field}"))
    kb.add(B("🧾 Расширенный JSON шаблона", callback_data=f"{CBT.FUNPAY_TEMPLATE_JSON}"))
    kb.add(B("🏷 Изменить теги JSON", callback_data=f"{CBT.FUNPAY}:tags"))
    kb.add(B("💬 Сообщения заказов JSON", callback_data=f"{CBT.FUNPAY}:messages"))
    kb.add(B("⬅️ Назад", callback_data=CBT.MAIN))
    return kb


def _debug_text() -> str:
    accounts = _load_accounts().get("accounts", {})
    purchases = _load_purchases().get("operations", {})
    return (
        "<b>🛠 Отладка</b>\n\n"
        "Здесь можно проверить LZT-кандидата, вручную купить его после двух подтверждений и выполнить операции Steam Guard.\n"
        "Операции, отменяющие гарантию, вынесены под отдельное подтверждение. Секреты не сохраняются в файлы плагина.\n\n"
        f"Записей аккаунтов: <code>{len(accounts) if isinstance(accounts, dict) else 0}</code>\n"
        f"Операций покупки: <code>{len(purchases) if isinstance(purchases, dict) else 0}</code>"
    )


def _debug_keyboard():
    kb = K(row_width=1)
    kb.add(B("🔢 Указать item_id LZT", callback_data=f"{CBT.DEBUG_ITEM}:set"))
    kb.add(B("⬅️ Назад", callback_data=CBT.MAIN))
    return kb


def _debug_item_keyboard(item_id: str):
    kb = K(row_width=1)
    kb.add(B("💳 Проверить перед покупкой", callback_data=f"{CBT.PURCHASE_CHECK}:{item_id}"))
    for order in _orders_for_item(item_id, {"ready"}):
        order_id = str(order.get("order_id") or "")
        kb.add(B(
            f"📤 Выдать заказу #{order_id[:10]}",
            callback_data=f"{CBT.DELIVERY}:{item_id}:{order_id}",
        ))
    kb.add(B("🔐 Получить Steam Guard код", callback_data=f"{CBT.DEBUG_CODE}:{item_id}"))
    kb.add(B("✅ Список подтверждений SDA", callback_data=f"{CBT.DEBUG_CONFIRMATIONS}:{item_id}"))
    kb.add(B("✉️ Получить код почты", callback_data=f"{CBT.DEBUG_EMAIL_CODE}:{item_id}"))
    kb.add(B("📨 Получить последние письма", callback_data=f"{CBT.DEBUG_LETTERS}:{item_id}"))
    kb.add(B("⚠️ Получить maFile", callback_data=f"{CBT.DEBUG_DANGEROUS}:{item_id}:mafile"))
    kb.add(B("⚠️ Получить пароль временной почты", callback_data=f"{CBT.DEBUG_DANGEROUS}:{item_id}:email_password"))
    kb.add(B("🗑 Удалить Steam Guard", callback_data=f"{CBT.DEBUG_DANGEROUS}:{item_id}:remove_mafile"))
    kb.add(B("⬅️ Назад", callback_data=CBT.DEBUG))
    return kb


def _preset_key_for_item(item_id: str) -> str:
    raw_items = _load_catalog().get("items", {})
    record = raw_items.get(str(item_id)) if isinstance(raw_items, dict) else None
    if isinstance(record, dict):
        keys = record.get("preset_keys", [])
        if isinstance(keys, list) and keys:
            return str(keys[0])
    return ""


def _catalog_items() -> list[dict[str, Any]]:
    raw_items = _load_catalog().get("items", {})
    if not isinstance(raw_items, dict):
        return []
    items = [item for item in raw_items.values() if isinstance(item, dict)]
    def price_key(record: dict[str, Any]) -> tuple[int, float, str]:
        raw_price = _item_field(record.get("metadata", {}), "rub_price", "price", default=None)
        try:
            return (0, float(raw_price), str(record.get("item_id", "")))
        except (TypeError, ValueError):
            return (1, 0.0, str(record.get("item_id", "")))

    items.sort(key=price_key)
    return items


def _catalog_text() -> str:
    catalog = _load_catalog()
    items = _catalog_items()
    last_run = catalog.get("last_run") or {}
    lines = [
        "<b>📚 Каталог кандидатов</b>",
        f"Лотов: <code>{len(items)}</code>",
        f"Обновлён: <code>{html.escape(str(catalog.get('updated_at') or 'ещё не обновлялся'))}</code>",
    ]
    if last_run:
        lines.append(
            f"Последний запуск: <code>{html.escape(str(last_run.get('status', 'unknown')))}</code>"
        )
    if not items:
        lines.append("\nКаталог пуст. Запустите обновление по пресету.")
    else:
        lines.append("")
        shown = 0
        for item in items:
            candidate = _format_candidate(item.get("metadata", {}), _float(
                item.get("markup_percent"), 25.0, minimum=0.0
            ))
            if len("\n\n".join(lines + [candidate])) > 3900:
                break
            lines.append(candidate)
            shown += 1
        if shown < len(items):
            lines.append(f"\n<i>Показаны первые {shown} из {len(items)}.</i>")
    return "\n".join(lines)


def _catalog_keyboard():
    kb = K(row_width=1)
    kb.add(B("🔄 Обновить все включённые пресеты", callback_data=f"{CBT.REFRESH}:all"))
    kb.add(B("⬅️ Назад", callback_data=CBT.MAIN))
    return kb


def _prompt(kind: str) -> str:
    return {
        "token": "Отправьте API-токен LZT Market. Он сохранится локально и будет отображаться только частично.",
        "language": "Введите язык ответов API: <code>ru</code> или <code>en</code>.",
        "proxy": "Отправьте прокси с протоколом или <code>-</code>.",
        "timeout": "Введите таймаут запроса в секундах, например <code>300</code>.",
        "delay": "Введите минимальную задержку между запросами в секундах, например <code>0.5</code>.",
        "balance_id": "Введите ID баланса LZT для покупки или <code>-</code>, чтобы использовать баланс по умолчанию.",
        "preset_limit": "Введите количество кандидатов для этого пресета: целое число от 1 до 200.",
        "preset_markup": "Введите процент наценки для этого пресета, например <code>25</code>.",
        "preset_lot_ids": (
            "Отправьте ID FunPay-лотов через пробел, запятую, точку с запятой или с новой строки. "
            "Дубликаты будут удалены. Отправьте <code>-</code>, чтобы очистить пул.\n\n"
            "Текущий пул не изменится, пока ввод не будет принят."
        ),
        "preset_funpay": "Отправьте JSON-конфигурацию FunPay этого пресета. В ней задаются subcategory_id, lot_ids, field_values и templates.",
        "funpay_template": "Отправьте JSON универсального шаблона FunPay.",
        "funpay_tags": "Отправьте JSON-массив тегов FunPay, например <code>[\"steam\", \"account\"]</code>.",
        "debug_item": "Введите item_id купленного аккаунта LZT. Покупка через этот экран не выполняется.",
    }[kind]


def _start_edit(call) -> None:
    kind = call.data.split(":", 1)[1]
    state_key = (call.message.chat.id, call.from_user.id)
    _temporary[state_key] = {"kind": kind}
    message = _cardinal.telegram.bot.send_message(call.message.chat.id, _prompt(kind), reply_markup=_back(CBT.SETTINGS))
    _cardinal.telegram.set_state(call.message.chat.id, message.id, call.from_user.id, f"LZTFP_EDIT:{kind}")
    _cardinal.telegram.bot.answer_callback_query(call.id)


def _start_preset_edit(call) -> None:
    key = call.data.split(":", 2)[2]
    presets = _load_presets()
    preset = presets.get(key)
    if not preset:
        _cardinal.telegram.bot.answer_callback_query(call.id, "Пресет не найден", show_alert=True)
        return
    example = json.dumps(preset.get("filters", {}), ensure_ascii=False, indent=2)
    prompt = "Отправьте JSON-объект фильтров LZT. Поддерживаются все параметры API.\n\nТекущие фильтры:\n<pre>" + html.escape(example[:3000]) + "</pre>"
    state_key = (call.message.chat.id, call.from_user.id)
    _temporary[state_key] = {"kind": "preset", "preset_key": key}
    message = _cardinal.telegram.bot.send_message(call.message.chat.id, prompt, reply_markup=_back(f"{CBT.PRESET}:{key}"))
    _cardinal.telegram.set_state(call.message.chat.id, message.id, call.from_user.id, "LZTFP_EDIT:preset")
    _cardinal.telegram.bot.answer_callback_query(call.id)


def _start_preset_json_edit(call, kind: str) -> None:
    key = call.data.split(":", 1)[1]
    presets = _load_presets()
    preset = presets.get(key)
    if not preset:
        _cardinal.telegram.bot.answer_callback_query(call.id, "Пресет не найден", show_alert=True)
        return
    if kind == "preset_funpay":
        current = preset.get("funpay", {})
        prompt = "JSON-конфигурация FunPay пресета:\n<pre>" + html.escape(
            json.dumps(current, ensure_ascii=False, indent=2)[:3000]
        ) + "</pre>"
        state_name = "preset_funpay"
    else:
        current = {"selection_limit": _preset_limit(preset), "markup_percent": _preset_markup(preset)}
        prompt = "Отправьте JSON финансовых настроек пресета:\n<pre>" + html.escape(
            json.dumps(current, ensure_ascii=False, indent=2)
        ) + "</pre>"
        state_name = "preset_finance"
    state_key = (call.message.chat.id, call.from_user.id)
    _temporary[state_key] = {"kind": state_name, "preset_key": key}
    message = _cardinal.telegram.bot.send_message(
        call.message.chat.id, prompt, reply_markup=_back(f"{CBT.PRESET}:{key}")
    )
    _cardinal.telegram.set_state(call.message.chat.id, message.id, call.from_user.id, f"LZTFP_EDIT:{state_name}")
    _cardinal.telegram.bot.answer_callback_query(call.id)


def _start_funpay_edit(call) -> None:
    kind = call.data.split(":", 1)[1] if ":" in call.data else "template"
    data = _load_funpay_settings()
    if kind == "template":
        current = data.get("default_template", {})
        state_name = "funpay_template"
    elif kind == "tags":
        current = data.get("lot_tags", [])
        state_name = "funpay_tags"
    else:
        current = data.get("order_messages", {})
        state_name = "funpay_messages"
    prompt = "Отправьте JSON:\n<pre>" + html.escape(json.dumps(current, ensure_ascii=False, indent=2)[:3000]) + "</pre>"
    state_key = (call.message.chat.id, call.from_user.id)
    _temporary[state_key] = {"kind": state_name}
    message = _cardinal.telegram.bot.send_message(call.message.chat.id, prompt, reply_markup=_back(CBT.FUNPAY))
    _cardinal.telegram.set_state(call.message.chat.id, message.id, call.from_user.id, f"LZTFP_EDIT:{state_name}")
    _cardinal.telegram.bot.answer_callback_query(call.id)


def _start_funpay_template_field_edit(call) -> None:
    field = call.data.split(":", 1)[1]
    field_names = {name for name, _label in LOT_TEMPLATE_FIELDS}
    if field not in field_names:
        _cardinal.telegram.bot.answer_callback_query(call.id, "Неизвестное поле", show_alert=True)
        return
    data = _load_funpay_settings()
    current = _template_value(data.get("default_template", {}), field)
    label = dict(LOT_TEMPLATE_FIELDS)[field]
    prompt = (
        f"<b>{html.escape(label)}</b>\n\n"
        "Отправьте новое значение одним сообщением. Для переноса строки используйте обычный Enter.\n\n"
        f"Текущее значение:\n<pre>{html.escape(current or '(пусто)')}</pre>"
    )
    state_key = (call.message.chat.id, call.from_user.id)
    _temporary[state_key] = {"kind": "funpay_template_field", "template_field": field}
    message = _cardinal.telegram.bot.send_message(
        call.message.chat.id, prompt, reply_markup=_back(CBT.FUNPAY)
    )
    _cardinal.telegram.set_state(
        call.message.chat.id, message.id, call.from_user.id, "LZTFP_EDIT:funpay_template_field"
    )
    _cardinal.telegram.bot.answer_callback_query(call.id)


def _start_preset_template_field_edit(call) -> None:
    parts = call.data.split(":")
    if len(parts) != 3:
        return
    key, field = parts[1:]
    if field not in {name for name, _label in LOT_TEMPLATE_FIELDS}:
        _cardinal.telegram.bot.answer_callback_query(call.id, "Неизвестное поле", show_alert=True)
        return
    preset = _load_presets().get(key)
    if not isinstance(preset, dict):
        _cardinal.telegram.bot.answer_callback_query(call.id, "Пресет не найден", show_alert=True)
        return
    config = preset.get("funpay", {})
    local = config.get("templates", {}) if isinstance(config, dict) else {}
    current = _template_value(local, field) if isinstance(local, dict) else ""
    inherited = _template_value(_load_funpay_settings().get("default_template", {}), field)
    label = dict(LOT_TEMPLATE_FIELDS)[field]
    prompt = (
        f"<b>{html.escape(label)}</b> для пресета\n\n"
        "Отправьте новое значение одним сообщением. Пустое сообщение в Telegram не отправляется, "
        "поэтому для сброса используйте кнопку в меню шаблона.\n\n"
        f"Локальное значение:\n<pre>{html.escape(current or '(не задано)')}</pre>\n"
        f"Универсальное значение:\n<pre>{html.escape(inherited or '(пусто)')}</pre>"
    )
    state_key = (call.message.chat.id, call.from_user.id)
    _temporary[state_key] = {
        "kind": "preset_template_field",
        "preset_key": key,
        "template_field": field,
    }
    message = _cardinal.telegram.bot.send_message(
        call.message.chat.id, prompt, reply_markup=_back(f"{CBT.LOT_TEMPLATE}:{key}")
    )
    _cardinal.telegram.set_state(
        call.message.chat.id, message.id, call.from_user.id, "LZTFP_EDIT:preset_template_field"
    )
    _cardinal.telegram.bot.answer_callback_query(call.id)


def _reset_preset_template(call) -> None:
    key = call.data.split(":", 2)[2]
    presets = _load_presets()
    preset = presets.get(key)
    if not isinstance(preset, dict):
        _cardinal.telegram.bot.answer_callback_query(call.id, "Пресет не найден", show_alert=True)
        return
    config = preset.setdefault("funpay", {})
    if not isinstance(config, dict):
        config = {}
        preset["funpay"] = config
    config["templates"] = {}
    _save_presets(presets)
    _edit(call, _preset_lot_template_text(key), _preset_lot_template_keyboard(key))
    _cardinal.telegram.bot.answer_callback_query(call.id, "Локальные поля сброшены")


def _handle_input(message) -> None:
    state_key = (message.chat.id, message.from_user.id)
    state = _temporary.get(state_key, {})
    kind = state.get("kind")
    value = (message.text or "").strip()
    try:
        if kind == "token":
            if not value or len(value) > 4096:
                raise ValueError("токен не должен быть пустым")
            SETTINGS.api_token = value
            _save_settings()
        elif kind == "language":
            if value.lower() not in {"ru", "en"}:
                raise ValueError("допустимы только ru и en")
            SETTINGS.language = value.lower()
            _save_settings()
        elif kind == "proxy":
            SETTINGS.proxy = "" if value == "-" else value
            if SETTINGS.proxy and "://" not in SETTINGS.proxy:
                raise ValueError("укажите прокси вместе с протоколом")
            _save_settings()
        elif kind == "timeout":
            timeout = _input_float(value)
            if timeout < 1:
                raise ValueError("таймаут должен быть не меньше 1 секунды")
            SETTINGS.timeout_seconds = timeout
            _save_settings()
        elif kind == "delay":
            delay = _input_float(value)
            if delay < 0:
                raise ValueError("задержка не может быть отрицательной")
            SETTINGS.min_request_delay_seconds = delay
            _save_settings()
        elif kind == "balance_id":
            SETTINGS.balance_id = 0 if value in {"-", "0", ""} else _int(value, -1)
            if SETTINGS.balance_id < 0:
                raise ValueError("ID баланса должен быть неотрицательным числом")
            _save_settings()
        elif kind == "preset_limit":
            limit = _int(value, -1)
            if not 1 <= limit <= 200:
                raise ValueError("количество должно быть от 1 до 200")
            presets = _load_presets()
            presets[state["preset_key"]]["selection_limit"] = limit
            _save_presets(presets)
        elif kind == "preset_markup":
            markup = _input_float(value)
            if markup < 0:
                raise ValueError("наценка не может быть отрицательной")
            presets = _load_presets()
            presets[state["preset_key"]]["markup_percent"] = markup
            _save_presets(presets)
        elif kind == "preset_lot_ids":
            lot_ids = _parse_lot_ids(value)
            presets = _load_presets()
            preset_key = state["preset_key"]
            preset = presets.get(preset_key)
            if not isinstance(preset, dict):
                raise ValueError("пресет не найден")
            config = preset.setdefault("funpay", {})
            if not isinstance(config, dict):
                config = {}
                preset["funpay"] = config
            subcategory_id = _int(config.get("subcategory_id"), 0)
            claimed_by_other = (
                _lot_ids_claimed_by_other_presets(presets, preset_key, subcategory_id)
                if subcategory_id > 0 else set()
            )
            conflicts = [lot_id for lot_id in lot_ids if lot_id in claimed_by_other]
            if conflicts:
                raise ValueError(
                    "эти ID уже назначены другому пресету в этой подкатегории: "
                    + ", ".join(str(lot_id) for lot_id in conflicts)
                )
            config["lot_ids"] = lot_ids
            _save_presets(presets)
        elif kind == "preset":
            raw = json.loads(value)
            filters = _normalise_filters(raw)
            presets = _load_presets()
            presets[state["preset_key"]]["filters"] = filters
            _save_presets(presets)
        elif kind == "preset_finance":
            raw = json.loads(value)
            if not isinstance(raw, dict):
                raise ValueError("финансовые настройки должны быть JSON-объектом")
            limit = _int(raw.get("selection_limit"), -1)
            markup = _input_float(str(raw.get("markup_percent", "")))
            if not 1 <= limit <= 200 or markup < 0:
                raise ValueError("selection_limit: 1..200, markup_percent: >= 0")
            presets = _load_presets()
            presets[state["preset_key"]]["selection_limit"] = limit
            presets[state["preset_key"]]["markup_percent"] = markup
            _save_presets(presets)
        elif kind == "preset_funpay":
            raw = json.loads(value)
            if not isinstance(raw, dict):
                raise ValueError("FunPay-конфигурация должна быть JSON-объектом")
            if raw.get("subcategory_id") is not None and _int(raw.get("subcategory_id"), -1) < 1:
                raise ValueError("subcategory_id должен быть положительным числом или null")
            if not isinstance(raw.get("lot_ids", []), list):
                raise ValueError("lot_ids должен быть JSON-массивом")
            presets = _load_presets()
            presets[state["preset_key"]]["funpay"] = raw
            _save_presets(presets)
        elif kind == "funpay_template_field":
            field = state.get("template_field")
            if field not in {name for name, _label in LOT_TEMPLATE_FIELDS}:
                raise ValueError("неизвестное поле шаблона")
            data = _load_funpay_settings()
            template = data.setdefault("default_template", {})
            if not isinstance(template, dict):
                template = {}
                data["default_template"] = template
            template[field] = value
            _save_funpay_settings(data)
        elif kind == "preset_template_field":
            field = state.get("template_field")
            if field not in {name for name, _label in LOT_TEMPLATE_FIELDS}:
                raise ValueError("неизвестное поле шаблона")
            presets = _load_presets()
            preset = presets.get(state.get("preset_key"))
            if not isinstance(preset, dict):
                raise ValueError("пресет не найден")
            config = preset.setdefault("funpay", {})
            if not isinstance(config, dict):
                config = {}
                preset["funpay"] = config
            templates = config.setdefault("templates", {})
            if not isinstance(templates, dict):
                templates = {}
                config["templates"] = templates
            templates[field] = value
            _save_presets(presets)
        elif kind == "funpay_template":
            raw = json.loads(value)
            if not isinstance(raw, dict):
                raise ValueError("шаблон должен быть JSON-объектом")
            data = _load_funpay_settings()
            data["default_template"] = raw
            _save_funpay_settings(data)
        elif kind == "funpay_tags":
            raw = json.loads(value)
            if not isinstance(raw, list) or not all(isinstance(item, str) for item in raw):
                raise ValueError("теги должны быть JSON-массивом строк")
            data = _load_funpay_settings()
            data["lot_tags"] = raw
            _save_funpay_settings(data)
        elif kind == "funpay_messages":
            raw = json.loads(value)
            if not isinstance(raw, dict) or not all(isinstance(key, str) and isinstance(item, str) for key, item in raw.items()):
                raise ValueError("сообщения должны быть JSON-объектом строк")
            data = _load_funpay_settings()
            data["order_messages"] = raw
            _save_funpay_settings(data)
        elif kind == "debug_item":
            item_id = _item_id({"item_id": value})
            if not item_id:
                raise ValueError("item_id должен быть числом")
            _debug_item_ids[message.from_user.id] = item_id
            result = f"✅ Item ID сохранён: <code>{item_id}</code>"
        else:
            raise ValueError("неизвестная настройка")
        result = "✅ Настройка сохранена."
    except (ValueError, json.JSONDecodeError) as exc:
        result = f"❌ Ошибка: <code>{html.escape(str(exc))}</code>"
    except Exception:
        logger.exception("LZT-FP: failed to save Telegram input")
        result = "❌ Не удалось сохранить настройку."
    finally:
        _temporary.pop(state_key, None)
        _cardinal.telegram.clear_state(message.chat.id, message.from_user.id)
    back = CBT.SETTINGS
    if kind in {"preset", "preset_finance", "preset_funpay", "preset_limit", "preset_markup", "preset_lot_ids", "preset_template_field"}:
        back = f"{CBT.PRESET}:{state.get('preset_key', '')}" if state.get("preset_key") else CBT.PRESETS
        if kind == "preset_template_field" and state.get("preset_key"):
            back = f"{CBT.LOT_TEMPLATE}:{state['preset_key']}"
    elif kind in {"funpay_template", "funpay_template_field", "funpay_tags", "funpay_messages"}:
        back = CBT.FUNPAY
    elif kind == "debug_item":
        back = CBT.DEBUG
    _cardinal.telegram.bot.send_message(message.chat.id, result, reply_markup=_back(back))


def _preview_worker(chat_id: int, message_id: int, preset_key: str) -> None:
    try:
        preset = _load_presets().get(preset_key)
        if not preset:
            raise ValueError("пресет не найден")
        items, total, search_url = _search_preset(
            preset, _preset_limit(preset), verify_items=True
        )
        if not items:
            text = "📊 <b>Предпросмотр</b>\n\nПодходящих аккаунтов не найдено."
        else:
            chunks = [_format_candidate(item, _preset_markup(preset)) for item in items]
            text = (
                f"📊 <b>Предпросмотр: {html.escape(str(preset.get('name', preset_key)))}</b>\n"
                f"Найдено: <code>{total}</code> · Показано: <code>{len(items)}</code>\n"
                f"Сортировка: <code>price</code> · Наценка: <code>{_preset_markup(preset):g}%</code>\n\n"
                + "\n\n".join(chunks)
            )
            if search_url:
                text += f"\n\nЗапрос LZT: <code>{html.escape(search_url)}</code>"
        if len(text) > 4090:
            text = text[:4050] + "\n\n<i>Список обрезан лимитом Telegram.</i>"
        _cardinal.telegram.bot.edit_message_text(text, chat_id, message_id, reply_markup=_back(f"{CBT.PRESET}:{preset_key}"))
    except Exception as exc:
        logger.exception("LZT-FP: preview failed for preset=%s", preset_key)
        text = f"❌ Ошибка предпросмотра: <code>{html.escape(str(exc))}</code>"
        try:
            _cardinal.telegram.bot.edit_message_text(text, chat_id, message_id, reply_markup=_back(f"{CBT.PRESET}:{preset_key}"))
        except Exception:
            _cardinal.telegram.bot.send_message(chat_id, text)


def _start_preview(call) -> None:
    preset_key = call.data.split(":", 1)[1]
    _cardinal.telegram.bot.answer_callback_query(call.id, "Запрос отправлен")
    _edit(call, "⏳ Получаю read-only выборку из LZT Market...", _back(f"{CBT.PRESET}:{preset_key}"))
    threading.Thread(target=_preview_worker, args=(call.message.chat.id, call.message.id, preset_key), daemon=True, name="lztfp-preview").start()


def _refresh_worker(chat_id: int, message_id: int, preset_keys: list[str], back_callback: str) -> None:
    if not _refresh_lock.acquire(blocking=False):
        text = "❌ Обновление уже выполняется. Дождитесь его завершения."
        _cardinal.telegram.bot.edit_message_text(text, chat_id, message_id, reply_markup=_back(back_callback))
        return
    try:
        selected, metadata = _refresh_catalog(preset_keys)
        reconciliation = _reconcile_presets(preset_keys)
        text = (
            "✅ <b>Каталог обновлён</b>\n\n"
            f"Выбрано кандидатов: <code>{selected}</code>\n"
            f"Метаданные загружены: <code>{metadata}</code>\n\n"
            "Лоты синхронизированы:\n" + "\n".join(reconciliation)
        )
    except Exception as exc:
        logger.exception("LZT-FP: catalog refresh failed")
        text = f"❌ Ошибка обновления каталога: <code>{html.escape(str(exc))}</code>"
    finally:
        _refresh_lock.release()
    try:
        _cardinal.telegram.bot.edit_message_text(text, chat_id, message_id, reply_markup=_back(back_callback))
    except Exception:
        _cardinal.telegram.bot.send_message(chat_id, text, reply_markup=_back(back_callback))


def _start_refresh(call) -> None:
    target = call.data.split(":", 1)[1]
    presets = _load_presets()
    if target == "all":
        preset_keys = [key for key, preset in presets.items() if preset.get("enabled", True)]
        back_callback = CBT.CATALOG
    else:
        if target not in presets:
            _cardinal.telegram.bot.answer_callback_query(call.id, "Пресет не найден", show_alert=True)
            return
        preset_keys = [target]
        back_callback = f"{CBT.PRESET}:{target}"
    if not preset_keys:
        _cardinal.telegram.bot.answer_callback_query(call.id, "Нет включённых пресетов", show_alert=True)
        return
    _cardinal.telegram.bot.answer_callback_query(call.id, "Обновление запущено")
    _edit(call, "⏳ Обновляю read-only каталог и загружаю метаданные...", _back(back_callback))
    threading.Thread(
        target=_refresh_worker,
        args=(call.message.chat.id, call.message.id, preset_keys, back_callback),
        daemon=True,
        name="lztfp-catalog-refresh",
    ).start()


def _debug_item_id(user_id: int) -> str:
    return _debug_item_ids.get(user_id, "")


def _json_preview(payload: Any, limit: int = 3500) -> str:
    text = json.dumps(payload, ensure_ascii=False, indent=2, default=str)
    return html.escape(text[:limit] + ("\n..." if len(text) > limit else ""))


def _debug_item_worker(chat_id: int, message_id: int, item_id: str) -> None:
    try:
        payload = _lzt_request(f"/{item_id}")
        item = _detail_payload(payload)
        data = _load_accounts()
        data.setdefault("accounts", {})[item_id] = {
            "item_id": int(item_id),
            "last_checked_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "capabilities": {
                key: item.get(key) for key in (
                    "canViewLoginData", "canViewTempEmail", "canChangePassword",
                    "canChangeEmailPassword", "steam_mfa", "emailLoginUrl",
                ) if key in item
            },
            "status": str(item.get("item_state", "unknown")),
        }
        _save_accounts(data)
        text = (
            f"<b>Аккаунт LZT #{item_id}</b>\n\n"
            f"Состояние: <code>{html.escape(str(item.get('item_state', 'не указано')))}</code>\n"
            f"Логин доступен: <code>{html.escape(str(item.get('canViewLoginData', 'не указано')))}</code>\n"
            f"Временная почта доступна: <code>{html.escape(str(item.get('canViewTempEmail', 'не указано')))}</code>\n"
            f"MaFile/SDA: <code>{html.escape(str(item.get('steam_mfa', 'не указано')))}</code>\n"
            f"Почтовая ссылка: <code>{html.escape(str(item.get('emailLoginUrl', 'не указана')))}</code>\n\n"
            "Секретные данные в отладочный файл не сохранялись."
        )
        markup = _debug_item_keyboard(item_id)
    except Exception as exc:
        logger.exception("LZT-FP: debug item inspection failed item=%s", item_id)
        text = f"❌ Ошибка проверки аккаунта: <code>{html.escape(str(exc))}</code>"
        markup = _back(CBT.DEBUG)
    try:
        _cardinal.telegram.bot.edit_message_text(text, chat_id, message_id, reply_markup=markup)
    except Exception:
        _cardinal.telegram.bot.send_message(chat_id, text, reply_markup=markup)


def _start_debug_item(call) -> None:
    target = call.data.split(":", 1)[1]
    if target == "set":
        state_key = (call.message.chat.id, call.from_user.id)
        _temporary[state_key] = {"kind": "debug_item"}
        message = _cardinal.telegram.bot.send_message(
            call.message.chat.id, _prompt("debug_item"), reply_markup=_back(CBT.DEBUG)
        )
        _cardinal.telegram.set_state(call.message.chat.id, message.id, call.from_user.id, "LZTFP_EDIT:debug_item")
        _cardinal.telegram.bot.answer_callback_query(call.id)
        return
    _cardinal.telegram.bot.answer_callback_query(call.id, "Проверка запущена")
    _edit(call, "⏳ Получаю read-only карточку LZT...", _back(CBT.DEBUG))
    threading.Thread(
        target=_debug_item_worker,
        args=(call.message.chat.id, call.message.id, target),
        daemon=True,
        name="lztfp-debug-item",
    ).start()


def _purchase_check_worker(chat_id: int, message_id: int, user_id: int, item_id: str) -> None:
    try:
        payload = LZTAccountOperations.check_account(item_id)
        item = payload.get("item", payload) if isinstance(payload, dict) else {}
        item = item if isinstance(item, dict) else {}
        price = _item_field(item, "rub_price", "price", default=None)
        if price in (None, ""):
            raise ValueError("LZT не вернул актуальную цену")
        state = str(item.get("item_state") or "").lower()
        if state and state not in {"active", "available"}:
            raise ValueError(f"аккаунт недоступен: {state}")
        numeric_price = float(str(price).replace(",", "."))
        _purchase_confirmations[(user_id, item_id)] = {
            "price": numeric_price,
            "checked_at": time.time(),
            "preset_key": _preset_key_for_item(item_id),
        }
        _record_purchase(
            item_id,
            status="checked",
            price=numeric_price,
            preset_key=_preset_key_for_item(item_id),
            details={"check_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())},
        )
        text = (
            f"<b>Проверка покупки #{item_id}</b>\n\n"
            f"Статус: <code>{html.escape(state or 'доступен')}</code>\n"
            f"Актуальная цена: <code>{numeric_price:g} ₽</code>\n\n"
            "Проверка не списала деньги. Следующая кнопка выполнит реальную покупку."
        )
        markup = K(row_width=1)
        markup.add(B(
            f"✅ Купить за {numeric_price:g} ₽",
            callback_data=f"{CBT.PURCHASE_CONFIRM}:{item_id}",
        ))
        markup.add(B("❌ Отмена", callback_data=f"{CBT.DEBUG_ITEM}:{item_id}"))
    except Exception as exc:
        logger.exception("LZT-FP: purchase check failed item=%s", item_id)
        text = f"❌ Проверка покупки не пройдена: <code>{html.escape(str(exc))}</code>"
        markup = _debug_item_keyboard(item_id)
    try:
        _cardinal.telegram.bot.edit_message_text(text, chat_id, message_id, reply_markup=markup)
    except Exception:
        _cardinal.telegram.bot.send_message(chat_id, text, reply_markup=markup)


def _start_purchase_check(call) -> None:
    item_id = call.data.split(":", 1)[1]
    _cardinal.telegram.bot.answer_callback_query(call.id, "Проверяю доступность")
    _edit(call, "⏳ Проверяю аккаунт LZT без покупки...", _back(f"{CBT.DEBUG_ITEM}:{item_id}"))
    threading.Thread(
        target=_purchase_check_worker,
        args=(call.message.chat.id, call.message.id, call.from_user.id, item_id),
        daemon=True,
        name="lztfp-purchase-check",
    ).start()


def _credentials_for_item(item_id: str) -> dict[str, Any]:
    record = _load_credentials().get("accounts", {}).get(str(item_id), {})
    return record if isinstance(record, dict) else {}


def _is_valorant_preset_key(preset_key: str) -> bool:
    preset = _load_presets().get(str(preset_key), {})
    return isinstance(preset, dict) and str(preset.get("category") or "").casefold() == "riot"


def _delivery_text(item_id: str) -> str:
    credentials = _credentials_for_item(item_id)
    def safe(value: Any, fallback: str = "не получен") -> str:
        return html.escape(str(value if value not in (None, "") else fallback))

    login = credentials.get("account_login") or credentials.get("steam_login")
    password = credentials.get("account_password") or credentials.get("steam_password")
    lines = ["✅ Аккаунт готов к выдаче!", "", "Данные для входа:", "", f"1. Логин: {safe(login)}", "", f"2. Пароль: {safe(password)}"]
    if credentials.get("email_login"):
        lines.extend(["", f"3. Почта: {safe(credentials['email_login'])}"])
    if credentials.get("email_password"):
        lines.extend(["", f"4. Пароль почты: {safe(credentials['email_password'])}"])
    if credentials.get("email_login_url"):
        lines.extend([
            "",
            f"Ссылка для входа в почту: {safe(credentials['email_login_url'])}",
        ])
    if credentials.get("backup_email_login") and credentials.get("backup_email_password"):
        lines.extend([
            "",
            "Данные от резервной почты: "
            f"{safe(credentials['backup_email_login'])}:{safe(credentials['backup_email_password'])}",
        ])
    if _is_valorant_preset_key(str(credentials.get("preset_key") or "")):
        return "\n".join(lines)
    if credentials.get("email_login") and credentials.get("email_password"):
        lines.extend([
            "",
            "Ниже представлена инструкция по проверке и перевязке аккаунта. "
            "Следуйте этой инструкции, чтобы сделка прошла качественно, а при возникновении "
            "трудностей вы могли претендовать на возврат.",
            "",
            '1. Войдите на аккаунт через логин и пароль. Авторизацию подтвердите по коду, '
            'который вы можете получить, введя в этот чат команду "!sg_code".',
            "",
            "2. Осмотрите аккаунт. Убедитесь, что он соответствует тому, что заявлено в названии и описании лота.",
            "",
            "3. ВАЖНО! Убедитесь, что почта, которая пришла вам после покупки, живая и существует. "
            'Если вы удалите Steam Guard (см. пункт 5) и окажется, что почта не принимает сообщения от Steam, '
            'то аккаунт можно считать "мёртвым" и возврат невозможен по причине того, что вы его "окирпичили".',
            "",
            '4. Смените почту на аккаунте. Для этого вам потребуется сначала получить подтверждение через Steam Guard '
            '(вы можете сделать это при помощи команды "!sg_confirm"), а затем получить код с почты '
            '(либо скопируйте его вручную с почты, либо используйте команду !email_code).',
            "",
            '5. Отвяжите мобильный аутентификатор. Для этого используйте команду "!sg_delete".',
            "",
            "6. Смените пароль на аккаунте. Подтверждение придёт уже на почту (причём на новую, которую вы привязали).",
            "",
            "7. Подтвердите выполнение заказа на Funpay. Буду благодарен, если оставите и хороший отзыв!",
        ])
    return "\n".join(lines)


def _deliver_order(item_id: str, order_id: str) -> tuple[bool, str]:
    data = _load_orders()
    record = data.get("orders", {}).get(str(order_id))
    if not isinstance(record, dict) or str(record.get("item_id") or "") != str(item_id):
        return False, "заказ не найден или не привязан к этому аккаунту"
    if record.get("status") != "ready":
        return False, f"заказ имеет статус {record.get('status', 'unknown')}"
    credentials = _credentials_for_item(item_id)
    if not _account_credentials_ready(credentials):
        return False, "в хранилище нет полного логина и пароля аккаунта"
    if not _cardinal:
        return False, "Cardinal не инициализирован"
    chat_id = record.get("chat_id")
    if not chat_id:
        return False, "у заказа нет chat_id"

    # Persist the attempt before sending anything. A crash after FunPay accepts
    # the message must conservatively block any later automatic refund.
    attempted_at = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    _update_order_record(
        order_id,
        delivery_attempted_at=attempted_at,
        delivery_item_id=str(item_id),
    )
    result = _cardinal.send_message(chat_id, _delivery_text(item_id))
    if not result:
        return False, "FunPay не подтвердил отправку сообщения"
    message_ids = [
        int(getattr(message, "id", 0) or 0)
        for message in result
        if int(getattr(message, "id", 0) or 0) > 0
    ]
    if not message_ids:
        return False, "FunPay отправил ответ без идентификатора сообщения"
    record["status"] = "issued"
    record["issued_at"] = attempted_at
    record["delivery_confirmed_at"] = attempted_at
    record["delivery_message_id"] = max(message_ids)
    record["updated_at"] = record["issued_at"]
    _save_orders(data)
    return True, "данные отправлены покупателю"


def _start_delivery_confirmation(call) -> None:
    parts = call.data.split(":")
    if len(parts) != 3:
        return
    item_id, order_id = parts[1:]
    record = _load_orders().get("orders", {}).get(order_id, {})
    buyer = html.escape(str(record.get("buyer") or "неизвестен")) if isinstance(record, dict) else "неизвестен"
    text = (
        "<b>⚠️ Подтвердите выдачу</b>\n\n"
        f"Аккаунт: <code>#{item_id}</code>\n"
        f"Заказ: <code>#{html.escape(order_id)}</code>\n"
        f"Покупатель: <code>{buyer}</code>\n\n"
        "После отправки данные нельзя отозвать этим плагином."
    )
    kb = K(row_width=1)
    kb.add(B("✅ Отправить данные", callback_data=f"{CBT.DELIVERY_CONFIRM}:{item_id}:{order_id}"))
    kb.add(B("❌ Отмена", callback_data=f"{CBT.DEBUG_ITEM}:{item_id}"))
    _edit(call, text, kb)
    _cardinal.telegram.bot.answer_callback_query(call.id)


def _confirm_delivery(call) -> None:
    parts = call.data.split(":")
    if len(parts) != 3:
        return
    item_id, order_id = parts[1:]
    try:
        ok, detail = _deliver_order(item_id, order_id)
        text = (f"✅ Выдача выполнена: {html.escape(detail)}" if ok
                else f"❌ Выдача не выполнена: <code>{html.escape(detail)}</code>")
    except Exception as exc:
        logger.exception("LZT-FP: manual delivery failed item=%s order=%s", item_id, order_id)
        text = f"❌ Ошибка выдачи: <code>{html.escape(str(exc))}</code>"
    _edit(call, text, _debug_item_keyboard(item_id))
    _cardinal.telegram.bot.answer_callback_query(call.id)


def _mark_orders_ready(item_id: str) -> list[dict[str, Any]]:
    data = _load_orders()
    ready: list[dict[str, Any]] = []
    for record in data.get("orders", {}).values():
        if not isinstance(record, dict) or str(record.get("item_id") or "") != str(item_id):
            continue
        if record.get("status") != "awaiting_manual_purchase":
            continue
        record["status"] = "ready"
        record["updated_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        ready.append(record)
    if ready:
        _save_orders(data)
    return ready


def _purchase_confirm_worker(chat_id: int, message_id: int, user_id: int, item_id: str,
                            confirmation: dict[str, Any]) -> None:
    if not _purchase_lock.acquire(blocking=False):
        text = "❌ Другая покупка уже выполняется. Дождитесь её завершения."
        _cardinal.telegram.bot.edit_message_text(text, chat_id, message_id, reply_markup=_back(CBT.DEBUG))
        return
    try:
        price = float(confirmation["price"])
        preset_key = str(confirmation.get("preset_key") or "")
        _record_purchase(item_id, status="purchase_started", price=price, preset_key=preset_key)
        payload = LZTAccountOperations.fast_buy(
            item_id, price, LZTAccountOperations.resolve_balance_id()
        )
        try:
            capability_summary = _prepare_full_access(item_id, payload, preset_key)
        except Exception as exc:
            _record_purchase(
                item_id,
                status="full_access_failed",
                price=price,
                preset_key=preset_key,
                details={"full_access_error": _exception_detail(exc)},
            )
            raise
        item = payload.get("item", payload) if isinstance(payload, dict) else {}
        item = item if isinstance(item, dict) else {}
        _mark_account_purchased(item_id, preset_key=preset_key, capabilities=capability_summary)
        ready_orders = _mark_orders_ready(item_id)
        catalog_record = _catalog_record_for_item(item_id)[0]
        if catalog_record:
            _update_catalog_item_status(item_id, "sold")
            if catalog_record.get("funpay_lot_id"):
                try:
                    _deactivate_funpay_lot(str(catalog_record["funpay_lot_id"]))
                except Exception:
                    logger.exception("LZT-FP: manually purchased FunPay lot could not be deactivated item=%s", item_id)
        _safe_balance_check("after manual purchase")
        _record_purchase(
            item_id,
            status="purchased",
            price=price,
            preset_key=preset_key,
            details={
                "lzt_status": str(payload.get("status") or "ok"),
                "item_state": str(item.get("item_state") or ""),
                "credentials_stored": True,
                "capabilities": capability_summary,
                "orders_ready": len(ready_orders),
            },
        )
        text = (
            f"✅ <b>Аккаунт #{item_id} куплен</b>\n\n"
            f"Цена: <code>{price:g} ₽</code>\n"
            "Данные сохранены в защищённое локальное хранилище.\n"
            f"Steam login: <code>{'да' if capability_summary['has_steam_login'] else 'нет'}</code>\n"
            f"Steam password: <code>{'да' if capability_summary['has_steam_password'] else 'нет'}</code>\n"
            f"Email: <code>{'да' if capability_summary['has_email_login'] else 'нет'}</code>\n\n"
            f"Заказов переведено в готовность: <code>{len(ready_orders)}</code>\n"
            "Передача клиенту и публикация credentials в FunPay пока не выполнялись."
        )
        markup = _debug_item_keyboard(item_id)
    except Exception as exc:
        logger.exception("LZT-FP: purchase failed item=%s", item_id)
        try:
            # FastBuy is a balance-changing request; after it starts, its result
            # must be treated as unknown until the item/order state is checked.
            current_operation = _load_purchases().get("operations", {}).get(str(item_id), {})
            current_status = current_operation.get("status") if isinstance(current_operation, dict) else ""
            if current_status != "full_access_failed":
                deterministic_failure = isinstance(exc, LZTAPIError) and 400 <= exc.status_code < 500
                _record_purchase(
                    item_id,
                    status="purchase_failed" if deterministic_failure else "purchase_unknown",
                    details=_purchase_error_details(exc),
                )
        except Exception:
            logger.exception("LZT-FP: failed to record purchase failure item=%s", item_id)
        if _is_lzt_account_validation_failure(exc):
            for order in _orders_for_item(item_id, {"awaiting_manual_purchase"}):
                order_id = str(order.get("order_id") or "")
                if not order_id:
                    continue
                if _try_auto_refund_after_validation_failure(order_id, item_id, exc):
                    continue
                _send_order_failure(
                    order_id,
                    item_id,
                    "ошибка проверки аккаунта LZT; автоматический возврат остановлен, требуется ручная проверка",
                )
        text = (
            f"❌ <b>Покупка #{item_id} не завершена</b>\n\n"
            f"Ошибка: <code>{html.escape(_exception_detail(exc))}</code>\n\n"
            "Проверьте состояние аккаунта и историю операций LZT перед повтором."
        )
        markup = _debug_item_keyboard(item_id)
    finally:
        _purchase_confirmations.pop((user_id, item_id), None)
        _purchase_lock.release()
    try:
        _cardinal.telegram.bot.edit_message_text(text, chat_id, message_id, reply_markup=markup)
    except Exception:
        _cardinal.telegram.bot.send_message(chat_id, text, reply_markup=markup)


def _confirm_purchase(call) -> None:
    item_id = call.data.split(":", 1)[1]
    confirmation = _purchase_confirmations.get((call.from_user.id, item_id))
    if not confirmation or time.time() - float(confirmation.get("checked_at", 0)) > 600:
        _purchase_confirmations.pop((call.from_user.id, item_id), None)
        _cardinal.telegram.bot.answer_callback_query(call.id, "Проверка устарела, повторите", show_alert=True)
        return
    _cardinal.telegram.bot.answer_callback_query(call.id, "Покупка запущена")
    _edit(call, "⏳ Выполняю подтверждённую покупку LZT...", _back(f"{CBT.DEBUG_ITEM}:{item_id}"))
    threading.Thread(
        target=_purchase_confirm_worker,
        args=(call.message.chat.id, call.message.id, call.from_user.id, item_id, confirmation),
        daemon=True,
        name="lztfp-purchase-confirm",
    ).start()


def _debug_operation_worker(chat_id: int, message_id: int, item_id: str, operation: str) -> None:
    try:
        if operation == "guard":
            payload = LZTAccountOperations.get_guard_code(item_id)
            title = "Steam Guard код"
        elif operation == "confirmations":
            payload = LZTAccountOperations.list_sda_confirmations(item_id)
            title = "Подтверждения SDA"
        elif operation == "email":
            payload = LZTAccountOperations.get_email_code(item_id)
            title = "Код почты"
        elif operation == "letters":
            payload = LZTAccountOperations.get_letters(item_id, limit=5)
            title = "Последние письма"
        elif operation == "mafile":
            payload = LZTAccountOperations.get_mafile(item_id)
            title = "maFile"
        elif operation == "email_password":
            payload = LZTAccountOperations.get_temp_email_password(item_id)
            title = "Пароль временной почты"
        elif operation == "remove_mafile":
            payload = LZTAccountOperations.remove_mafile(item_id)
            title = "Удаление Steam Guard"
        else:
            raise ValueError("неизвестная операция")
        text = f"<b>{html.escape(title)} для #{item_id}</b>\n\n<pre>{_json_preview(payload)}</pre>"
        markup = _debug_item_keyboard(item_id)
        if operation == "confirmations":
            confirmations = payload.get("confirmations", payload.get("items", payload.get("data", []))) if isinstance(payload, dict) else []
            if isinstance(confirmations, dict):
                confirmations = confirmations.get("confirmations", confirmations.get("items", []))
            if isinstance(confirmations, list):
                for entry in confirmations[:10]:
                    if not isinstance(entry, dict) or "id" not in entry or "nonce" not in entry:
                        continue
                    markup.add(B(
                        f"✅ Подтвердить {entry.get('type', entry.get('id'))}",
                        callback_data=f"{CBT.DEBUG_CONFIRM}:{item_id}:{entry['id']}:{entry['nonce']}",
                    ))
    except Exception as exc:
        logger.exception("LZT-FP: debug account operation failed item=%s op=%s", item_id, operation)
        text = f"❌ Ошибка операции: <code>{html.escape(str(exc))}</code>"
        markup = _debug_item_keyboard(item_id)
    try:
        _cardinal.telegram.bot.edit_message_text(text, chat_id, message_id, reply_markup=markup)
    except Exception:
        _cardinal.telegram.bot.send_message(chat_id, text, reply_markup=markup)


def _start_debug_operation(call, operation: str) -> None:
    item_id = call.data.split(":", 1)[1]
    _cardinal.telegram.bot.answer_callback_query(call.id, "Запрос отправлен")
    _edit(call, "⏳ Выполняю запрос к LZT...", _back(f"{CBT.DEBUG_ITEM}:{item_id}"))
    threading.Thread(
        target=_debug_operation_worker,
        args=(call.message.chat.id, call.message.id, item_id, operation),
        daemon=True,
        name=f"lztfp-debug-{operation}",
    ).start()


def _start_dangerous_debug_confirmation(call) -> None:
    parts = call.data.split(":")
    if len(parts) != 3:
        return
    item_id, operation = parts[1:]
    labels = {
        "mafile": "получить maFile",
        "email_password": "получить пароль временной почты",
        "remove_mafile": "удалить Steam Guard",
    }
    label = labels.get(operation)
    if not label:
        return
    text = (
        f"<b>⚠️ Подтвердите действие</b>\n\n"
        f"Вы собираетесь: <code>{html.escape(label)}</code> для аккаунта <code>#{item_id}</code>.\n\n"
        "Получение maFile или пароля временной почты аннулирует гарантию LZT. "
        "Удаление maFile отвяжет Steam Guard и также может сделать аккаунт невосстановимым.\n\n"
        "Продолжать только если вы осознанно принимаете последствия."
    )
    kb = K(row_width=1)
    kb.add(B("✅ Да, выполнить", callback_data=f"{CBT.DEBUG_DANGEROUS_CONFIRM}:{item_id}:{operation}"))
    kb.add(B("❌ Отмена", callback_data=f"{CBT.DEBUG_ITEM}:{item_id}"))
    _edit(call, text, kb)
    _cardinal.telegram.bot.answer_callback_query(call.id)


def _confirm_dangerous_debug(call) -> None:
    parts = call.data.split(":")
    if len(parts) != 3:
        return
    item_id, operation = parts[1:]
    _cardinal.telegram.bot.answer_callback_query(call.id, "Запрос отправлен")
    _edit(call, "⏳ Выполняю подтверждённую операцию LZT...", _back(f"{CBT.DEBUG_ITEM}:{item_id}"))
    threading.Thread(
        target=_debug_operation_worker,
        args=(call.message.chat.id, call.message.id, item_id, operation),
        daemon=True,
        name=f"lztfp-debug-dangerous-{operation}",
    ).start()


def _confirm_debug_sda(call) -> None:
    parts = call.data.split(":")
    if len(parts) != 4:
        return
    item_id, confirmation_id, nonce = parts[1:]
    try:
        payload = LZTAccountOperations.confirm_sda(item_id, confirmation_id, nonce)
        text = (
            f"✅ Подтверждение отправлено для <code>#{item_id}</code>.\n\n"
            "Внимание: подтверждение SDA отменяет активную гарантию LZT.\n\n"
            f"<pre>{_json_preview(payload, 1800)}</pre>"
        )
    except Exception as exc:
        logger.exception("LZT-FP: SDA confirmation failed item=%s", item_id)
        text = f"❌ Не удалось подтвердить SDA: <code>{html.escape(str(exc))}</code>"
    _edit(call, text, _debug_item_keyboard(item_id))
    _cardinal.telegram.bot.answer_callback_query(call.id)


def _extract_code(payload: Any) -> str:
    if isinstance(payload, dict):
        for key in (
            "code", "confirmation_code", "confirmationCode",
            "guard_code", "guardCode", "email_code", "emailCode", "value",
        ):
            value = payload.get(key)
            if value not in (None, ""):
                return str(value)
        for key in ("item", "data", "codes", "codeData", "code_data"):
            value = payload.get(key)
            code = _extract_code(value)
            if code:
                return code
    elif isinstance(payload, list):
        for value in payload:
            code = _extract_code(value)
            if code:
                return code
    return ""


def _customer_capabilities(item_id: str) -> dict[str, Any]:
    """Merge durable capability data with the credentials store.

    The debug inspector can refresh an account and replace the compact
    purchase summary, so customer commands must not rely on one writer's
    representation of the same account.
    """
    account = _load_accounts().get("accounts", {}).get(str(item_id), {})
    raw = account.get("capabilities", {}) if isinstance(account, dict) else {}
    capabilities = dict(raw) if isinstance(raw, dict) else {}
    credentials = _credentials_for_item(item_id)

    if "has_mafile" not in capabilities:
        capabilities["has_mafile"] = bool(
            _int(capabilities.get("steam_mfa"), 0)
            if "steam_mfa" in capabilities else True
        )
    capabilities["has_email_login"] = bool(
        capabilities.get("has_email_login")
        or capabilities.get("has_email_password")
        or capabilities.get("has_email_login_url")
        or capabilities.get("canViewTempEmail")
        or capabilities.get("emailLoginUrl")
        or credentials.get("email_login")
        or credentials.get("email_password")
        or credentials.get("email_login_url")
    )
    return capabilities


def _customer_order_for_message(message: Any) -> dict[str, Any] | None:
    chat_id = str(getattr(message, "chat_id", "") or "")
    author_id = _int(getattr(message, "author_id", 0), 0)
    matches = []
    for record in _load_orders().get("orders", {}).values():
        if not isinstance(record, dict) or record.get("status") not in {"issued", "closed"}:
            continue
        stored_buyer_id = _int(record.get("buyer_id"), 0)
        same_chat = str(record.get("chat_id") or "") == chat_id
        same_buyer = bool(stored_buyer_id and author_id and stored_buyer_id == author_id)
        # FunPay uses two representations for a private chat: the order
        # record may contain a users-* alias while message events contain a
        # numeric CID. The buyer id is the stable identity in both forms.
        if not same_chat and not same_buyer:
            continue
        matches.append(record)
    if not matches:
        return None
    matches.sort(
        key=lambda record: str(record.get("updated_at") or record.get("created_at") or ""),
        reverse=True,
    )
    return matches[0]


def _customer_confirmation_items(payload: Any, depth: int = 0) -> list[dict[str, Any]]:
    """Extract SDA entries without exposing the raw API response to a buyer."""
    if depth > 4:
        return []
    if isinstance(payload, list):
        entries = [entry for entry in payload if isinstance(entry, dict)]
        if entries:
            return entries
        for value in payload:
            entries = _customer_confirmation_items(value, depth + 1)
            if entries:
                return entries
        return []
    if not isinstance(payload, dict):
        return []
    if (
        _customer_confirmation_value(payload, "id", "confirmation_id") not in (None, "")
        and _customer_confirmation_value(payload, "nonce", "confirmation_nonce") not in (None, "")
    ):
        return [payload]
    for key in (
        "confirmations", "confirmation_requests", "requests", "actions",
        "items", "data", "result", "sda", "confirmation", "confirmation_list",
        "confirms", "steam_guard", "steam",
    ):
        if key in payload:
            entries = _customer_confirmation_items(payload[key], depth + 1)
            if entries:
                return entries
    return []


def _customer_confirmation_value(entry: dict[str, Any], *keys: str) -> Any:
    for key in keys:
        value = entry.get(key)
        if value not in (None, ""):
            return value
    return ""


def _customer_confirmation_timestamp(entry: dict[str, Any]) -> float:
    for key in (
        "created_at", "createdAt", "creation_time", "creationTime",
        "timestamp", "time", "date", "created",
    ):
        value = entry.get(key)
        try:
            timestamp = float(value)
        except (TypeError, ValueError):
            continue
        if timestamp > 10_000_000_000:
            timestamp /= 1000
        if timestamp > 0:
            return timestamp
    return 0.0


def _customer_confirmation_matches(entry: dict[str, Any], selector: str) -> bool:
    """Match an optional Steam recovery code without displaying API fields."""
    selector = str(selector or "").strip()
    if not selector:
        return True
    for value in entry.values():
        if isinstance(value, dict) and _customer_confirmation_matches(value, selector):
            return True
        if isinstance(value, list):
            if any(
                _customer_confirmation_matches(item, selector)
                for item in value if isinstance(item, dict)
            ):
                return True
        elif value not in (None, "") and selector in str(value):
            return True
    return False


def _select_customer_confirmation(
    confirmations: list[dict[str, Any]], selector: str = ""
) -> dict[str, Any] | None:
    if selector:
        confirmations = [
            entry for entry in confirmations
            if _customer_confirmation_matches(entry, selector)
        ]
    if not confirmations:
        return None
    timestamped = [
        entry for entry in confirmations
        if _customer_confirmation_timestamp(entry) > 0
    ]
    now = time.time()
    recent = [
        entry for entry in timestamped
        if 0 <= now - _customer_confirmation_timestamp(entry) <= 5 * 60
    ]
    candidates = recent or timestamped or confirmations
    return max(
        candidates,
        key=lambda entry: _customer_confirmation_timestamp(entry),
    ) if timestamped else candidates[0]


def _customer_email_address(item_id: str) -> str:
    credentials = _credentials_for_item(item_id)
    return str(credentials.get("email_login") or "указанной")


def _customer_email_code_not_found(item_id: str) -> str:
    return (
        f"Код для подтверждения не найден на почте {_customer_email_address(item_id)}. "
        "Попробуйте выслать код заново и проверьте, что почта привязана к этому аккаунту "
        "через форму восстановления аккаунта."
    )


def _customer_help_text(record: dict[str, Any]) -> str:
    if _is_valorant_preset_key(str(record.get("preset_key") or "")):
        return "Для данного заказа не предусмотрены текстовые команды."
    capabilities = _customer_capabilities(str(record.get("item_id") or ""))
    lines = [
        "Доступные команды:",
        "!help — показать это сообщение",
    ]
    if capabilities.get("has_mafile", True):
        lines.extend([
            "!sg_code — получить код Steam Guard",
            "!sg_confirm — автоматически подтвердить последнее действие",
            "!sg_delete — запросить удаление аутентификатора",
        ])
    if capabilities.get("has_email_login", False):
        lines.append("!email_code — получить код подтверждения с почты")
    return "\n".join(lines)


def _customer_confirmation_key(message: Any) -> tuple[str, int]:
    return (
        str(getattr(message, "chat_id", "") or ""),
        _int(getattr(message, "author_id", 0), 0),
    )


def _set_customer_delete_confirmation(message: Any, record: dict[str, Any]) -> None:
    with _lock:
        _customer_delete_confirmations[_customer_confirmation_key(message)] = {
            "order_id": str(record.get("order_id") or ""),
            "item_id": str(record.get("item_id") or ""),
            "expires_at": time.time() + CUSTOMER_DELETE_CONFIRMATION_TTL_SECONDS,
        }


def _pop_customer_delete_confirmation(message: Any) -> dict[str, Any] | None:
    with _lock:
        pending = _customer_delete_confirmations.pop(_customer_confirmation_key(message), None)
    if not isinstance(pending, dict):
        return None
    if float(pending.get("expires_at") or 0) < time.time():
        return None
    return pending


def _customer_order_by_id(order_id: str, message: Any) -> dict[str, Any] | None:
    record = _load_orders().get("orders", {}).get(str(order_id))
    if not isinstance(record, dict) or record.get("status") not in {"issued", "closed"}:
        return None
    author_id = _int(getattr(message, "author_id", 0), 0)
    if _int(record.get("buyer_id"), 0) != author_id:
        return None
    return record


def _customer_delete_worker(c: Cardinal, message: Any, record: dict[str, Any]) -> None:
    chat_id = getattr(message, "chat_id", "")
    item_id = str(record.get("item_id") or "")
    try:
        if not _customer_capabilities(item_id).get("has_mafile"):
            c.send_message(chat_id, "Аутентификатор Steam Guard для этого аккаунта уже удалён.")
            return
        LZTAccountOperations.remove_mafile(item_id)
        account_data = _load_accounts()
        account = account_data.get("accounts", {}).get(item_id, {})
        account_capabilities = account.setdefault("capabilities", {})
        account_capabilities["has_mafile"] = False
        account_capabilities["steam_mfa"] = 0
        _save_accounts(account_data)
        c.send_message(chat_id, "✅ Аутентификатор Steam Guard удалён.")
    except Exception:
        logger.exception(
            "LZT-FP: customer authenticator removal failed order=%s item=%s",
            record.get("order_id"), item_id,
        )
        c.send_message(chat_id, "❌ Не удалось удалить аутентификатор. Попробуйте повторить запрос позже.")


def _customer_command_worker(c: Cardinal, message: Any, record: dict[str, Any],
                             command: str, args: str) -> None:
    chat_id = getattr(message, "chat_id", "")
    item_id = str(record.get("item_id") or "")
    capabilities = _customer_capabilities(item_id)
    try:
        if command in {"!sg_code", "!sg-code"}:
            if not capabilities.get("has_mafile"):
                c.send_message(chat_id, "❌ Для этого аккаунта Steam Guard недоступен.")
                return
            payload = LZTAccountOperations.get_guard_code(item_id)
            code = _extract_code(payload)
            c.send_message(chat_id, f"Steam Guard-код: {code or 'не найден'}")
        elif command in {"!sg_confirm", "!sg-confirm"}:
            if not capabilities.get("has_mafile"):
                c.send_message(chat_id, "❌ Для этого аккаунта Steam Guard недоступен.")
                return
            parts = args.split()
            if len(parts) > 1:
                c.send_message(chat_id, "⚠️ Используйте !sg_confirm без параметров или с кодом из окна Steam.")
                return
            payload = LZTAccountOperations.list_sda_confirmations(item_id)
            confirmations = _customer_confirmation_items(payload)
            if isinstance(payload, dict):
                logger.info(
                    "LZT-FP: SDA list response shape item=%s keys=%s entries=%s",
                    item_id, sorted(str(key) for key in payload.keys())[:20], len(confirmations),
                )
            selected = _select_customer_confirmation(confirmations, parts[0] if parts else "")
            if not selected:
                c.send_message(
                    chat_id,
                    "Нет подходящего ожидающего подтверждения. Сначала начните действие в Steam и повторите команду.",
                )
                return
            confirmation_id = _customer_confirmation_value(selected, "id", "confirmation_id")
            nonce = _customer_confirmation_value(selected, "nonce", "confirmation_nonce")
            if confirmation_id in (None, "") or nonce in (None, ""):
                c.send_message(chat_id, "Не удалось определить ожидающее действие. Повторите попытку позже.")
                return
            LZTAccountOperations.confirm_sda(item_id, confirmation_id, nonce)
            c.send_message(chat_id, "✅ Последнее действие Steam Guard подтверждено.")
        elif command in {"!email_code", "!email-code", "!mail_code"}:
            if not capabilities.get("has_email_login"):
                c.send_message(chat_id, "❌ Почтовые функции для этого аккаунта недоступны.")
                return
            payload = LZTAccountOperations.get_email_code(item_id)
            code = _extract_code(payload)
            c.send_message(chat_id, f"Код почты: {code}" if code else _customer_email_code_not_found(item_id))
    except Exception:
        logger.exception(
            "LZT-FP: customer command failed order=%s command=%s item=%s",
            record.get("order_id"), command, item_id,
        )
        if command in {"!sg_code", "!sg-code"}:
            response = "❌ Не удалось получить код Steam Guard. Попробуйте повторить запрос позже."
        elif command in {"!sg_confirm", "!sg-confirm"}:
            response = "❌ Не удалось получить или подтвердить действие Steam Guard. Проверьте данные и повторите попытку."
        else:
            response = _customer_email_code_not_found(item_id)
        try:
            c.send_message(chat_id, response)
        except Exception:
            logger.exception("LZT-FP: failed to send customer command error order=%s", record.get("order_id"))


def process_customer_message(c: Cardinal, event: NewMessageEvent) -> None:
    if not event.message:
        return
    message = event.message
    if getattr(message, "type", None) not in (None, MessageTypes.NON_SYSTEM):
        return
    author_id = _int(getattr(message, "author_id", 0), 0)
    if not author_id or (_cardinal and _cardinal.account and author_id == _cardinal.account.id):
        return
    text = (getattr(message, "text", "") or "").strip()
    if not text:
        return
    if text == "+":
        pending = _pop_customer_delete_confirmation(message)
        if not pending:
            logger.info("LZT-FP: customer delete confirmation ignored: no pending request")
            return
        record = _customer_order_by_id(str(pending.get("order_id") or ""), message)
        if not record or str(record.get("item_id") or "") != str(pending.get("item_id") or ""):
            c.send_message(message.chat_id, "❌ Запрос на удаление устарел. Отправьте !sg_delete заново.")
            return
        threading.Thread(
            target=_customer_delete_worker,
            args=(c, message, record),
            daemon=True,
            name="lztfp-customer-delete",
        ).start()
        return
    parts = text.split(maxsplit=1)
    command = parts[0].lower()
    args = parts[1] if len(parts) > 1 else ""
    logger.info(
        "LZT-FP: customer command received command=%s chat=%s author=%s",
        command, getattr(message, "chat_id", ""), author_id,
    )
    record = _customer_order_for_message(message)
    if not record:
        logger.warning(
            "LZT-FP: customer command ignored: no eligible order chat=%s author=%s",
            getattr(message, "chat_id", ""), author_id,
        )
        return
    logger.info(
        "LZT-FP: customer command routed order=%s status=%s item=%s",
        record.get("order_id"), record.get("status"), record.get("item_id"),
    )
    if command == "!help":
        c.send_message(message.chat_id, _customer_help_text(record))
        return
    if command in {"!sg_delete", "!sg-delete"}:
        capabilities = _customer_capabilities(str(record.get("item_id") or ""))
        if not capabilities.get("has_mafile"):
            c.send_message(message.chat_id, "❌ Для этого аккаунта Steam Guard недоступен.")
            return
        _set_customer_delete_confirmation(message, record)
        c.send_message(
            message.chat_id,
            "⚠️ Вы ТОЧНО уверены, что хотите удалить аутентификатор Steam Guard?\n\n"
            "Если почта окажется недействительной и не будет получать коды, возврат средств будет невозможен.\n\n"
            "Удаляйте аутентификатор только после проверки почты. Если вы всё проверили и уверены, "
            "что хотите удалить Steam Guard, напишите в чат «+».",
        )
        return
    if command not in {
        "!sg_code", "!sg-code", "!sg_confirm", "!sg-confirm",
        "!email_code", "!email-code", "!mail_code",
    }:
        logger.info("LZT-FP: unsupported customer command=%s order=%s", command, record.get("order_id"))
        return
    threading.Thread(
        target=_customer_command_worker,
        args=(c, message, record, command, args),
        daemon=True,
        name=f"lztfp-customer-{command[1:].replace('-', '_')}",
    ).start()


def process_new_order(c: Cardinal, event: NewOrderEvent) -> None:
    order = getattr(event, "order", None)
    if not order or getattr(order, "status", None) != OrderStatuses.PAID:
        return
    order_id = str(getattr(order, "id", "") or "")
    if not order_id:
        return
    existing = _load_orders().get("orders", {}).get(order_id)
    if isinstance(existing, dict):
        return
    lot_id = _resolve_order_lot_id(order)
    if not lot_id:
        logger.warning("LZT-FP: paid order=%s could not be mapped to a unique configured lot", order_id)
        return
    catalog_record = _catalog_record_for_lot(lot_id)
    item_id = _item_id(catalog_record.get("metadata", {})) if catalog_record else ""
    if not item_id:
        record = _save_funpay_order(order, lot_id, None, status="unbound_lot")
        c.send_message(order.chat_id, _order_message("failed"))
        logger.error(
            "LZT-FP: paid order=%s accepted for unbound lot=%s; no LZT purchase started",
            order_id, lot_id,
        )
        return
    try:
        preset_key = _reserve_catalog_item(lot_id, item_id, order_id)
    except Exception as exc:
        _save_funpay_order(order, lot_id, item_id, status="manual_review")
        c.send_message(order.chat_id, _order_message("failed"))
        logger.exception("LZT-FP: paid order=%s could not reserve item=%s", order_id, item_id)
        return
    status = "awaiting_purchase" if SETTINGS.auto_purchase_after_paid else "awaiting_manual_purchase"
    record = _save_funpay_order(order, lot_id, item_id, status=status, preset_key=preset_key)
    if not _send_order_message(order_id, "waiting"):
        logger.error("LZT-FP: failed to send waiting notification order=%s", order_id)
    logger.info(
        "LZT-FP: FunPay order=%s recorded lot=%s item=%s status=%s",
        order_id, lot_id, item_id or "none", record.get("status"),
    )
    if status == "awaiting_purchase":
        threading.Thread(
            target=_auto_purchase_worker,
            args=(order_id, item_id, preset_key),
            daemon=True,
            name="lztfp-auto-purchase",
        ).start()


def process_order_status_changed(c: Cardinal, event: OrderStatusChangedEvent) -> None:
    order = getattr(event, "order", None)
    order_id = str(getattr(order, "id", "") or "") if order else ""
    if not order_id:
        return
    data = _load_orders()
    record = data.get("orders", {}).get(order_id)
    if not isinstance(record, dict):
        return
    status = getattr(order, "status", None)
    if status == OrderStatuses.REFUNDED:
        previous_status = str(record.get("status") or "")
        if previous_status == "refunded":
            return
        item_id = str(record.get("item_id") or "")
        if item_id and previous_status in {
            "awaiting_purchase", "purchase_checking", "awaiting_manual_purchase",
            "auto_refund_pending", "refund_verification_pending", "refund_pending",
        }:
            record["status"] = "refunded"
            _release_catalog_reservation(item_id, order_id)
            message_kind = "refunded"
        elif previous_status in {"purchase_started", "purchase_response_received", "purchase_unknown", "ready", "issued"}:
            record["status"] = "refund_conflict"
            record["refund_conflict_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
            if item_id:
                _update_catalog_item_status(item_id, "manual_review", order_id=order_id)
            message_kind = "refund_conflict"
            logger.error(
                "LZT-FP: refund observed after purchase/delivery started order=%s previous=%s",
                order_id, previous_status,
            )
        else:
            record["status"] = "refunded"
            message_kind = "refunded"
    elif status == OrderStatuses.CLOSED:
        record["status"] = "closed"
        message_kind = "closed"
    else:
        return
    record["updated_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    _save_orders(data)
    if not _send_order_message(order_id, message_kind):
        logger.error("LZT-FP: failed to notify order status order=%s kind=%s", order_id, message_kind)


def post_init(c: Cardinal) -> None:
    """Resume only orders that were safely before the LZT purchase call."""
    _start_balance_monitor()
    _start_catalog_monitor()
    if not SETTINGS.auto_purchase_after_paid:
        return
    orders = _load_orders().get("orders", {})
    if not isinstance(orders, dict):
        return
    for order_id, record in orders.items():
        if not isinstance(record, dict) or record.get("status") not in {"awaiting_purchase", "purchase_checking"}:
            continue
        item_id = str(record.get("item_id") or "")
        if not item_id:
            continue
        operation = _load_purchases().get("operations", {}).get(item_id, {})
        if isinstance(operation, dict) and operation.get("status") in {
            "purchase_started", "purchase_response_received", "purchase_unknown"
        }:
            _send_order_failure(str(order_id), item_id, "после перезапуска обнаружено неопределённое состояние покупки")
            continue
        threading.Thread(
            target=_auto_purchase_worker,
            args=(str(order_id), item_id, str(record.get("preset_key") or _preset_key_for_item(item_id))),
            daemon=True,
            name="lztfp-auto-resume",
        ).start()


def _lot_pool_worker(chat_id: int, message_id: int, preset_key: str) -> None:
    presets = _load_presets()
    preset = presets.get(preset_key, {})
    config = preset.get("funpay", {}) if isinstance(preset, dict) else {}
    lot_ids = config.get("lot_ids", []) if isinstance(config, dict) else []
    expected = _int(config.get("subcategory_id"), 0) if isinstance(config, dict) else 0
    results = []
    try:
        if not _cardinal or not _cardinal.account:
            raise RuntimeError("FunPay API не инициализирован")
        if not isinstance(lot_ids, list):
            raise ValueError("lot_ids должен быть списком")
        if expected <= 0:
            raise ValueError("у пресета не задана FunPay подкатегория")
        lot_ids, missing_lot_ids = _prune_missing_preset_lots(
            presets, preset_key, preset, expected
        )
        results = []
        for lot_id in missing_lot_ids:
            results.append(f"🧹 <code>{lot_id}</code>: отсутствующий ID удалён из базы")
        if not lot_ids:
            results.append("ℹ️ В базе не осталось существующих лотов этого пресета.")
        for raw_id in lot_ids:
            lot_id = _int(raw_id, 0)
            if lot_id <= 0:
                results.append(f"❌ Некорректный ID: <code>{html.escape(str(raw_id))}</code>")
                continue
            try:
                fields = _cardinal.account.get_lot_fields(lot_id)
                actual = getattr(getattr(fields, "subcategory", None), "id", None)
                if expected and actual and int(actual) != expected:
                    results.append(f"⚠️ <code>{lot_id}</code>: категория {actual}, ожидалась {expected}")
                else:
                    results.append(f"✅ <code>{lot_id}</code>: категория {actual or 'не определена'}")
            except Exception as exc:
                logger.warning("LZT-FP: FunPay lot validation failed lot=%s: %s", lot_id, exc)
                results.append(f"❌ <code>{lot_id}</code>: {html.escape(str(exc)[:180])}")
        text = f"<b>Проверка пула: {html.escape(str(preset.get('name', preset_key)))}</b>\n\n" + "\n".join(results)
    except Exception as exc:
        text = f"❌ Ошибка проверки пула: <code>{html.escape(str(exc))}</code>"
    try:
        _cardinal.telegram.bot.edit_message_text(
            text[:4090], chat_id, message_id, reply_markup=_back(f"{CBT.PRESET}:{preset_key}")
        )
    except Exception:
        _cardinal.telegram.bot.send_message(chat_id, text[:4090], reply_markup=_back(f"{CBT.PRESET}:{preset_key}"))


def _start_lot_validation(call) -> None:
    key = call.data.split(":", 1)[1]
    _cardinal.telegram.bot.answer_callback_query(call.id, "Проверка запущена")
    _edit(call, "⏳ Проверяю FunPay lot_ids без сохранения изменений...", _back(f"{CBT.PRESET}:{key}"))
    threading.Thread(
        target=_lot_pool_worker,
        args=(call.message.chat.id, call.message.id, key),
        daemon=True,
        name="lztfp-funpay-lots",
    ).start()


def _lot_sync_worker(chat_id: int, message_id: int, preset_key: str) -> None:
    try:
        with _lot_reconcile_lock:
            bound, disabled, messages = _sync_funpay_lot_pool(preset_key)
        text = (
            f"✅ <b>Пул FunPay обновлён: {html.escape(preset_key)}</b>\n\n"
            f"Заполнено: <code>{bound}</code>\n"
            f"Отключено пустых слотов: <code>{disabled}</code>\n\n"
            + "\n".join(messages)
            + "\n\n<i>Покупка LZT и передача данных клиенту не выполнялись.</i>"
        )
    except Exception as exc:
        logger.error(
            "LZT-FP: FunPay lot pool sync failed preset=%s: %s",
            preset_key,
            _short_exception(exc),
        )
        text = (
            "❌ Ошибка заполнения пула: "
            f"<code>{html.escape(_short_exception(exc))}</code>"
        )
    try:
        _cardinal.telegram.bot.edit_message_text(
            text[:4090], chat_id, message_id, reply_markup=_back(f"{CBT.PRESET}:{preset_key}")
        )
    except Exception as exc:
        logger.warning(
            "LZT-FP: could not edit lot sync message, sending a new one: %s",
            _short_exception(exc),
        )
        try:
            _cardinal.telegram.bot.send_message(
                chat_id, text[:4090], reply_markup=_back(f"{CBT.PRESET}:{preset_key}")
            )
        except Exception:
            logger.exception("LZT-FP: could not send lot sync result message")


def _start_lot_sync(call) -> None:
    preset_key = call.data.split(":", 1)[1]
    _cardinal.telegram.bot.answer_callback_query(call.id, "Обновление запущено")
    _edit(
        call,
        "⏳ Заполняю существующие FunPay-лоты данными из каталога...",
        _back(f"{CBT.PRESET}:{preset_key}"),
    )
    threading.Thread(
        target=_lot_sync_worker,
        args=(call.message.chat.id, call.message.id, preset_key),
        daemon=True,
        name="lztfp-funpay-sync",
    ).start()


def _start_preset_scalar_edit(call, kind: str) -> None:
    key = call.data.split(":")[-1]
    if key not in _load_presets():
        _cardinal.telegram.bot.answer_callback_query(call.id, "Пресет не найден", show_alert=True)
        return
    state_key = (call.message.chat.id, call.from_user.id)
    _temporary[state_key] = {"kind": kind, "preset_key": key}
    message = _cardinal.telegram.bot.send_message(
        call.message.chat.id, _prompt(kind), reply_markup=_back(f"{CBT.PRESET}:{key}")
    )
    _cardinal.telegram.set_state(call.message.chat.id, message.id, call.from_user.id, f"LZTFP_EDIT:{kind}")
    _cardinal.telegram.bot.answer_callback_query(call.id)


def _start_preset_lot_ids_edit(call) -> None:
    key = call.data.split(":", 1)[1]
    preset = _load_presets().get(key)
    if not isinstance(preset, dict):
        _cardinal.telegram.bot.answer_callback_query(call.id, "Пресет не найден", show_alert=True)
        return
    current = ", ".join(str(lot_id) for lot_id in _preset_lot_ids(preset)) or "не заданы"
    prompt = _prompt("preset_lot_ids") + f"\n\nТекущий пул: <code>{html.escape(current)}</code>"
    state_key = (call.message.chat.id, call.from_user.id)
    _temporary[state_key] = {"kind": "preset_lot_ids", "preset_key": key}
    message = _cardinal.telegram.bot.send_message(
        call.message.chat.id, prompt, reply_markup=_back(f"{CBT.PRESET}:{key}")
    )
    _cardinal.telegram.set_state(
        call.message.chat.id, message.id, call.from_user.id, "LZTFP_EDIT:preset_lot_ids"
    )
    _cardinal.telegram.bot.answer_callback_query(call.id)


def _start_preset_json_edit(call, kind: str) -> None:
    key = call.data.split(":", 1)[1]
    presets = _load_presets()
    preset = presets.get(key)
    if not preset:
        _cardinal.telegram.bot.answer_callback_query(call.id, "Пресет не найден", show_alert=True)
        return
    if kind == "preset_funpay":
        current = preset.get("funpay", {})
        state_name = "preset_funpay"
    else:
        current = {"selection_limit": _preset_limit(preset), "markup_percent": _preset_markup(preset)}
        state_name = "preset_finance"
    prompt = "Отправьте JSON:\n<pre>" + html.escape(json.dumps(current, ensure_ascii=False, indent=2)[:3000]) + "</pre>"
    state_key = (call.message.chat.id, call.from_user.id)
    _temporary[state_key] = {"kind": state_name, "preset_key": key}
    message = _cardinal.telegram.bot.send_message(
        call.message.chat.id, prompt, reply_markup=_back(f"{CBT.PRESET}:{key}")
    )
    _cardinal.telegram.set_state(call.message.chat.id, message.id, call.from_user.id, f"LZTFP_EDIT:{state_name}")
    _cardinal.telegram.bot.answer_callback_query(call.id)


def init(cardinal: Cardinal, *args) -> None:
    global _cardinal
    _cardinal = cardinal
    _load_settings()
    _load_presets()
    _load_catalog()
    _load_funpay_settings()
    _load_accounts()
    _load_purchases()
    _load_credentials()
    _load_orders()
    if not cardinal.telegram:
        return
    tg = cardinal.telegram

    def open_main(call):
        _temporary.pop((call.message.chat.id, call.from_user.id), None)
        tg.clear_state(call.message.chat.id, call.from_user.id)
        _edit(call, _main_text(), _main_keyboard())
        tg.bot.answer_callback_query(call.id)

    def open_settings(call):
        _edit(call, _settings_text(), _settings_keyboard())
        tg.bot.answer_callback_query(call.id)

    def open_presets(call):
        _edit(call, "<b>🗂 Категории продаж</b>\n\nВыберите пресет LZT и его настройки.", _presets_keyboard())
        tg.bot.answer_callback_query(call.id)

    def open_funpay(call):
        if call.data == CBT.FUNPAY:
            _edit(call, _funpay_text(), _funpay_keyboard())
            tg.bot.answer_callback_query(call.id)
        elif call.data == CBT.FUNPAY_TEMPLATE_JSON:
            _start_funpay_edit(call)
        else:
            _start_funpay_edit(call)

    def open_debug(call):
        if call.data != CBT.DEBUG:
            return
        item_id = _debug_item_id(call.from_user.id)
        text = _debug_text()
        markup = _debug_keyboard()
        if item_id:
            text += f"\n\nТекущий item_id: <code>{item_id}</code>"
            markup.add(B("🔎 Проверить карточку аккаунта", callback_data=f"{CBT.DEBUG_ITEM}:{item_id}"))
        _edit(call, text, markup)
        tg.bot.answer_callback_query(call.id)

    def open_catalog(call):
        _edit(call, _catalog_text(), _catalog_keyboard())
        tg.bot.answer_callback_query(call.id)

    def open_preset(call):
        parts = call.data.split(":")
        if len(parts) == 3 and parts[1] == "edit":
            _start_preset_edit(call)
            return
        key = parts[1]
        _edit(call, _preset_text(key), _preset_keyboard(key))
        tg.bot.answer_callback_query(call.id)

    def open_finance(call):
        parts = call.data.split(":")
        if len(parts) == 3 and parts[1] == "limit":
            _start_preset_scalar_edit(call, "preset_limit")
        else:
            _start_preset_json_edit(call, "preset_finance")

    def open_lot_template(call):
        parts = call.data.split(":")
        if len(parts) == 2:
            key = parts[1]
            _edit(call, _preset_lot_template_text(key), _preset_lot_template_keyboard(key))
            tg.bot.answer_callback_query(call.id)
        elif len(parts) == 3 and parts[1] == "reset":
            _reset_preset_template(call)

    def open_preset_template_json(call):
        _start_preset_json_edit(call, "preset_funpay")

    tg.cbq_handler(open_main, lambda call: call.data == CBT.MAIN or call.data.startswith(CBT.ROOT))
    tg.cbq_handler(open_settings, lambda call: call.data == CBT.SETTINGS)
    tg.cbq_handler(_toggle_auto_purchase, lambda call: call.data == CBT.AUTO_PURCHASE)
    tg.cbq_handler(open_presets, lambda call: call.data == CBT.PRESETS)
    tg.cbq_handler(open_funpay, lambda call: call.data == CBT.FUNPAY or call.data.startswith(f"{CBT.FUNPAY}:"))
    tg.cbq_handler(_start_funpay_template_field_edit, lambda call: call.data.startswith(f"{CBT.FUNPAY_TEMPLATE_FIELD}:"))
    tg.cbq_handler(open_funpay, lambda call: call.data == CBT.FUNPAY_TEMPLATE_JSON)
    tg.cbq_handler(open_debug, lambda call: call.data == CBT.DEBUG)
    tg.cbq_handler(open_catalog, lambda call: call.data == CBT.CATALOG)
    tg.cbq_handler(_toggle_preset_selling, lambda call: call.data.startswith(f"{CBT.SELLING}:"))
    tg.cbq_handler(open_preset, lambda call: call.data.startswith(f"{CBT.PRESET}:"))
    tg.cbq_handler(open_finance, lambda call: call.data.startswith(f"{CBT.FINANCE}:"))
    tg.cbq_handler(open_lot_template, lambda call: call.data.startswith(f"{CBT.LOT_TEMPLATE}:"))
    tg.cbq_handler(_start_preset_lot_ids_edit, lambda call: call.data.startswith(f"{CBT.LOT_IDS}:"))
    tg.cbq_handler(_start_preset_template_field_edit, lambda call: call.data.startswith(f"{CBT.LOT_TEMPLATE_FIELD}:"))
    tg.cbq_handler(open_preset_template_json, lambda call: call.data.startswith(f"{CBT.LOT_TEMPLATE_JSON}:"))
    tg.cbq_handler(_start_lot_validation, lambda call: call.data.startswith(f"{CBT.LOT_VALIDATE}:"))
    tg.cbq_handler(_start_lot_sync, lambda call: call.data.startswith(f"{CBT.LOT_SYNC}:"))
    tg.cbq_handler(_start_preview, lambda call: call.data.startswith(f"{CBT.PREVIEW}:"))
    tg.cbq_handler(_start_refresh, lambda call: call.data.startswith(f"{CBT.REFRESH}:"))
    tg.cbq_handler(_start_debug_item, lambda call: call.data.startswith(f"{CBT.DEBUG_ITEM}:"))
    tg.cbq_handler(_start_purchase_check, lambda call: call.data.startswith(f"{CBT.PURCHASE_CHECK}:"))
    tg.cbq_handler(_confirm_purchase, lambda call: call.data.startswith(f"{CBT.PURCHASE_CONFIRM}:"))
    tg.cbq_handler(_start_delivery_confirmation, lambda call: call.data.startswith(f"{CBT.DELIVERY}:"))
    tg.cbq_handler(_confirm_delivery, lambda call: call.data.startswith(f"{CBT.DELIVERY_CONFIRM}:"))
    tg.cbq_handler(lambda call: _start_debug_operation(call, "guard"), lambda call: call.data.startswith(f"{CBT.DEBUG_CODE}:"))
    tg.cbq_handler(lambda call: _start_debug_operation(call, "confirmations"), lambda call: call.data.startswith(f"{CBT.DEBUG_CONFIRMATIONS}:"))
    tg.cbq_handler(lambda call: _start_debug_operation(call, "email"), lambda call: call.data.startswith(f"{CBT.DEBUG_EMAIL_CODE}:"))
    tg.cbq_handler(lambda call: _start_debug_operation(call, "letters"), lambda call: call.data.startswith(f"{CBT.DEBUG_LETTERS}:"))
    tg.cbq_handler(_confirm_debug_sda, lambda call: call.data.startswith(f"{CBT.DEBUG_CONFIRM}:"))
    tg.cbq_handler(_start_dangerous_debug_confirmation, lambda call: call.data.startswith(f"{CBT.DEBUG_DANGEROUS}:"))
    tg.cbq_handler(_confirm_dangerous_debug, lambda call: call.data.startswith(f"{CBT.DEBUG_DANGEROUS_CONFIRM}:"))
    tg.cbq_handler(_start_edit, lambda call: call.data.startswith(f"{CBT.EDIT}:"))
    tg.msg_handler(
        _handle_input,
        func=lambda message: any(
            tg.check_state(message.chat.id, message.from_user.id, f"LZTFP_EDIT:{kind}")
            for kind in (
                "token", "language", "proxy", "timeout", "delay", "balance_id", "preset",
                "preset_limit", "preset_finance", "preset_funpay",
                "preset_lot_ids",
                "funpay_template", "funpay_template_field", "preset_template_field",
                "funpay_tags", "funpay_messages", "debug_item",
            )
        ),
    )
    logger.info("LZT-FP: Telegram UI initialized; catalog and account operations ready")


BIND_TO_PRE_INIT = [init]
BIND_TO_POST_INIT = [post_init]
BIND_TO_NEW_ORDER = [process_new_order]
BIND_TO_ORDER_STATUS_CHANGED = [process_order_status_changed]
BIND_TO_NEW_MESSAGE = [process_customer_message]
