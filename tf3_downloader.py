import getpass
import hashlib
import os
import random
import re
import shutil
import sys
import tempfile
import time
import zipfile
import zlib
from collections import deque
from pathlib import Path
from urllib.parse import urlparse, quote, quote_plus


# Проверка версии Python и наличия requests — ДО всего остального.
# Без этой обёртки пользователь при прямом запуске .py (не через
# батник) и без установленного requests получил бы сырой traceback.
if sys.version_info < (3, 11):
    print(
        f"Требуется Python 3.11 или новее. "
        f"У тебя {sys.version_info.major}.{sys.version_info.minor}."
    )
    sys.exit(1)

try:
    import requests
except ModuleNotFoundError:
    print("Не установлен пакет requests.")
    print("Установи его командой: pip install requests")
    sys.exit(1)


VERSION = "0.9.42-BETA"

GAME_ID = 10640
API_BASE = f"https://g-{GAME_ID}.modapi.io/v1"
USER_AGENT = f"TpF3-Mod-Downloader/{VERSION}"

MAX_RETRIES = 3
MAX_DOWNLOAD_RETRIES = 3

MAX_EXTRACT_DIR_LEN = 150
MAX_MOD_PATH_LEN = 200
MAX_PATH_WARNING_THRESHOLD = 240
MAX_FOLDER_NAME_LEN = 60

# Лимиты на количество ФАЙЛОВ в архиве (записи каталогов не считаем).
MAX_ZIP_MEMBERS = 50_000
MAX_ZIP_MEMBERS_WARN = 8_000

DEPENDENCIES_PAGE_LIMIT = 100
MAX_DEPENDENCIES = 25

KNOWN_CDN_SUFFIXES = (
    ".mod.io",
    ".modapi.io",
    ".digitaloceanspaces.com",
)

RETRYABLE_API_STATUSES = (429, 500, 502, 503, 504)

# Платформа, для которой скачиваем файлы (значение заголовка X-Modio-Platform).
# У мода могут быть отдельные файлы под разные платформы (Windows, консоли, Linux).
TARGET_PLATFORM = "windows"

# API-ключ mod.io: по документации — 32 символа.
API_KEY_LENGTH = 32
MAX_KEY_ATTEMPTS = 3


class InvalidApiKeyError(RuntimeError):
    """mod.io не принял API key (HTTP 401)."""

# ---------- Настройки распаковки ----------
EXTRACT_DIR = Path(r"C:\Games\Буфер TpF3")
KEEP_ZIP = True
# ------------------------------------------

# ---------- Статусы распаковки ----------
STATUS_EXTRACTED = "extracted"
STATUS_EXTRACTED_WITH_WARNINGS = "extracted_warnings"
STATUS_ALREADY = "already"
STATUS_CANCELLED = "cancelled"
STATUS_FAILED = "failed"
STATUS_NOT_ZIP = "not_zip"
# ----------------------------------------

# ---------- Режимы ----------
MODE_FILE_ONE = 1
MODE_FILE_ONE_DEPS = 2

MODE_NAME_AUTO = 1
MODE_NAME_MANUAL = 2
# ---------------------------

DEPS_OK = "ok"
DEPS_EXCEEDED = "exceeded"
DEPS_TRUNCATED = "truncated"
DEPS_ERROR = "error"

FETCH_OK = "ok"
FETCH_ERROR = "error"
FETCH_TRUNCATED = "truncated"

# ---------- HTTP-сессия ----------
_SESSION = requests.Session()
_SESSION.headers.update({
    "User-Agent": USER_AGENT,
    "Accept": "application/json",
    "X-Modio-Platform": TARGET_PLATFORM,
})
# ---------------------------------


class ExtractionCancelled(Exception):
    """Пользователь отказался от распаковки."""


class IncompleteDownload(Exception):
    """Соединение закрылось раньше, чем получен весь файл."""


class RetryableDownloadHTTPError(Exception):
    """HTTP-ошибка CDN, которую имеет смысл повторить (429, 5xx)."""

    def __init__(self, status_code, retry_after=None):
        self.status_code = status_code
        self.retry_after = retry_after
        super().__init__(f"CDN HTTP {status_code}")


class DownloadCancelled(Exception):
    """Пользователь отказался от скачивания (файл уже есть)."""


class ExpiredDownloadLink(Exception):
    """Временная ссылка на файл больше не действительна."""


_DELETE = object()

_RESERVED_WIN_NAMES = {
    "CON", "PRN", "AUX", "NUL",
    *(f"COM{i}" for i in range(1, 10)),
    *(f"LPT{i}" for i in range(1, 10)),
}


def safe_int(value):
    """Возвращает int из значения, если это безопасно."""
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    if isinstance(value, str):
        try:
            return int(value)
        except ValueError:
            return None
    return None


def safe_non_negative_int(value):
    """Как safe_int, но отсекает отрицательные значения."""
    result = safe_int(value)
    if result is None or result < 0:
        return None
    return result


def _clean_key(raw):
    """Убирает пробелы и случайные кавычки вокруг ключа."""
    return (raw or "").strip().strip('"').strip("'").strip()


def _prompt_api_key(show_help=True):
    """Запрашивает ключ со скрытым вводом. Может вернуть пустую строку."""
    if show_help:
        print("Ключ при вводе не отображается — это нормально.")
        print("Вводи его точно, без пробелов и кавычек.")
        print(f"Ключ состоит из {API_KEY_LENGTH} символов; взять его можно на https://mod.io/me/access")
        print("Вставь ключ и нажми Enter.")
        print()
    key = _clean_key(getpass.getpass("API key mod.io: "))

    if key:
        print(f"Принято символов: {len(key)}")
        if len(key) != API_KEY_LENGTH:
            print(
                f"Внимание: ожидалось {API_KEY_LENGTH} символов. "
                "Возможно, ключ вставился не полностью."
            )

    return key


def _key_is_valid(api_key):
    """True — mod.io принял ключ, False — ключ не принят (HTTP 401).
    Остальные ошибки (сеть, 5xx, 403) пробрасываются как есть,
    чтобы не выдавать их за «неверный ключ»."""
    try:
        api_get(f"/games/{GAME_ID}/mods", api_key, {"_limit": 1})
    except InvalidApiKeyError:
        return False
    return True


def get_api_key():
    """Возвращает проверенный API-ключ mod.io.

    Сначала пробует переменную MODIO_API_KEY, затем просит ввести ключ
    вручную (скрытый ввод, до MAX_KEY_ATTEMPTS попыток)."""
    env_key = _clean_key(os.environ.get("MODIO_API_KEY"))

    print()
    if env_key:
        print("Проверяю ключ из переменной MODIO_API_KEY...")
        if _key_is_valid(env_key):
            print("Ключ принят.")
            print()
            return env_key

        print("mod.io не принял ключ из переменной MODIO_API_KEY.")
        print("Введи ключ вручную. Саму переменную потом нужно исправить.")
    else:
        print("API key не найден в переменной окружения.")
        print()
        print("Чтобы не вводить его каждый раз, задай переменную MODIO_API_KEY.")
        print("В обычной командной строке: setx MODIO_API_KEY \"ключ\"")
        print("Также можно через настройки Windows - «переменные среды»")
        print("После этого открой новое окно консоли.")
    print()

    for attempt in range(1, MAX_KEY_ATTEMPTS + 1):
        key = _prompt_api_key(show_help=(attempt == 1))

        if not key:
            print("Ключ не введён.")
        else:
            print("Проверяю ключ...")
            if _key_is_valid(key):
                print("Ключ принят.")
                print()
                return key
            print("mod.io не принял этот ключ.")

        if attempt < MAX_KEY_ATTEMPTS:
            print(f"Попробуй ещё раз ({attempt}/{MAX_KEY_ATTEMPTS}).")
            print()

    raise RuntimeError(
        f"API key не принят после {MAX_KEY_ATTEMPTS} попыток.\n"
        "Проверь ключ на https://mod.io/me/access и запусти скрипт заново."
    )


def mask_key(text, api_key):
    """Прячет API key в тексте."""
    if not api_key or len(api_key) < 8:
        return str(text)

    result = str(text)
    result = result.replace(api_key, "***")

    for encoder in (quote, quote_plus):
        encoded = encoder(api_key, safe="")
        if encoded != api_key:
            result = result.replace(encoded, "***")

    return result


def mask_url(url, api_key):
    """Прячет потенциально чувствительные части URL."""
    if not url:
        return url

    try:
        parsed = urlparse(url)
    except Exception:
        return mask_key(url, api_key)

    scheme_host = f"{parsed.scheme}://{parsed.netloc}"

    marker = "/download/"
    if marker in parsed.path:
        prefix = parsed.path.partition(marker)[0] + marker
        return f"{scheme_host}{prefix}<verification-token>"

    safe_path = parsed.path.rpartition("/")[0] + "/"
    return f"{scheme_host}{safe_path}<redacted>"


def host_is_known_cdn(url):
    """Мягкая проверка хоста binary_url."""
    try:
        host = urlparse(url).hostname or ""
    except Exception:
        return False

    host = host.lower()

    for suffix in KNOWN_CDN_SUFFIXES:
        if host == suffix.lstrip(".") or host.endswith(suffix):
            return True

    return False


def get_downloads_dir():
    """Возвращает путь к папке загрузок."""
    home = Path.home()

    for name in ("Downloads", "Загрузки"):
        candidate = home / name
        if candidate.is_dir():
            return candidate

    downloads = home / "Downloads"
    downloads.mkdir(exist_ok=True)
    return downloads


def format_size(num_bytes):
    """Человекочитаемый размер. Делим по сырому значению."""
    size = float(num_bytes)
    for unit in ("Б", "КБ", "МБ", "ГБ"):
        if size < 1024:
            if unit == "Б":
                return f"{int(size)} {unit}"
            return f"{size:.1f} {unit}"
        size /= 1024
    return f"{size:.1f} ТБ"


def file_md5(path):
    """Считает MD5 файла (читаем кусками)."""
    h = hashlib.md5()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def dir_size_bytes(path):
    """Суммарный размер всех файлов в папке."""
    total = 0

    for f in path.rglob("*"):
        try:
            if f.is_file():
                total += f.stat().st_size
        except OSError:
            continue

    return total


def parse_content_length(header_value):
    """Аккуратно парсит Content-Length."""
    if not header_value:
        return None
    try:
        return int(header_value)
    except ValueError:
        return None


def print_progress(text, width=80):
    """Печатает строку прогресса с возвратом каретки."""
    print(f"\r{text:<{width}}", end="", flush=True)


def _print_download_progress(total, filesize):
    """Строка прогресса скачивания: «Скачано: N байт (X%)»."""
    if filesize:
        percent = min(100, total * 100 // filesize)
        print_progress(f"Скачано: {total:,} байт ({percent}%)")
    else:
        print_progress(f"Скачано: {total:,} байт")


def _print_retry_message(error, attempt):
    """Печатает сообщение о повторе скачивания и возвращает паузу.

    Для HTTP-ошибки CDN сообщение и пауза зависят от статуса и
    Retry-After. Для сетевых обрывов — стандартные «5 секунд».
    """
    if isinstance(error, RetryableDownloadHTTPError):
        if error.retry_after is not None:
            wait = max(1, min(error.retry_after, 60))
            print(
                f"CDN просит подождать {wait} сек... "
                f"({attempt}/{MAX_DOWNLOAD_RETRIES})"
            )
            return wait

        if error.status_code == 429:
            wait = 5
            print(
                f"CDN ограничивает частоту запросов, "
                f"повтор через {wait} сек... "
                f"({attempt}/{MAX_DOWNLOAD_RETRIES})"
            )
            return wait

        wait = 5
        print(
            f"CDN временно недоступен, повтор через {wait} сек... "
            f"({attempt}/{MAX_DOWNLOAD_RETRIES})"
        )
        return wait

    wait = 5
    print(
        f"Обрыв связи, повтор через {wait} сек... "
        f"({attempt}/{MAX_DOWNLOAD_RETRIES})"
    )
    return wait


def _is_junk_member(filename):
    """Служебный файл из архива, который не нужно распаковывать."""
    name = filename.replace("\\", "/")

    if name.startswith("__MACOSX/"):
        return True

    lowered = name.lower()
    base = lowered.rsplit("/", 1)[-1]

    if base == ".ds_store":
        return True
    if base == "thumbs.db":
        return True
    if base == "desktop.ini":
        return True
    if base.startswith("._"):
        return True

    return False


def warn_about_old_folders(extract_dir):
    """Ищет .old-папки и остатки tmpXXXX в буфере."""
    if extract_dir is None or not extract_dir.exists():
        return

    old_pattern = re.compile(r"\.old\d*$")
    tmp_pattern = re.compile(r"^tmp[a-z0-9_]{8}$", re.IGNORECASE)

    leftover_old = sorted(
        p for p in extract_dir.iterdir()
        if p.is_dir() and old_pattern.search(p.name)
    )
    leftover_tmp = sorted(
        p for p in extract_dir.iterdir()
        if p.is_dir() and tmp_pattern.match(p.name)
    )

    if not leftover_old and not leftover_tmp:
        return

    print("=" * 60)
    print("Остатки от прошлых запусков")
    print("=" * 60)

    if leftover_old:
        print()
        print("Старые версии модов (не удалось удалить после замены):")
        for p in leftover_old:
            print(f"  {p}")
        print()
        print("Если не нужно — удали вручную.")
        print("Если нужно восстановить — переименуй, убрав \".old\" из имени.")

    if leftover_tmp:
        print()
        print("Временные папки (процесс был завершён жёстко):")
        for p in leftover_tmp:
            print(f"  {p}")
        print()
        print("Это недоделанная распаковка, безопасно удалить вручную.")

    print("=" * 60)
    print()


# ---------- Санитайз и валидация имени папки ----------

def sanitize_folder_name(raw):
    """Приводит имя из mod.io к безопасному виду."""
    forbidden = '\\/:*?"<>|'
    result = "".join("_" if (c in forbidden or c == " ") else c for c in raw)
    result = re.sub(r"_+", "_", result).strip("_")
    was_changed = (result != raw)
    return result, was_changed


def sanitize_zip_filename(name):
    """Чистит имя ZIP-файла."""
    forbidden = '\\/:*?"<>|'
    cleaned = "".join(
        "_" if (c in forbidden or ord(c) < 32) else c
        for c in name
    )

    stem, dot, ext = cleaned.rpartition(".")
    if dot and ext:
        stem = stem.rstrip(". ")
        cleaned = f"{stem}{dot}{ext}" if stem else f"mod{dot}{ext}"
    else:
        cleaned = cleaned.rstrip(". ")

    if not cleaned:
        return "mod.zip"

    if is_reserved_name(cleaned):
        cleaned = f"mod_{cleaned}"

    return cleaned


def truncate_at_boundary(name, limit):
    """Обрезает имя до limit символов по границе слова."""
    if len(name) <= limit:
        return name

    if name[limit] == "_":
        return name[:limit].rstrip(". _")

    cut = name[:limit].rfind("_")
    if cut > 0:
        return name[:cut].rstrip(". _")

    return name[:limit].rstrip(". _")


def is_reserved_name(name):
    """Зарезервировано ли имя в Windows."""
    stem = name.split(".")[0].upper()
    return stem in _RESERVED_WIN_NAMES


def validate_folder_name(name):
    """Проверяет имя папки на валидность Windows."""
    if not name:
        return "Имя не может быть пустым."

    if name in (".", ".."):
        return "Имя '.' или '..' использовать нельзя."

    forbidden = '\\/:*?"<>|'
    bad_chars = sorted(set(c for c in name if c in forbidden))

    if bad_chars:
        chars_str = " ".join(bad_chars)
        return (
            f"В имени есть недопустимые символы: {chars_str}\n"
            f"Запрещено в Windows: \\ / : * ? \" < > |"
        )

    control_chars = [c for c in name if ord(c) < 32]
    if control_chars:
        return (
            "В имени есть управляющие символы (код < 32), "
            "Windows их не разрешает."
        )

    if name.endswith(".") or name.endswith(" "):
        return (
            "Имя заканчивается точкой или пробелом — Windows это не разрешает.\n"
            "Убери их с конца."
        )

    if len(name) > MAX_FOLDER_NAME_LEN:
        return (
            f"Слишком длинное имя ({len(name)} символов, "
            f"максимум {MAX_FOLDER_NAME_LEN})."
        )

    if is_reserved_name(name):
        return (
            f"Имя \"{name}\" зарезервировано в Windows.\n"
            "Зарезервированы: CON, PRN, AUX, NUL, COM1-9, LPT1-9."
        )

    return None


def ask_folder_name(archive_name, intro=None):
    """Спрашивает имя папки у пользователя."""
    print()
    if intro is None:
        print("Название папки для мода")
    else:
        print(intro)

    print(f"(Enter без ввода — оставить как в архиве: {archive_name})")

    while True:
        name = input("> ").strip()

        if not name:
            archive_error = validate_folder_name(archive_name)
            if archive_error:
                print()
                print("Имя из архива не подходит как имя папки:")
                print(archive_error)
                print("Введи имя вручную.")
                continue
            return archive_name

        error = validate_folder_name(name)
        if error:
            print()
            print(error)
            continue

        return name


def resolve_folder_name(archive_name, mod_name, name_mode):
    """Определяет имя папки для распаковки."""
    if name_mode == MODE_NAME_MANUAL:
        return ask_folder_name(archive_name)

    if not mod_name:
        return ask_folder_name(
            archive_name,
            intro=(
                "Не удалось получить официальное название мода с mod.io.\n"
                "Введи имя вручную."
            ),
        )

    sanitized, _ = sanitize_folder_name(mod_name)

    if not sanitized:
        return ask_folder_name(
            archive_name,
            intro=(
                f"Официальное имя \"{mod_name}\" после обработки стало пустым.\n"
                "Введи имя вручную."
            ),
        )

    sanitized = sanitized.rstrip(". ")

    error = validate_folder_name(sanitized)

    if error and len(sanitized) <= MAX_FOLDER_NAME_LEN:
        return ask_folder_name(
            archive_name,
            intro=(
                f"Официальное имя \"{mod_name}\" не годится как имя папки:\n"
                f"{error}\n"
                "Введи имя вручную."
            ),
        )

    if len(sanitized) > MAX_FOLDER_NAME_LEN:
        truncated = truncate_at_boundary(sanitized, MAX_FOLDER_NAME_LEN)

        if not truncated:
            return ask_folder_name(
                archive_name,
                intro=(
                    "Официальное имя после обрезки стало пустым.\n"
                    "Введи имя вручную."
                ),
            )

        error = validate_folder_name(truncated)
        if error:
            return ask_folder_name(
                archive_name,
                intro=(
                    f"Официальное имя после обрезки не годится:\n{error}\n"
                    "Введи имя вручную."
                ),
            )

        print()
        print(
            f"Официальное имя длиннее {MAX_FOLDER_NAME_LEN} символов "
            f"(было {len(sanitized)}), обрезано до:"
        )
        print(f"  {truncated}")
        return truncated

    return sanitized


# ---------- Диалоги стартового окна ----------

def check_extract_dir(extract_dir):
    """Проверяет путь до буфера и что папку можно открыть.
    Делается ДО скачивания — чтобы не тратить трафик зря."""
    path_str = str(extract_dir)
    if len(path_str) > MAX_EXTRACT_DIR_LEN:
        raise RuntimeError(
            f"Путь к буферу распаковки слишком длинный "
            f"({len(path_str)} символов, максимум {MAX_EXTRACT_DIR_LEN}).\n"
            "Windows может не справиться с путями к файлам внутри мода.\n"
            "Сократи EXTRACT_DIR или перенеси буфер ближе к корню диска."
        )

    try:
        extract_dir.mkdir(parents=True, exist_ok=True)
    except OSError as e:
        raise RuntimeError(
            f"Не удалось создать/открыть папку распаковки:\n"
            f"  {extract_dir}\n"
            f"Причина: {e}"
        ) from e


def ask_file_mode():
    """Стартовое окно — выбор режима работы с файлами."""
    print("Выбери режим работы:")
    print(f"  {MODE_FILE_ONE} — один файл без зависимостей")
    print(f"  {MODE_FILE_ONE_DEPS} — один файл с зависимостями")
    print("  3 — несколько файлов (в разработке)")
    print()

    while True:
        choice = input("> ").strip()

        if choice == str(MODE_FILE_ONE):
            return MODE_FILE_ONE

        if choice == str(MODE_FILE_ONE_DEPS):
            print()
            print("=" * 60)
            print("Режим с зависимостями!")
            print("=" * 60)
            print("Этот режим рассчитан только на докачку базовых зависимостей.")
            print(f"Максимум: {MAX_DEPENDENCIES} штук.")
            print("Большие деревья зависимостей не поддерживаются.")
            print("Перед скачиванием скрипт обойдёт всё дерево зависимостей;")
            print("если их окажется больше лимита — установка приостановится.")
            print("=" * 60)
            print()
            return MODE_FILE_ONE_DEPS

        if choice == "3":
            print("Этот режим в данной версии не реализован,")
            print("но он, скорее всего, появится ближе к релизной v1.1.0.")
            print("Пока что выбери 1 или 2.")
            continue

        print("Непонятный ответ. Введи 1 или 2.")


def ask_name_mode():
    """Стартовое окно — выбор режима работы с именем папки."""
    print()
    print("Как выбирать имя папки для мода:")
    print(f"  {MODE_NAME_AUTO} — автоматически (название с mod.io)")
    print(f"  {MODE_NAME_MANUAL} — вручную")
    print()

    while True:
        choice = input("> ").strip()

        if choice == str(MODE_NAME_AUTO):
            return MODE_NAME_AUTO
        if choice == str(MODE_NAME_MANUAL):
            return MODE_NAME_MANUAL

        print("Непонятный ответ. Введи 1 или 2.")


# ---------- Работа с API ----------

def get_mod_slug(url):
    """Достаёт slug мода из ссылки на mod.io."""
    url = url.strip().strip("\"'`<>()[]{}")

    if "://" not in url:
        url = "https://" + url

    parsed = urlparse(url)

    host = (parsed.hostname or "").lower()
    if host != "mod.io" and not host.endswith(".mod.io"):
        raise ValueError(
            f"Это не ссылка mod.io: {host or '(пусто)'}\n"
            "Нужен URL вида:\n"
            "https://mod.io/g/transportfever3/m/название-мода"
        )

    match = re.fullmatch(r"/g/([^/]+)/m/([^/]+)(?:/.*)?", parsed.path)

    if not match:
        raise ValueError(
            "Не удалось разобрать ссылку.\n"
            "Нужен URL вида:\n"
            "https://mod.io/g/transportfever3/m/название-мода"
        )

    game_slug = match.group(1)
    mod_slug = match.group(2)

    if game_slug.lower() != "transportfever3":
        raise ValueError(
            f"Это не ссылка на Transport Fever 3: {game_slug}"
        )

    mod_slug = mod_slug.strip("\"'`<>()[]{}.,")

    if not mod_slug:
        raise ValueError(
            "Ссылка обрывается: не хватает названия мода.\n"
            "Нужен URL вида:\n"
            "https://mod.io/g/transportfever3/m/название-мода"
        )

    return mod_slug


def api_get(path, api_key, params=None):
    """GET-запрос к API mod.io с ретраями."""
    params = dict(params or {})
    params["api_key"] = api_key

    for attempt in range(1, MAX_RETRIES + 1):
        try:
            response = _SESSION.get(
                API_BASE + path,
                params=params,
                timeout=(10, 80),
            )
        except requests.exceptions.RequestException as e:
            if attempt < MAX_RETRIES:
                print(f"Сетевая ошибка, повтор через 2 сек... ({attempt}/{MAX_RETRIES})")
                time.sleep(2)
                continue

            raise RuntimeError(
                "Не удалось связаться с mod.io:\n" + mask_key(e, api_key)
            ) from None

        if response.status_code in RETRYABLE_API_STATUSES and attempt < MAX_RETRIES:
            raw = response.headers.get("Retry-After", "")
            try:
                wait = int(raw)
            except (ValueError, TypeError):
                wait = 5 * attempt

            wait = max(1, min(wait, 60))
            print(f"mod.io просит подождать, повтор через {wait} сек... ({attempt}/{MAX_RETRIES})")
            time.sleep(wait)
            continue

        if response.status_code == 401:
            raise InvalidApiKeyError(
                "mod.io не принял API key (HTTP 401):\n"
                f"{mask_key(response.text[:2000], api_key)}"
            )

        if response.status_code != 200:
            raise RuntimeError(
                f"mod.io вернул HTTP {response.status_code}:\n"
                f"{mask_key(response.text[:2000], api_key)}"
            )

        try:
            return response.json()
        except ValueError:
            preview = response.text[:300].replace("\n", " ").replace("\r", "")
            raise RuntimeError(
                f"mod.io вернул не-JSON (HTTP {response.status_code}).\n"
                f"Начало ответа: {preview}"
            ) from None


def _platform_entries(item):
    """Список (ПЛАТФОРМА, статус) из поля platforms файла.
    Пустой, если игра не использует платформы или поле имеет другой вид."""
    result = []
    platforms = item.get("platforms") if isinstance(item, dict) else None

    if not isinstance(platforms, list):
        return result

    for entry in platforms:
        if not isinstance(entry, dict):
            continue

        name = str(entry.get("platform") or "").strip().upper()

        if name:
            result.append((name, entry.get("status")))

    return result


def _platforms_text(item):
    """«WINDOWS, LINUX» — платформы файла для вывода на экран."""
    names = []

    for name, _ in _platform_entries(item):
        if name not in names:
            names.append(name)

    return ", ".join(names)


def _file_fits_target(item):
    """True — файл подходит или платформы у него не указаны (проверять нечего).
    False — платформы указаны, но нашей среди них нет (или она отклонена)."""
    entries = _platform_entries(item)

    if not entries:
        return True

    for name, status in entries:
        if name in (TARGET_PLATFORM.upper(), "ALL") and status != 2:  # 2 = DENIED
            return True

    return False


def _live_file_id_for_target(mod):
    """ID файла, который mod.io считает «живым» для нашей платформы.
    Берётся из mod['platforms'] (есть, только если игра включила платформы)."""
    platforms = mod.get("platforms") if isinstance(mod, dict) else None

    if not isinstance(platforms, list):
        return None

    fallback = None

    for entry in platforms:
        if not isinstance(entry, dict):
            continue

        name = str(entry.get("platform") or "").strip().upper()
        file_id = safe_non_negative_int(entry.get("modfile_live"))

        if not file_id:
            continue

        if name == TARGET_PLATFORM.upper():
            return file_id

        if name == "ALL" and fallback is None:
            fallback = file_id

    return fallback


def _find_target_file(mod_id, api_key):
    """Ищет среди файлов мода самый свежий файл для нашей платформы."""
    data = api_get(
        f"/games/{GAME_ID}/mods/{mod_id}/files",
        api_key,
        {"_limit": 100},
    )

    files = data.get("data") if isinstance(data, dict) else None

    if not isinstance(files, list):
        return None

    best = None

    for item in files:
        # Без сведений о платформах нельзя утверждать, что файл для Windows.
        if not _platform_entries(item) or not _file_fits_target(item):
            continue

        added = safe_non_negative_int(item.get("date_added")) or 0

        if best is None or added > best[0]:
            best = (added, item)

    return best[1] if best else None


def _ask_yes_no(question):
    """Вопрос да/нет. EOFError пробрасывается наружу."""
    while True:
        answer = input(f"{question} (y/n): ").strip().lower()

        if answer in ("y", "yes", "д", "да"):
            return True

        if answer in ("n", "no", "н", "нет"):
            return False

        print("Ответь y или n.")


def resolve_file_info(mod, mod_id, api_key, ask=True):
    """Выбирает файл мода для нашей платформы. Возвращает (file_id, file_info).

    Если подходящего файла нет и пользователь отказался скачивать
    «не тот» файл, возвращает (None, None)."""
    file_id = get_current_file_id(mod, api_key)
    file_info = fetch_file_info(mod_id, file_id, api_key)

    if _file_fits_target(file_info):
        return file_id, file_info

    print()
    print(
        f"Текущий файл мода ({file_info.get('filename')}) "
        f"помечен для: {_platforms_text(file_info)}."
    )
    print(f"Ищу среди файлов мода версию для {TARGET_PLATFORM.capitalize()}...")

    other = _find_target_file(mod_id, api_key)
    other_id = safe_non_negative_int(other.get("id")) if other else None

    if other_id:
        other_info = fetch_file_info(mod_id, other_id, api_key)
        print(f"Найден файл: {other_info.get('filename')}")
        return other_id, other_info

    print(f"Файл для {TARGET_PLATFORM.capitalize()} не найден.")

    if ask and not _ask_yes_no("Всё равно скачать текущий файл?"):
        return None, None

    return file_id, file_info


def get_current_file_id(mod, api_key):
    """Достаёт ID текущего файла мода (для нашей платформы, если она известна)."""
    live_id = _live_file_id_for_target(mod)

    if live_id:
        return live_id

    modfile = mod.get("modfile")

    if isinstance(modfile, dict):
        file_id = safe_non_negative_int(modfile.get("id"))
    else:
        file_id = safe_non_negative_int(modfile)

    if not file_id:
        print("Получаю сведения о текущем файле...")

        mod_id = safe_non_negative_int(mod.get("id"))
        if mod_id is None:
            raise RuntimeError(
                "mod.io вернул мод без числового id."
            )

        details = api_get(
            f"/games/{GAME_ID}/mods/{mod_id}",
            api_key,
        )

        if not isinstance(details, dict):
            raise RuntimeError(
                "mod.io вернул неожиданный формат ответа для мода."
            )

        modfile = details.get("modfile")

        if isinstance(modfile, dict):
            file_id = safe_non_negative_int(modfile.get("id"))
        else:
            file_id = safe_non_negative_int(modfile)

    if not file_id:
        raise RuntimeError(
            "У мода не найден текущий modfile."
        )

    return file_id


def fetch_file_info(mod_id, file_id, api_key):
    """Спрашивает у mod.io свежие данные о файле."""
    return api_get(
        f"/games/{GAME_ID}/mods/{mod_id}/files/{file_id}",
        api_key,
    )


def fetch_dependencies_once(mod_id, api_key):
    """Запрашивает прямые зависимости одного мода."""
    try:
        data = api_get(
            f"/games/{GAME_ID}/mods/{mod_id}/dependencies",
            api_key,
            {"_limit": DEPENDENCIES_PAGE_LIMIT},
        )
    except Exception as e:
        print(f"Не удалось получить список зависимостей: {mask_key(e, api_key)}")
        return [], FETCH_ERROR

    if not isinstance(data, dict):
        print("mod.io вернул неожиданный формат ответа для зависимостей.")
        return [], FETCH_ERROR

    items = data.get("data") or []
    if not isinstance(items, list):
        print("mod.io вернул неожиданный формат списка зависимостей.")
        return [], FETCH_ERROR

    total = safe_non_negative_int(data.get("result_total"))

    if total is not None and total > len(items):
        print(
            f"ВНИМАНИЕ: mod.io отдал {len(items)} зависимостей "
            f"из {total} — ответ обрезан."
        )
        return items, FETCH_TRUNCATED

    if total is None and len(items) >= DEPENDENCIES_PAGE_LIMIT:
        print(
            f"ВНИМАНИЕ: mod.io вернул ровно {DEPENDENCIES_PAGE_LIMIT} "
            "зависимостей — упёрлись в потолок запроса."
        )
        return items, FETCH_TRUNCATED

    return items, FETCH_OK


def collect_all_dependencies(root_mod_id, api_key):
    """BFS-обход дерева зависимостей."""
    seen = {root_mod_id}
    queue = deque([root_mod_id])
    result = []
    had_errors = False
    truncated = False

    while queue:
        current_id = queue.popleft()
        deps, status = fetch_dependencies_once(current_id, api_key)

        if status == FETCH_ERROR:
            had_errors = True
            break

        if status == FETCH_TRUNCATED:
            truncated = True
            break

        for dep in deps:
            if not isinstance(dep, dict):
                continue

            # Явная проверка is None: 0 как id отсекаем тоже, но
            # без магии "or" — если mod_id вернулся 0, это ошибка,
            # а не повод молча прыгнуть на "id".
            dep_id = safe_non_negative_int(dep.get("mod_id"))
            if dep_id is None:
                dep_id = safe_non_negative_int(dep.get("id"))

            if not dep_id or dep_id in seen:
                continue

            seen.add(dep_id)

            dep_display = (
                dep.get("name")
                or dep.get("name_id")
                or str(dep_id)
            )
            result.append((dep_id, dep_display))
            queue.append(dep_id)

            if len(result) > MAX_DEPENDENCIES:
                return DEPS_EXCEEDED, result

    if had_errors:
        return DEPS_ERROR, []

    if truncated:
        return DEPS_TRUNCATED, []

    return DEPS_OK, result


def _is_valid_zip_by_md5(path, expected_md5):
    """Файл существует и MD5 совпадает. OSError → False.

    Явная проверка типа: если mod.io вернёт не строку (например,
    случайно int или None), .lower() упал бы с AttributeError.
    """
    if not path.is_file():
        return False
    if not isinstance(expected_md5, str) or not expected_md5:
        return False

    try:
        actual_md5 = file_md5(path)
    except OSError:
        return False

    return actual_md5.lower() == expected_md5.lower()


def _fix_zip_member_encoding(member):
    """Правит кодировку имени внутри ZIP.

    Многие архиваторы пишут имена UTF-8 БЕЗ флага 0x800
    (Info-ZIP, macOS). Старые WinRAR пишут cp1251 без флага.
    Сначала пробуем строгий UTF-8, потом cp1251.
    """
    if member.flag_bits & 0x800:
        return

    try:
        raw = member.filename.encode("cp437")
    except UnicodeEncodeError:
        return

    try:
        member.filename = raw.decode("utf-8")
        return
    except UnicodeDecodeError:
        pass

    try:
        candidate = raw.decode("cp1251")
    except UnicodeDecodeError:
        return

    if any("\u0400" <= c <= "\u04ff" for c in candidate):
        member.filename = candidate


def find_existing_valid_zip(file_info, output_dir, fallback_name):
    """Ищет валидный ZIP, включая копии с суффиксами _1, _2, ..."""
    filename = file_info.get("filename")
    if not filename:
        return None

    filehash = file_info.get("filehash")
    expected_md5 = filehash.get("md5") if isinstance(filehash, dict) else None

    if not expected_md5:
        return None

    safe_name = sanitize_zip_filename(Path(filename).name or fallback_name)

    original = output_dir / safe_name
    if _is_valid_zip_by_md5(original, expected_md5):
        return original

    stem = Path(safe_name).stem
    suffix = Path(safe_name).suffix or ".zip"

    for candidate in sorted(
        output_dir.glob(f"{glob_escape(stem)}_*{glob_escape(suffix)}")
    ):
        if _is_valid_zip_by_md5(candidate, expected_md5):
            return candidate

    return None


def glob_escape(pattern):
    """Экранирует спецсимволы glob ([, ], ?) в строке."""
    import glob as _glob
    return _glob.escape(pattern)


def _check_zip_path_length(path):
    """Проверяет длину пути до ZIP-файла (или .part)."""
    path_str = str(path)
    if len(path_str) > MAX_MOD_PATH_LEN:
        raise RuntimeError(
            f"Путь до ZIP-файла слишком длинный "
            f"({len(path_str)} символов, максимум {MAX_MOD_PATH_LEN}).\n"
            f"Файл: {path_str}\n"
            "Windows может не справиться с таким путём."
        )


def download_zip(file_info, output_dir, fallback_name, api_key=None):
    """Скачивает ZIP во временный .part, проверяет размер и MD5,
    потом переименовывает. При обрыве сети — несколько попыток.

    Возвращает (путь_к_zip, was_skipped).
    """
    output_dir.mkdir(parents=True, exist_ok=True)

    existing = find_existing_valid_zip(file_info, output_dir, fallback_name)
    if existing is not None:
        print()
        print("ZIP уже скачан ранее и совпадает по MD5:")
        print(f"  {existing}")
        print("Пропускаю скачивание.")
        return existing, True

    filename = file_info.get("filename")
    download = file_info.get("download") or {}
    binary_url = download.get("binary_url")
    date_expires = safe_non_negative_int(download.get("date_expires"))

    if not filename or not binary_url:
        raise RuntimeError(
            "mod.io не вернул binary_url для этого файла."
        )

    filesize = safe_non_negative_int(file_info.get("filesize"))
    filehash = file_info.get("filehash")
    expected_md5 = filehash.get("md5") if isinstance(filehash, dict) else None

    print()
    print("-" * 60)
    print(f"ZIP      : {filename}")
    if filesize is not None:
        print(f"Размер   : {filesize:,} байт")
    else:
        print("Размер   : неизвестен")

    if date_expires:
        print(
            "Ссылка до:",
            time.strftime(
                "%Y-%m-%d %H:%M:%S",
                time.localtime(date_expires),
            ),
        )

    print("-" * 60)
    print()
    print("Временная ссылка получена:")
    print(mask_url(binary_url, api_key))

    if not host_is_known_cdn(binary_url):
        try:
            host = urlparse(binary_url).hostname or "?"
        except Exception:
            host = "?"
        print()
        print(f"ВНИМАНИЕ: ссылка ведёт на нестандартный хост: {host}")
        print("Обычно mod.io отдаёт файлы со своих CDN. Продолжаю скачивание,")
        print("но если что-то смущает — можно прервать (Ctrl+C).")
    print()

    raw_name = Path(filename).name or fallback_name
    safe_name = sanitize_zip_filename(raw_name)

    output_path = output_dir / safe_name
    tmp_path = output_dir / (safe_name + ".part")

    _check_zip_path_length(tmp_path)

    if output_path.exists():
        if not output_path.is_file():
            raise RuntimeError(
                f"По пути {output_path} находится папка, а не файл.\n"
                "Скрипт не может использовать её как ZIP.\n"
                "Переименуй или удали эту папку и запусти снова."
            )

        if expected_md5:
            print("ZIP с таким именем уже есть, но MD5 не совпадает:")
        else:
            print("ZIP с таким именем уже есть (MD5 не проверялся):")
        print(f"  {output_path}")

        print()
        print("Что делать?")
        print("  1 — перезаписать")
        print("  2 — сохранить рядом с другим именем (суффикс _1, _2, ...)")
        print("  3 — отменить")
        choice = input("> ").strip()

        if choice == "2":
            i = 1
            while True:
                candidate = output_dir / f"{output_path.stem}_{i}{output_path.suffix}"
                if not candidate.exists():
                    break
                i += 1

            print(f"Новое имя: {candidate.name}")
            output_path = candidate
            tmp_path = output_dir / (output_path.name + ".part")

            _check_zip_path_length(tmp_path)

        elif choice == "1":
            pass

        else:
            print("Считаю отменой.")
            raise DownloadCancelled("Скачивание отменено пользователем.")

    print()
    print("Скачивание в:")
    print(output_path)
    print()

    last_error = None

    for attempt in range(1, MAX_DOWNLOAD_RETRIES + 1):
        md5 = hashlib.md5()
        total = 0
        server_size = None

        try:
            if attempt == 1:
                print_progress("Подключаюсь к серверу загрузки...")
            else:
                print_progress(
                    "Подключаюсь к серверу загрузки "
                    f"(попытка {attempt}/{MAX_DOWNLOAD_RETRIES})..."
                )

            with _SESSION.get(
                binary_url,
                headers={
                    "Accept-Encoding": "identity",
                    "Accept": "*/*",
                },
                stream=True,
                timeout=(15, 90),
            ) as response:

                if response.status_code in (401, 403):
                    raise ExpiredDownloadLink(
                        f"сервер ответил HTTP {response.status_code}"
                    )

                if response.status_code == 429 or response.status_code >= 500:
                    retry_after = None
                    if response.status_code == 429:
                        raw_ra = response.headers.get("Retry-After", "")
                        try:
                            retry_after = int(raw_ra)
                        except (ValueError, TypeError):
                            retry_after = None
                    raise RetryableDownloadHTTPError(
                        response.status_code, retry_after
                    )

                if response.status_code != 200:
                    raise RuntimeError(
                        f"CDN ответил HTTP {response.status_code} "
                        "(подробности URL скрыты — там может быть токен ссылки)"
                    )

                server_size = parse_content_length(
                    response.headers.get("Content-Length")
                )

                if (
                    server_size is not None
                    and filesize is not None
                    and server_size != filesize
                ):
                    raise RuntimeError(
                        f"Файл на сервере изменился: ожидалось {filesize:,} байт, "
                        f"сервер отдаёт {server_size:,} байт.\n"
                        "Скорее всего, автор только что обновил мод. "
                        "Запусти скрипт ещё раз."
                    )

                print_progress("Соединение установлено, жду данные...")

                last_update = 0.0
                with open(tmp_path, "wb") as f:
                    for chunk in response.iter_content(chunk_size=64 * 1024):
                        if not chunk:
                            continue

                        f.write(chunk)
                        md5.update(chunk)
                        total += len(chunk)

                        now = time.monotonic()
                        if now - last_update >= 0.2:
                            last_update = now
                            _print_download_progress(total, filesize)

                _print_download_progress(total, filesize)

            if filesize is not None and total != filesize:
                raise IncompleteDownload(
                    f"получено {total:,} из {filesize:,} байт (по метаданным mod.io)"
                )

            if server_size is not None and total != server_size:
                raise IncompleteDownload(
                    f"получено {total:,} из {server_size:,} байт "
                    "(по заголовку сервера)"
                )

            print()
            print()
            break

        except (RetryableDownloadHTTPError,
                requests.exceptions.ConnectionError,
                requests.exceptions.Timeout,
                requests.exceptions.ChunkedEncodingError,
                IncompleteDownload) as e:
            # Один общий обработчик для всех retryable-ошибок.
            # Сообщение о повторе печатает _print_retry_message.
            last_error = e
            print()
            if attempt < MAX_DOWNLOAD_RETRIES:
                wait = _print_retry_message(e, attempt)
                time.sleep(wait)
                continue

            try:
                tmp_path.unlink(missing_ok=True)
            except OSError:
                pass
            raise RuntimeError(
                f"Не удалось скачать после {MAX_DOWNLOAD_RETRIES} попыток.\n"
                "Проверь соединение и запусти скрипт ещё раз."
            ) from last_error

        except requests.exceptions.RequestException as e:
            # Прочие ошибки requests (InvalidURL, MissingSchema,
            # битая схема). Не retryable — падаем сразу, но маскируем
            # binary_url в тексте, там может быть токен.
            try:
                tmp_path.unlink(missing_ok=True)
            except OSError:
                pass

            msg = str(e)
            if binary_url:
                safe = mask_url(binary_url, api_key)
                msg = msg.replace(binary_url, safe)

            raise RuntimeError(
                f"Ошибка обращения к CDN:\n{msg}"
            ) from None

        except BaseException:
            try:
                tmp_path.unlink(missing_ok=True)
            except OSError:
                pass
            raise

    try:
        if expected_md5:
            if md5.hexdigest().lower() != expected_md5.lower():
                raise RuntimeError(
                    "Контрольная сумма MD5 не совпала — файл повреждён при загрузке.\n"
                    "Попробуй скачать ещё раз."
                )
            print("Проверка MD5: OK")
        else:
            print("Проверка MD5: пропущена (mod.io не передал хэш)")

        tmp_path.replace(output_path)
    except BaseException:
        try:
            tmp_path.unlink(missing_ok=True)
        except OSError:
            pass
        raise

    print("Готово!")
    print(f"Файл: {output_path}")

    if zipfile.is_zipfile(output_path):
        print("Проверка ZIP: OK")
    else:
        print("ВНИМАНИЕ: файл не распознан как ZIP.")

    return output_path, False


def extract_zip(zip_path, extract_root, mod_name=None, name_mode=MODE_NAME_AUTO,
                zip_was_skipped=False):
    """Распаковывает ZIP в extract_root.

    Возвращает (path, had_old_warning), либо None, если пользователь
    отказался переустанавливать существующую папку.
    """
    had_old_warning = False

    extract_root.mkdir(parents=True, exist_ok=True)

    try:
        zf = zipfile.ZipFile(zip_path)
    except zipfile.BadZipFile as e:
        raise RuntimeError(
            "Архив повреждён или имеет некорректный формат ZIP.\n"
            f"Техническая причина: {e}"
        ) from None

    with zf:
        members = [
            i for i in zf.infolist()
            if not _is_junk_member(i.filename)
        ]

        if not members:
            raise RuntimeError(
                "В архиве нет файлов для распаковки.\n"
                "Он пуст или содержит только служебные файлы."
            )

        real_files = [m for m in members if not m.filename.endswith("/")]
        if not real_files:
            raise RuntimeError(
                "В архиве нет ни одного файла — только пустые папки.\n"
                "Устанавливать нечего."
            )

        if len(real_files) > MAX_ZIP_MEMBERS:
            raise RuntimeError(
                "=" * 60 + "\n"
                "Слишком много файлов в архиве!\n"
                + "=" * 60 + "\n"
                f"Файлов в архиве:  {len(real_files):,}\n"
                f"Лимит:            {MAX_ZIP_MEMBERS:,}\n"
                "\n"
                "Это значительно больше того, что обычно встречается в модах.\n"
                "Похоже на аномалию: битый архив, ошибку упаковки или что-то\n"
                "нестандартное.\n"
                "Распаковка такого архива может занять очень много времени,\n"
                "а также подозрительно нагрузить диск.\n"
                "\n"
                "Установка отменена. ZIP остался в Downloads.\n"
                "Если уверен, что это нормальный мод — попробуй скачать его\n"
                "вручную.\n"
                + "=" * 60
            )

        for m in members:
            _fix_zip_member_encoding(m)

        names = [
            i.filename[2:] if i.filename.startswith("./") else i.filename
            for i in members
        ]

        tops = {n.split("/")[0] for n in names if n.strip("/")}

        single_folder = len(tops) == 1 and any(
            "/" in n.strip("/") or n.endswith("/") for n in names
        )
        top_name = next(iter(tops)) if single_folder else None
        archive_name = top_name or zip_path.stem

        current_name = resolve_folder_name(archive_name, mod_name, name_mode)

        base_resolved = extract_root.resolve()
        for member in members:
            target = (extract_root / member.filename).resolve()
            try:
                target.relative_to(base_resolved)
            except ValueError:
                raise RuntimeError(
                    f"Небезопасный путь в архиве: {member.filename}\n"
                    "Распаковка отменена."
                )

        confirmed_delete = False

        while True:
            final_path = extract_root / current_name

            if final_path.resolve().parent != extract_root.resolve():
                raise RuntimeError(
                    f"Недопустимое имя папки: {current_name!r}. Распаковка отменена."
                )

            if not final_path.exists():
                break

            if zip_was_skipped:
                zip_was_skipped = False

                print()
                print("ZIP не менялся с прошлого раза. Папка уже распакована:")
                print(f"  {final_path}")
                print()
                print("Если ты не уверен, что там актуальная версия — выбери «да».")
                print()

                answer = input("Распаковать заново? (нет/да):\n> ").strip().lower()

                if answer not in ("да", "д", "yes", "y"):
                    return None

                if not confirm_delete_with_code():
                    raise ExtractionCancelled("Распаковка отменена пользователем.")

                confirmed_delete = True
                break

            action = ask_about_existing_folder(final_path, archive_name)

            if action is None:
                raise ExtractionCancelled("Распаковка отменена пользователем.")

            if action is _DELETE:
                confirmed_delete = True
                break

            current_name = action

        final_path_str = str(final_path)
        if len(final_path_str) > MAX_MOD_PATH_LEN:
            raise RuntimeError(
                f"Итоговый путь до папки мода слишком длинный "
                f"({len(final_path_str)} символов, максимум {MAX_MOD_PATH_LEN}).\n"
                "Внутри мода могут быть вложенные файлы, для которых не хватит "
                "запаса Windows до лимита длины пути (260 символов).\n"
                "Сократи EXTRACT_DIR или выбери более короткое имя папки."
            )

        # Распаковка идёт сначала во временную папку вида
        # extract_root/tmpXXXXXXXX — это на ~11-13 символов длиннее,
        # чем extract_root. Значит, реальный максимальный путь может
        # оказаться длиннее финального. Считаем предупреждение от
        # максимума: либо финальный путь, либо оценка временного.
        estimated_tmp_path_len = len(str(extract_root)) + 1 + 11
        base_for_warning = max(len(final_path_str), estimated_tmp_path_len)

        longest = 0
        for m in members:
            candidate_len = (
                base_for_warning
                + 1
                + len(m.filename.replace("/", "\\"))
            )
            if candidate_len > longest:
                longest = candidate_len

        if longest > MAX_PATH_WARNING_THRESHOLD:
            print()
            print("ВНИМАНИЕ: внутри архива есть файлы с длинными путями.")
            print(f"Самый длинный путь после распаковки: ~{longest} символов.")
            print("Windows может отказать при распаковке (лимит 260 символов).")
            print("Если распаковка упадёт — сократи EXTRACT_DIR или имя папки.")
            print()

        total_uncompressed = sum(m.file_size for m in members)

        if total_uncompressed > 0:
            needed = total_uncompressed
            extra_note = ""

            if confirmed_delete and final_path.exists():
                old_size = dir_size_bytes(final_path)
                needed += old_size
                extra_note = f" + {format_size(old_size)} (старая папка)"

            free_space = shutil.disk_usage(extract_root).free

            if needed > free_space:
                raise RuntimeError(
                    f"Недостаточно места для распаковки:\n"
                    f"  нужно:      {format_size(needed)}{extra_note}\n"
                    f"  свободно:   {format_size(free_space)}\n"
                    f"Распаковка отменена."
                )

        if len(real_files) > MAX_ZIP_MEMBERS_WARN:
            print()
            print("=" * 60)
            print("Файлов в архиве больше обычного!")
            print("=" * 60)
            print(f"Файлов в архиве:  {len(real_files):,}")
            print("Типичный мод в основном содержит сотни файлов.")
            print()
            print("Распаковка такого архива может занять много времени.")
            print("Если уверен, что всё в порядке — продолжай.")
            print()
            print("[Enter — продолжить, Ctrl+C — прервать]")
            input("> ")

        if not confirmed_delete:
            print()
            print(f"Создаю новую папку: {final_path.name}")

        with tempfile.TemporaryDirectory(dir=extract_root) as tmpdir:
            tmp_path = Path(tmpdir)

            # «Старая папка не тронута» уместно писать только если
            # она действительно была.
            old_note = (
                "\nСтарая папка не тронута."
                if confirmed_delete and final_path.exists() else ""
            )

            try:
                zf.extractall(tmp_path, members=members)
            except zipfile.BadZipFile as e:
                # Bad CRC-32 и подобное: данные внутри архива не сходятся
                # с его же контрольной суммой. К символам и длине пути
                # это отношения не имеет.
                raise RuntimeError(
                    "Архив повреждён внутри! Данные файла не сходятся "
                    "с контрольной суммой (CRC).\n"
                    f"Причина: {e}\n"
                    "Если при скачивании было «Проверка MD5: OK», файл "
                    "совпадает с тем, что лежит на mod.io.\n"
                    "Скорее всего, архив битый у источника. "
                    "Повторное скачивание не поможет.\n"
                    "Проверь архив в 7-Zip («Тестировать»): если он тоже "
                    "ругается, напиши автору мода, чтобы перезалил файл."
                    + old_note
                    + "\n\nМожно распаковать вручную, но на свой страх и риск!"
                ) from e
            except (EOFError, zlib.error) as e:
                # EOFError нельзя пропускать как есть: выше по стеку он
                # означает «ввод прерван» и завершил бы скрипт с неверным
                # сообщением.
                raise RuntimeError(
                    "Архив обрезан или данные сжатия повреждены.\n"
                    f"Причина: {e}\n"
                    "Скорее всего, файл битый. Попробуй скачать заново, "
                    "а если не поможет — напиши автору мода."
                    + old_note
                ) from e
            except NotImplementedError as e:
                raise RuntimeError(
                    "Архив использует метод сжатия, который Python "
                    "не поддерживает.\n"
                    f"Причина: {e}\n"
                    "Распакуй его вручную (например, 7-Zip)."
                    + old_note
                ) from e
            except Exception as e:
                msg = str(e).lower()

                if "encrypted" in msg or "password" in msg:
                    raise RuntimeError(
                        "Архив зашифрован — распаковать нельзя.\n"
                        "Такой архив требует пароль, скрипт его не знает."
                        + old_note
                    ) from e

                if isinstance(e, OSError):
                    raise RuntimeError(
                        f"Не удалось записать файлы: {e}\n"
                        "Возможно, имена файлов внутри содержат символы, "
                        "недопустимые в Windows, путь получился слишком "
                        "длинным, или не хватает места/прав."
                        + old_note
                    ) from e

                raise RuntimeError(
                    f"Неожиданная ошибка: {e}" + old_note
                ) from e

            source = (tmp_path / top_name) if single_folder else tmp_path

            old_path = None

            if confirmed_delete and final_path.exists():
                base_old = final_path.parent / (final_path.name + ".old")

                if base_old.exists():
                    print()
                    print(f"Найден остаток от прошлой замены: {base_old.name}")
                    print("Оставляю его на месте (удали вручную, если не нужен).")

                old_path = base_old
                suffix_i = 2
                while old_path.exists():
                    old_path = final_path.parent / (
                        f"{final_path.name}.old{suffix_i}"
                    )
                    suffix_i += 1

                try:
                    final_path.rename(old_path)
                except OSError as e:
                    raise RuntimeError(
                        f"Не удалось подготовить замену папки:\n{e}\n"
                        "Возможно, папка занята другой программой."
                    ) from e

            try:
                final_path.mkdir(parents=True)

                for item in source.iterdir():
                    shutil.move(str(item), str(final_path / item.name))
            except BaseException:
                if old_path is not None:
                    try:
                        if final_path.exists():
                            shutil.rmtree(final_path)
                        old_path.rename(final_path)
                        print()
                        print("Распаковка не удалась — старая папка восстановлена.")
                    except OSError:
                        print()
                        print(f"Не удалось восстановить старую папку. Она здесь: {old_path}")
                else:
                    try:
                        if final_path.exists():
                            shutil.rmtree(final_path)
                        print()
                        print("Распаковка не удалась — частично распакованная папка удалена.")
                    except OSError as e:
                        print()
                        print(f"Не удалось убрать недоделанную папку {final_path}: {e}")
                        print("Удали её вручную перед следующим запуском.")
                raise

            if old_path is not None:
                try:
                    shutil.rmtree(old_path)
                except OSError as e:
                    had_old_warning = True
                    print()
                    print(f"Не удалось удалить старую папку: {old_path}")
                    print(f"Причина: {e}")
                    print("Можешь удалить её вручную.")

    return final_path, had_old_warning


def confirm_delete_with_code():
    """Показывает случайный цифровой код и просит ввести его."""
    alphabet = "23456789"
    code = "".join(random.choice(alphabet) for _ in range(4))

    print()
    print(f"Для подтверждения введи код: {code}")
    entered = input("> ").strip()

    if entered != code:
        print("Код не совпал — распаковка отменена.")
        return False

    return True


def ask_about_existing_folder(folder_path, archive_name):
    """Показывает сводку о папке и спрашивает, что делать."""
    if not folder_path.is_dir():
        print()
        print("=" * 60)
        print("По этому пути лежит файл, а не папка!")
        print("=" * 60)
        print(f"Путь : {folder_path}")
        print()
        print("Скрипт не может распаковать мод: путь занят файлом.")
        print("Удали или переименуй этот файл и запусти скрипт снова.")
        print("=" * 60)
        return None

    try:
        files = [f for f in folder_path.rglob("*") if f.is_file()]
        file_count = len(files)
        total_size = sum(f.stat().st_size for f in files)
        mtime = folder_path.stat().st_mtime
    except OSError:
        file_count = None
        total_size = None
        mtime = None

    print()
    print("=" * 60)
    print("Найдена папка с таким же названием")
    print("=" * 60)
    print(f"Путь    : {folder_path}")

    if file_count is not None:
        print(f"Файлов  : {file_count}")
        print(f"Размер  : {format_size(total_size)}")
        print(
            "Изменена:",
            time.strftime("%Y-%m-%d %H:%M", time.localtime(mtime)),
        )

    print("=" * 60)
    print()

    answer = input("Удалить её и заменить новой? (да/нет):\n> ").strip().lower()

    if answer in ("нет", "н", "no", "n"):
        print()
        print("Хочешь ввести другое имя для папки этого мода?")
        print("  1 — ввести новое имя")
        print("  2 — отменить распаковку и выйти")
        choice = input("> ").strip()

        if choice == "1":
            return ask_folder_name(archive_name)

        return None

    if answer in ("да", "д", "yes", "y"):
        if not confirm_delete_with_code():
            return None

        return _DELETE

    print("Непонятный ответ — считаю отменой.")
    return None


def record_extract_status(issues, name, status):
    """Добавляет проблему с распаковкой в общий список."""
    if status == STATUS_FAILED:
        issues.append(f"{name}: не удалось распаковать — ZIP остался в Downloads")
    elif status == STATUS_CANCELLED:
        issues.append(f"{name}: операция отменена пользователем — ZIP остался в Downloads")
    elif status == STATUS_NOT_ZIP:
        issues.append(f"{name}: файл не ZIP — распаковка пропущена")
    elif status == STATUS_EXTRACTED_WITH_WARNINGS:
        issues.append(
            f"{name}: установлено, но старая версия (.old) не удалилась — "
            "удали вручную"
        )


def download_mod(mod, api_key, output_dir, file_info, mod_name=None,
                 name_mode=MODE_NAME_AUTO):
    """Скачивает и распаковывает мод.

    Возвращает (zip_path, extract_status).
    """
    mod_id = safe_non_negative_int(mod.get("id"))
    if mod_id is None:
        raise RuntimeError("mod.io вернул мод без числового id.")

    zip_path = None
    was_skipped = False

    for attempt in range(2):
        try:
            zip_path, was_skipped = download_zip(
                file_info, output_dir, f"mod_{mod_id}.zip", api_key
            )
            break

        except DownloadCancelled as e:
            print(f"{e}")
            return None, STATUS_CANCELLED

        except ExpiredDownloadLink as e:
            if attempt == 1:
                raise RuntimeError(
                    "Временная ссылка снова протухла — это очень странно.\n"
                    "Скорее всего, что-то не так на стороне mod.io.\n"
                    "Попробуй запустить скрипт заново позже."
                ) from None

            print()
            print(f"Временная ссылка на файл больше не работает ({e}).")
            print("Получаю свежую ссылку и пробую ещё раз...")

            file_id, file_info = resolve_file_info(
                mod, mod_id, api_key, ask=False
            )

    extract_status = None

    if EXTRACT_DIR is not None:
        print()
        if not zipfile.is_zipfile(zip_path):
            print("Распаковка пропущена: файл не является ZIP.")
            extract_status = STATUS_NOT_ZIP
        else:
            try:
                result = extract_zip(
                    zip_path, EXTRACT_DIR,
                    mod_name=mod_name,
                    name_mode=name_mode,
                    zip_was_skipped=was_skipped,
                )

                if result is None:
                    print("Распаковка пропущена (папка уже распакована).")
                    extract_status = STATUS_ALREADY
                else:
                    path, had_warning = result
                    print(f"Распаковано в: {path}")

                    if had_warning:
                        extract_status = STATUS_EXTRACTED_WITH_WARNINGS
                    else:
                        extract_status = STATUS_EXTRACTED

                    if not KEEP_ZIP:
                        try:
                            zip_path.unlink(missing_ok=True)
                            print("ZIP удалён из Downloads.")
                        except OSError as e:
                            print()
                            print(f"ВНИМАНИЕ: не удалось удалить ZIP: {e}")
                            print("Мод установлен, но ZIP остался в Downloads.")

            except EOFError:
                raise
            except ExtractionCancelled as e:
                print(f"{e}")
                print(f"ZIP остался здесь: {zip_path}")
                extract_status = STATUS_CANCELLED
            except Exception as e:
                print()
                print("Не удалось распаковать:")
                print(e)
                print()
                print(f"ZIP остался здесь: {zip_path}")
                extract_status = STATUS_FAILED

    return zip_path, extract_status


def process_dependencies(dependencies, api_key, downloads, name_mode, issues):
    """Скачивает список зависимостей."""
    failed = []

    for dep_id, dep_name in dependencies:
        print()
        print("=" * 60)
        print(f"Зависимость: {dep_name} (ID {dep_id})")
        print("=" * 60)

        try:
            dep_mod = api_get(f"/games/{GAME_ID}/mods/{dep_id}", api_key)

            dep_display_name = (
                dep_mod.get("name")
                or dep_mod.get("name_id")
                or dep_name
            )

            _, dep_file_info = resolve_file_info(dep_mod, dep_id, api_key)

            if dep_file_info is None:
                raise RuntimeError(
                    f"для зависимости нет файла для {TARGET_PLATFORM.capitalize()}"
                )

            _, dep_status = download_mod(
                dep_mod, api_key, downloads, dep_file_info,
                mod_name=dep_display_name, name_mode=name_mode,
            )
            record_extract_status(issues, dep_display_name, dep_status)
        except EOFError:
            raise
        except Exception as e:
            print(f"Не удалось скачать зависимость: {mask_key(e, api_key)}")
            failed.append(dep_name)

    return failed


# ---------- Диалоги при проблемах с зависимостями ----------

def _print_exceeded_menu():
    """Меню действий при превышении лимита зависимостей."""
    print("Что делать?")
    print("  1 — продолжить установку базового мода без зависимостей")
    print("  2 — вернуться на ввод ссылки")
    print("  3 — вернуться к выбору режима")
    print("  4 — закончить установку")


def _ask_exceeded_choice():
    """Спрашивает выбор из меню превышения лимита."""
    while True:
        choice = input("> ").strip()

        if choice == "1":
            return "no_deps"
        if choice == "2":
            return "retry_url"
        if choice == "3":
            return "restart"
        if choice == "4":
            return "exit"

        print("Непонятный ответ. Введи 1, 2, 3 или 4.")


def ask_exceeded_action():
    """Спрашивает, что делать при превышении нашего лимита (25)."""
    print()
    print("=" * 60)
    print(f"Найдено более {MAX_DEPENDENCIES} зависимостей (лимит — {MAX_DEPENDENCIES}).")
    print("Этот режим не предполагает обработку более "
          f"{MAX_DEPENDENCIES} зависимостей.")
    print("Установка приостановлена.")
    print("=" * 60)
    print()
    _print_exceeded_menu()
    return _ask_exceeded_choice()


def ask_truncated_action():
    """Спрашивает, что делать, если mod.io упёрся в свой потолок (100)."""
    print()
    print("=" * 60)
    print(f"Найдено более {DEPENDENCIES_PAGE_LIMIT} зависимостей.")
    print("Это технический лимит mod.io,")
    print("а также этот режим не предполагает обработку такого количества.")
    print("Установка приостановлена.")
    print("=" * 60)
    print()
    _print_exceeded_menu()
    return _ask_exceeded_choice()


def ask_api_error_with_zip_action():
    """Что делать при сбое зависимостей, когда валидный ZIP уже есть."""
    print()
    print("Что делать?")
    print("  1 — продолжить установку только с этим ZIP")
    print("  2 — закончить работу")

    while True:
        choice = input("> ").strip()

        if choice == "1":
            return "continue"
        if choice == "2":
            return "exit"

        print("Непонятный ответ. Введи 1 или 2.")


def ask_api_error_no_zip_action():
    """Что делать при сбое зависимостей, когда валидного ZIP нет."""
    print()
    print("Что делать?")
    print("  1 — скачать только основной мод (без зависимостей)")
    print("  2 — закончить работу")

    while True:
        choice = input("> ").strip()

        if choice == "1":
            return "continue"
        if choice == "2":
            return "exit"

        print("Непонятный ответ. Введи 1 или 2.")


def process_one_url(api_key, file_mode, name_mode, initial_url=None):
    """Обрабатывает одну ссылку.

    Возвращает:
      "done" / "warn" / "exit" / "retry_url" / "restart".
    """
    if initial_url is not None:
        mod_url = initial_url
        print()
        print(f"Ссылка из аргумента: {mod_url}")
    else:
        print()
        mod_url = input("Вставь ссылку на мод mod.io:\n> ").strip()

    try:
        mod_slug = get_mod_slug(mod_url)
    except ValueError as e:
        print()
        print(f"Ошибка в ссылке: {e}")
        return "retry_url"

    print()
    print(f"Мод: {mod_slug}")
    print("Ищу мод...")

    mod_slug_lower = mod_slug.lower()

    data = api_get(
        f"/games/{GAME_ID}/mods",
        api_key,
        {
            "name_id": mod_slug_lower,
            "_limit": 1,
        },
    )

    if not isinstance(data, dict):
        print()
        print("mod.io вернул неожиданный формат ответа для списка модов.")
        return "retry_url"

    matches = [
        m for m in (data.get("data") or [])
        if isinstance(m, dict) and (m.get("name_id") or "").lower() == mod_slug_lower
    ]

    if not matches:
        print()
        print("Точный мод по этой ссылке не найден через API.")
        return "retry_url"

    mod = matches[0]

    mod_id = safe_non_negative_int(mod.get("id"))
    if mod_id is None:
        print()
        print("mod.io вернул мод без числового id.")
        return "retry_url"

    mod_name = mod.get("name") or mod_slug

    print(f"Название : {mod_name}")
    print(f"Mod ID   : {mod_id}")

    print("Получаю свежую ссылку на ZIP...")
    file_id, file_info = resolve_file_info(mod, mod_id, api_key)

    if file_info is None:
        return "retry_url"

    print(f"File ID  : {file_id}")

    platforms_text = _platforms_text(file_info)

    if platforms_text:
        print(f"Платформы: {platforms_text}")

    deps_to_install = []

    if file_mode == MODE_FILE_ONE_DEPS:
        print()
        print("Проверяю зависимости (обход всего дерева)...")

        deps_status, deps_list = collect_all_dependencies(mod_id, api_key)

        if deps_status == DEPS_ERROR:
            print()
            print("=" * 60)
            print("Проблема на стороне mod.io")
            print("=" * 60)
            print("Не удалось получить полный список зависимостей.")
            print()

            valid_zip = find_existing_valid_zip(
                file_info, get_downloads_dir(), f"mod_{mod_id}.zip"
            )

            if valid_zip is None:
                print("Валидного ZIP в Downloads нет.")
                print("Основной мод скачать можно, но без зависимостей.")
                print("=" * 60)

                action = ask_api_error_no_zip_action()
                if action == "exit":
                    return "exit"
            else:
                print(f"В Downloads есть валидный ZIP: {valid_zip.name}")
                print("=" * 60)

                action = ask_api_error_with_zip_action()
                if action == "exit":
                    return "exit"

            deps_to_install = []

        elif deps_status == DEPS_TRUNCATED:
            action = ask_truncated_action()

            if action == "no_deps":
                print()
                print("Продолжаю установку только базового мода.")
                deps_to_install = []
            elif action == "retry_url":
                return "retry_url"
            elif action == "restart":
                return "restart"
            elif action == "exit":
                return "exit"

        elif deps_status == DEPS_EXCEEDED:
            action = ask_exceeded_action()

            if action == "no_deps":
                print()
                print("Продолжаю установку только базового мода.")
                deps_to_install = []
            elif action == "retry_url":
                return "retry_url"
            elif action == "restart":
                return "restart"
            elif action == "exit":
                return "exit"

        else:
            deps_to_install = deps_list
            if deps_to_install:
                print(f"Найдено зависимостей: {len(deps_to_install)}. Продолжаю...")
            else:
                print("Зависимостей нет.")

    downloads = get_downloads_dir()

    issues = []

    try:
        zip_path, status = download_mod(
            mod, api_key, downloads, file_info,
            mod_name=mod_name, name_mode=name_mode,
        )
        record_extract_status(issues, mod_name, status)
    except EOFError:
        raise
    except Exception as e:
        print()
        print(f"Не удалось скачать основной мод: {mask_key(e, api_key)}")
        print()
        print("Зависимости не скачиваю — без основного мода они не нужны.")
        return "exit"

    if status == STATUS_CANCELLED:
        print()
        print("=" * 60)
        if zip_path is not None:
            print("ZIP основного мода скачан, но распаковка отменена.")
            print("Зависимости не скачиваю — без установленного мода")
            print("они не имеют смысла.")
        else:
            print("Основной мод отменён — зависимости не скачиваю.")
        print("=" * 60)
        return "warn"

    if EXTRACT_DIR is not None and status not in (
        STATUS_EXTRACTED,
        STATUS_EXTRACTED_WITH_WARNINGS,
        STATUS_ALREADY,
    ):
        print()
        print("=" * 60)
        print("Основной мод не установлен — зависимости не скачиваю.")
        print("=" * 60)
        return "warn"

    failed = []

    if deps_to_install:
        failed = process_dependencies(
            deps_to_install, api_key, downloads,
            name_mode, issues,
        )

    print()
    print("=" * 60)

    if failed:
        print("Основной мод скачан, но эти зависимости скачать не удалось:")
        for name in failed:
            print(f"  - {name}")
        print("Скачай их вручную на странице мода.")

    if issues:
        print("Скачано, но не всё в порядке:")
        for line in issues:
            print(f"  - {line}")

    if not failed and not issues:
        if EXTRACT_DIR is None:
            print("Всё скачано.")
        else:
            print("Всё установлено и распаковано.")

    print("=" * 60)

    if failed or issues:
        print()
        if file_mode == MODE_FILE_ONE_DEPS:
            print("(Это не сбой запуска, а предупреждение о зависимостях.)")
        else:
            print("(Это не сбой запуска, а предупреждение.)")
        return "warn"

    return "done"


def main():
    """Диспетчер: выбирает режимы, ключ, и запускает обработку ссылок."""
    print("=" * 60)
    print(f"Transport Fever 3 — Mod Downloader v{VERSION}")
    print("=" * 60)
    print()

    api_key = ""

    try:
        if EXTRACT_DIR is not None:
            check_extract_dir(EXTRACT_DIR)

        warn_about_old_folders(EXTRACT_DIR)

        argv_url = None
        if len(sys.argv) > 1 and sys.argv[1].strip():
            argv_url = sys.argv[1].strip()

        file_mode = None
        name_mode = None

        while True:
            if file_mode is None:
                file_mode = ask_file_mode()
                name_mode = (
                    ask_name_mode() if EXTRACT_DIR is not None
                    else MODE_NAME_AUTO
                )
                if not api_key:
                    api_key = get_api_key()

            action = process_one_url(
                api_key, file_mode, name_mode, argv_url
            )

            argv_url = None

            if action == "done":
                return

            if action == "warn":
                sys.exit(2)

            if action == "exit":
                sys.exit(1)

            if action == "retry_url":
                continue

            if action == "restart":
                file_mode = None
                name_mode = None
                print()
                print("Возврат к выбору режима...")
                print()
                continue

    except EOFError:
        print()
        print("Ввод прерван (Ctrl+Z / Ctrl+D).")
        sys.exit(1)

    except Exception as e:
        print()
        print("ОШИБКА:")
        print(mask_key(e, api_key))
        print()
        sys.exit(1)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nОстановлено.")
        sys.exit(1)
    except EOFError:
        print("\nВвод прерван.")
        sys.exit(1)