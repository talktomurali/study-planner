#!/usr/bin/env python3
"""
download_ncert.py
=================
Download official NCERT English-medium textbooks (Classes 6-10: English,
Science, Social Science) from https://ncert.nic.in and save ONE complete PDF
per book.

Pipeline
  1. Discovery  - Reads the official catalogue at https://ncert.nic.in/textbook.php
                  (the data behind its Class / Subject / Book dropdowns).
                  If the static parse finds nothing for a class/subject, it can
                  drive the real page in a headless browser (Playwright, optional).
  2. Locating   - NCERT's "complete book" download is a ZIP of chapter PDFs.
                  The script looks for that link on the book's official page,
                  otherwise uses the portal's own naming scheme (<code>dd.zip).
                  Every candidate URL must be https://ncert.nic.in and is only
                  accepted if the content validates. If no ZIP exists, chapter
                  PDFs are downloaded individually instead.
  3. Validation - HTTP status, Content-Type (HTML pages rejected), ZIP CRCs,
                  %PDF- signature, and a full parse of every PDF with pypdf.
  4. Assembly   - Chapter PDFs are merged in order (front matter, chapters,
                  appendices) into a .part file that is renamed only when valid.

Run "python download_ncert.py --help" for all options.
Downloaded files are only read and parsed as data - never executed or opened.
"""
from __future__ import annotations

import argparse
import io
import json
import logging
import os
import re
import shutil
import sys
import time
import zipfile
from dataclasses import asdict, dataclass, field
from pathlib import Path, PurePosixPath
from urllib import robotparser
from urllib.parse import urljoin, urlparse

if sys.version_info < (3, 10):
    sys.exit("Python 3.10 or newer is required.")

try:
    import requests
    from bs4 import BeautifulSoup
    from pypdf import PdfReader, PdfWriter
    from requests.adapters import HTTPAdapter
    from tqdm import tqdm
    from tqdm.contrib.logging import logging_redirect_tqdm
    from urllib3.util.retry import Retry
except ImportError as exc:  # pragma: no cover
    sys.exit(f"Missing dependency ({exc.name}). Run:  pip install -r requirements.txt")

# --------------------------------------------------------------------------
# Configuration
# --------------------------------------------------------------------------
DEFAULT_DEST = Path(r"C:\Users\murali\Documents\ncert")
BASE_URL = "https://ncert.nic.in/"
CATALOGUE_URL = "https://ncert.nic.in/textbook.php?ln=en"
ALLOWED_HOSTS = frozenset({"ncert.nic.in", "www.ncert.nic.in"})
DEFAULT_USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "NCERT-Textbook-Downloader/1.0 (personal study use)"
)

ROMAN = {6: "VI", 7: "VII", 8: "VIII", 9: "IX", 10: "X"}
CLASS_DIRS = {6: "6th", 7: "7th", 8: "8th", 9: "9th", 10: "10th"}
SUBJECTS = ("English", "Mathematics", "Science", "Social Science")
SUBJECT_ALIASES = {
    "English": {"english"},
    "Mathematics": {"mathematics", "maths", "math"},
    "Science": {"science"},
    "Social Science": {"social science", "social sciences", "social studies"},
}

# NCERT book codes: <class letter a-l><medium letter><subject letters><number>,
# e.g. "fecu1" = Class 6 (f), English medium (e), Curiosity (cu), book 1.
BOOK_QS_RE = re.compile(r"textbook\.php\?([a-z]{3,5}\d{1,2})=(\d{1,3})-(\d{1,3})", re.IGNORECASE)
ENGLISH_MEDIUM_LETTER = "e"

CHUNK_SIZE = 64 * 1024
MAX_ATTEMPTS = 5                 # per file, for network failures (with backoff)
MAX_REDIRECTS = 5
MAX_UNZIPPED_BYTES = 1024 ** 3   # refuse ZIPs that expand beyond 1 GB
RETRYABLE_STATUS = {429, 500, 502, 503, 504}
PARTIAL_DIRNAME = "_partial_downloads"

log = logging.getLogger("ncert")


# --------------------------------------------------------------------------
# Errors and data structures
# --------------------------------------------------------------------------
class NcertError(Exception):
    """Base class for expected, reportable failures."""


class NotOfficialURLError(NcertError):
    """A URL (or redirect target) is outside the official NCERT domain."""


class NotAvailableError(NcertError):
    """The resource definitively does not exist (404/403, HTML page, empty)."""


class TransientDownloadError(NcertError):
    """Network trouble persisted after retries; partial data kept for resume."""


class ValidationError(NcertError):
    """Downloaded content is not a valid PDF/ZIP."""


class DiscoveryError(NcertError):
    """The catalogue could not be read."""


@dataclass(frozen=True)
class Book:
    class_num: int
    subject: str
    title: str
    code: str
    chapter_start: int
    chapter_end: int
    discovered_by: str

    @property
    def page_url(self) -> str:
        """The book's official NCERT page (same URL the portal's 'Go' button opens)."""
        return urljoin(BASE_URL, f"textbook.php?{self.code}={self.chapter_start}-{self.chapter_end}")


@dataclass
class Report:
    discovered: list[Book] = field(default_factory=list)
    downloaded: list[tuple[Book, Path, str]] = field(default_factory=list)
    skipped: list[tuple[Book, Path]] = field(default_factory=list)
    failed: list[tuple[Book, str]] = field(default_factory=list)
    unavailable: list[tuple[int, str, str]] = field(default_factory=list)


# --------------------------------------------------------------------------
# Small helpers
# --------------------------------------------------------------------------
def is_official_url(url: str) -> bool:
    try:
        parts = urlparse(url)
    except ValueError:
        return False
    return parts.scheme == "https" and (parts.hostname or "").lower() in ALLOWED_HOSTS


def class_from_code(code: str) -> int | None:
    num = ord(code[0].lower()) - ord("a") + 1
    return num if 1 <= num <= 12 else None


def is_english_medium(code: str) -> bool:
    return len(code) > 1 and code[1].lower() == ENGLISH_MEDIUM_LETTER


def canonical_subject(label: str | None) -> str | None:
    if not label:
        return None
    norm = re.sub(r"\s+", " ", label).strip().lower()
    for canon, aliases in SUBJECT_ALIASES.items():
        if norm in aliases:
            return canon
    return None


def safe_name(text: str, max_len: int = 80) -> str:
    cleaned = re.sub(r"[^A-Za-z0-9]+", "_", text).strip("_")
    return cleaned[:max_len].rstrip("_") or "Book"


def human_size(num: float | None) -> str:
    if num is None:
        return "size unknown"
    for unit in ("B", "KB", "MB", "GB"):
        if num < 1024 or unit == "GB":
            return f"{num:.0f} {unit}" if unit == "B" else f"{num:.1f} {unit}"
        num /= 1024
    return f"{num:.1f} GB"


# --------------------------------------------------------------------------
# HTTP client: official domain only, robots.txt aware, rate limited
# --------------------------------------------------------------------------
class OfficialClient:
    def __init__(self, user_agent: str, delay: float, connect_timeout: float, read_timeout: float):
        self.user_agent = user_agent
        self.delay = delay
        self.timeout = (connect_timeout, read_timeout)
        self._last_request = 0.0
        self._robots: robotparser.RobotFileParser | None = None

        self.session = requests.Session()
        self.session.headers.update({"User-Agent": user_agent, "Accept-Language": "en"})
        retry = Retry(
            total=3, connect=3, read=2, status=3,
            backoff_factor=2.0,
            status_forcelist=sorted(RETRYABLE_STATUS),
            allowed_methods=frozenset({"GET", "HEAD"}),
            respect_retry_after_header=True,
            raise_on_status=False,
        )
        self.session.mount("https://", HTTPAdapter(max_retries=retry))

    def _throttle(self) -> None:
        wait = self.delay - (time.monotonic() - self._last_request)
        if wait > 0:
            time.sleep(wait)
        self._last_request = time.monotonic()

    def load_robots(self) -> None:
        """Honour robots.txt rules and Crawl-delay if NCERT publishes them."""
        url = urljoin(BASE_URL, "robots.txt")
        try:
            self._throttle()
            resp = self.session.get(url, timeout=self.timeout, allow_redirects=False)
        except requests.RequestException as exc:
            log.info("Could not read robots.txt (%s); continuing with a %.1fs delay.", exc, self.delay)
            return
        with resp:
            ctype = resp.headers.get("Content-Type", "").lower()
            if resp.status_code == 200 and "text/plain" in ctype:
                parser = robotparser.RobotFileParser()
                parser.parse(resp.text.splitlines())
                self._robots = parser
                crawl_delay = parser.crawl_delay(self.user_agent)
                if crawl_delay:
                    self.delay = max(self.delay, float(crawl_delay))
                log.info("robots.txt loaded; request delay %.1fs.", self.delay)
            else:
                log.info("No robots.txt rules published (HTTP %s); request delay %.1fs.",
                         resp.status_code, self.delay)

    def allowed(self, url: str) -> bool:
        return self._robots is None or self._robots.can_fetch(self.user_agent, url)

    def get(self, url: str, *, stream: bool = False, headers: dict | None = None) -> requests.Response:
        """GET that follows redirects manually and verifies every hop is official."""
        current = url
        for _ in range(MAX_REDIRECTS + 1):
            if not is_official_url(current):
                raise NotOfficialURLError(f"Refusing non-official URL: {current}")
            if not self.allowed(current):
                raise NotAvailableError(f"robots.txt disallows {current}")
            self._throttle()
            resp = self.session.get(current, stream=stream, headers=headers,
                                    timeout=self.timeout, allow_redirects=False)
            if resp.is_redirect:
                location = resp.headers.get("Location", "")
                resp.close()
                current = urljoin(current, location)
                log.debug("Redirect -> %s", current)
                continue
            return resp
        raise NotAvailableError(f"Too many redirects starting from {url}")


# --------------------------------------------------------------------------
# Discovery
# --------------------------------------------------------------------------
# Tolerant tokenizer for the catalogue JavaScript. It tracks:
#   - subject conditions, e.g.  options[i].text=="Science"
#   - option assignments, e.g.  options[1].text="Curiosity"; options[1].value="textbook.php?fecu1=0-12"
#   - new Option("Curiosity", "textbook.php?fecu1=0-12")
SCRIPT_TOKEN_RE = re.compile(
    r"""\.(?:text|value)\s*==\s*(?P<q1>["'])(?P<subject>[A-Za-z][^"'\n]{0,60})(?P=q1)"""
    r"""|options\s*\[\s*(?P<text_idx>\d+)\s*\]\s*\.text\s*=(?!=)\s*(?P<q2>["'])(?P<title>[^\n]*?)(?P=q2)"""
    r"""|options\s*\[\s*(?P<value_idx>\d+)\s*\]\s*\.value\s*=(?!=)\s*(?P<q3>["'])(?P<value>[^\n]*?)(?P=q3)"""
    r"""|new\s+Option\s*\(\s*(?P<q4>["'])(?P<opt_title>[^\n]*?)(?P=q4)\s*,\s*(?P<q5>["'])(?P<opt_value>[^\n]*?)(?P=q5)""",
    re.IGNORECASE,
)


def make_book(value: str | None, title: str, subject_label: str | None, class_hint: int | None,
              classes: list[int], subjects: list[str], discovered_by: str) -> Book | None:
    """Turn one catalogue entry into a Book, or None if it is out of scope."""
    match = BOOK_QS_RE.search(value or "")
    if not match:
        return None
    code = match.group(1).lower()
    start, end = int(match.group(2)), int(match.group(3))
    if not is_english_medium(code):
        return None
    subject = canonical_subject(subject_label)
    if subject is None or subject not in subjects:
        return None
    code_class = class_from_code(code)
    if class_hint is not None and code_class != class_hint:
        log.warning("Catalogue lists %s under Class %s but its code implies Class %s; using the catalogue.",
                    code, class_hint, code_class)
        class_num = class_hint
    else:
        class_num = code_class
    if class_num not in classes or end < max(start, 1):
        return None
    title = re.sub(r"\s+", " ", title or "").strip() or code
    return Book(class_num, subject, title, code, start, end, discovered_by)


def fetch_catalogue_sources(client: OfficialClient) -> list[str]:
    """Return the catalogue HTML plus any same-site JavaScript files it loads."""
    resp = client.get(CATALOGUE_URL)
    with resp:
        if resp.status_code != 200:
            raise DiscoveryError(f"catalogue page returned HTTP {resp.status_code}")
        if "html" not in resp.headers.get("Content-Type", "").lower():
            raise DiscoveryError("catalogue page did not return HTML")
        html, page_url = resp.text, resp.url

    sources = [html]
    soup = BeautifulSoup(html, "html.parser")
    script_urls = []
    for tag in soup.find_all("script", src=True):
        url = urljoin(page_url, tag["src"].strip())
        name = PurePosixPath(urlparse(url).path).name.lower()
        if is_official_url(url) and not re.search(r"jquery|bootstrap|analytics|gtag|owl|slick|swiper", name):
            script_urls.append(url)
    for url in script_urls[:15]:
        try:
            js = client.get(url)
            with js:
                if js.status_code == 200:
                    sources.append(js.text)
        except (requests.RequestException, NcertError) as exc:
            log.debug("Skipping script %s: %s", url, exc)
    return sources


def parse_catalogue_scripts(texts: list[str], classes: list[int], subjects: list[str]) -> list[Book]:
    found: dict[str, Book] = {}
    for text in texts:
        subject_ctx: str | None = None
        pending_titles: dict[str, str] = {}
        for m in SCRIPT_TOKEN_RE.finditer(text):
            if m.group("subject") is not None:
                subject_ctx = m.group("subject").strip()
                pending_titles.clear()
            elif m.group("text_idx") is not None:
                pending_titles[m.group("text_idx")] = m.group("title").strip()
            else:
                if m.group("value_idx") is not None:
                    value, title = m.group("value"), pending_titles.get(m.group("value_idx"), "")
                else:
                    value, title = m.group("opt_value"), m.group("opt_title")
                book = make_book(value, title, subject_ctx, None, classes, subjects, "static catalogue parse")
                if book and book.code not in found:
                    found[book.code] = book
    return list(found.values())


def discover_with_browser(client: OfficialClient, classes: list[int], subjects: list[str],
                          timeout_ms: int = 60000) -> list[Book]:
    """Drive the real catalogue dropdowns in headless Chromium and read their options."""
    try:
        from playwright.sync_api import Error as PlaywrightError, sync_playwright
    except ImportError as exc:
        raise DiscoveryError("Playwright is not installed (optional): "
                             "pip install playwright && python -m playwright install chromium") from exc
    if not client.allowed(CATALOGUE_URL):
        raise DiscoveryError("robots.txt disallows the catalogue page")

    read_js = "s => Array.from(s.options).map(o => [o.text.trim(), o.value])"
    found: dict[str, Book] = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True)
            try:
                page = browser.new_page()
                page.set_default_timeout(timeout_ms)
                page.goto(CATALOGUE_URL, wait_until="domcontentloaded")
                selects = page.locator("select")
                all_opts = [selects.nth(i).evaluate(read_js) for i in range(selects.count())]

                def locate(needle: str):
                    # The portal's dropdowns start with "..Select Class..", "..Select Subject..",
                    # "..Select Book Title..".
                    for i, opts in enumerate(all_opts):
                        if opts and needle in opts[0][0].lower():
                            return selects.nth(i)
                    raise DiscoveryError(f"could not find the '{needle}' dropdown")

                class_sel = locate("select class")
                subject_sel = locate("select subject")
                book_sel = locate("select book")
                class_opts = class_sel.evaluate(read_js)

                for class_num in classes:
                    pattern = re.compile(rf"class\s+{ROMAN[class_num]}", re.IGNORECASE)
                    idx = next((i for i, (t, _) in enumerate(class_opts) if pattern.fullmatch(t)), None)
                    if idx is None:
                        log.warning("Class %s not present in the catalogue dropdown.", ROMAN[class_num])
                        continue
                    class_sel.select_option(index=idx, force=True)
                    page.wait_for_timeout(500)
                    for s_idx, (s_text, _) in enumerate(subject_sel.evaluate(read_js)):
                        canon = canonical_subject(s_text)
                        if canon is None or canon not in subjects:
                            continue
                        subject_sel.select_option(index=s_idx, force=True)
                        page.wait_for_timeout(500)
                        for b_text, b_value in book_sel.evaluate(read_js):
                            book = make_book(b_value, b_text, s_text, class_num, classes, subjects,
                                             "browser (Playwright)")
                            if book and book.code not in found:
                                found[book.code] = book
            finally:
                browser.close()
    except PlaywrightError as exc:
        raise DiscoveryError(f"browser discovery failed: {exc}") from exc
    return list(found.values())


def discover_books(client: OfficialClient, classes: list[int], subjects: list[str],
                   mode: str) -> tuple[list[Book], list[tuple[int, str, str]]]:
    books: dict[str, Book] = {}
    notes: list[str] = []

    if mode in ("auto", "static"):
        log.info("Reading official catalogue: %s", CATALOGUE_URL)
        try:
            for book in parse_catalogue_scripts(fetch_catalogue_sources(client), classes, subjects):
                books[book.code] = book
            log.info("Static catalogue parse found %d matching book(s).", len(books))
        except (requests.RequestException, NcertError) as exc:
            notes.append(f"static catalogue read failed: {exc}")
            log.warning("Static catalogue read failed: %s", exc)

    def gaps() -> list[tuple[int, str]]:
        return [(c, s) for c in classes for s in subjects
                if not any(b.class_num == c and b.subject == s for b in books.values())]

    missing = gaps()
    if mode == "browser" or (mode == "auto" and missing):
        if mode == "auto":
            log.info("%d class/subject combination(s) not found statically; trying browser discovery.",
                     len(missing))
        try:
            browser_books = discover_with_browser(client, classes, subjects)
            log.info("Browser discovery found %d matching book(s).", len(browser_books))
            for book in browser_books:
                if mode == "browser" or (book.class_num, book.subject) in missing:
                    books.setdefault(book.code, book)
        except DiscoveryError as exc:
            notes.append(str(exc))
            log.warning("%s", exc)

    detail = "; ".join(notes) if notes else "the official catalogue lists no English-medium book for it"
    unavailable = [(c, s, f"No book discovered ({detail})") for c, s in gaps()]
    ordered = sorted(books.values(), key=lambda b: (b.class_num, SUBJECTS.index(b.subject), b.code))
    return ordered, unavailable


# --------------------------------------------------------------------------
# Downloading (resumable, validated)
# --------------------------------------------------------------------------
def _retry_or_raise(attempt: int, label: str, reason: object) -> None:
    if attempt >= MAX_ATTEMPTS:
        raise TransientDownloadError(f"{label}: giving up after {attempt} attempts ({reason})")
    wait = min(60, 2 ** attempt)
    log.warning("  %s: %s - retry %d/%d in %ds", label, reason, attempt, MAX_ATTEMPTS - 1, wait)
    time.sleep(wait)


def download_to_part(client: OfficialClient, url: str, part: Path, kind: str, label: str) -> Path:
    """Download url into a .part file, resuming with HTTP Range when possible."""
    part.parent.mkdir(parents=True, exist_ok=True)
    attempt = 0
    while True:
        attempt += 1
        offset = part.stat().st_size if part.exists() else 0
        headers = {"Accept-Encoding": "identity"}
        if offset:
            headers["Range"] = f"bytes={offset}-"
        try:
            resp = client.get(url, stream=True, headers=headers)
        except requests.RequestException as exc:
            _retry_or_raise(attempt, label, exc)
            continue

        with resp:
            status = resp.status_code
            if status == 416 and offset:
                log.info("  %s: already fully downloaded (%s); validating.", label, human_size(offset))
                return part
            if status in (401, 403, 404, 410):
                raise NotAvailableError(f"HTTP {status} for {url}")
            if status in RETRYABLE_STATUS:
                _retry_or_raise(attempt, label, f"HTTP {status}")
                continue
            if status not in (200, 206):
                raise NotAvailableError(f"unexpected HTTP {status} for {url}")
            ctype = resp.headers.get("Content-Type", "").lower()
            if "text/html" in ctype:
                raise NotAvailableError(f"server returned a web page instead of a {kind.upper()}: {url}")

            mode, total = "wb", None
            if status == 206:
                cr = re.match(r"bytes\s+(\d+)-(\d+)/(\d+|\*)", resp.headers.get("Content-Range", ""))
                if not cr or int(cr.group(1)) != offset:
                    log.warning("  %s: unexpected byte range from server; restarting.", label)
                    part.unlink(missing_ok=True)
                    _retry_or_raise(attempt, label, "bad Content-Range")
                    continue
                mode = "ab"
                total = int(cr.group(3)) if cr.group(3).isdigit() else None
            else:
                if offset:
                    log.info("  %s: server did not resume; restarting from the beginning.", label)
                offset = 0
                length = resp.headers.get("Content-Length", "")
                total = int(length) if length.isdigit() else None

            log.info("  Downloading %s (%s)%s", label, human_size(total),
                     f", resuming at {human_size(offset)}" if offset else "")
            try:
                with part.open(mode) as fh, tqdm(total=total, initial=offset, unit="B", unit_scale=True,
                                                 unit_divisor=1024, desc=f"  {label[:40]}", leave=False) as bar:
                    for chunk in resp.iter_content(chunk_size=CHUNK_SIZE):
                        if chunk:
                            fh.write(chunk)
                            bar.update(len(chunk))
            except requests.RequestException as exc:
                _retry_or_raise(attempt, label, f"connection interrupted ({exc})")
                continue

        size = part.stat().st_size
        if size == 0:
            part.unlink(missing_ok=True)
            raise NotAvailableError(f"server sent an empty file: {url}")
        if total is not None and size < total:
            _retry_or_raise(attempt, label, f"incomplete ({size} of {total} bytes)")
            continue
        return part


# --------------------------------------------------------------------------
# Validation and assembly
# --------------------------------------------------------------------------
def validate_pdf_bytes(data: bytes, label: str) -> int:
    """Return the page count, or raise ValidationError."""
    if not data:
        raise ValidationError(f"{label}: file is empty")
    if b"%PDF-" not in data[:1024]:
        head = data.lstrip()[:15].lower()
        if head.startswith((b"<!doctype", b"<html")):
            raise ValidationError(f"{label}: is an HTML page, not a PDF")
        raise ValidationError(f"{label}: missing %PDF- signature")
    try:
        pages = len(PdfReader(io.BytesIO(data), strict=False).pages)
    except Exception as exc:  # pypdf raises several exception types for damaged files
        raise ValidationError(f"{label}: PDF could not be parsed ({exc})") from exc
    if pages < 1:
        raise ValidationError(f"{label}: PDF has no pages")
    return pages


def validate_pdf_file(path: Path) -> int:
    return validate_pdf_bytes(path.read_bytes(), path.name)


def chapter_sort_key(name: str, code: str) -> tuple[int, int, str]:
    """Order: front matter (..ps), numbered chapters (..01, ..02), then anything else."""
    stem = PurePosixPath(name).stem.lower()
    suffix = stem[len(code):] if stem.startswith(code.lower()) else stem
    if suffix in ("ps", "pr"):
        return (0, 0, suffix)
    if suffix.isdigit():
        return (1, int(suffix), suffix)
    return (2, 0, suffix)


def chapter_label(name: str, code: str) -> str:
    kind, num, suffix = chapter_sort_key(name, code)
    if kind == 0:
        return "Front matter"
    if kind == 1:
        return f"Chapter {num}"
    return f"Section {suffix.upper()}"


def read_pdfs_from_zip(zip_path: Path, code: str) -> list[tuple[str, bytes]]:
    """Validate a complete-book ZIP and return its PDFs (in memory, never extracted by name)."""
    with zip_path.open("rb") as fh:
        if fh.read(4) != b"PK\x03\x04":
            raise ValidationError(f"{zip_path.name}: not a ZIP archive")
    chapters: list[tuple[str, bytes]] = []
    try:
        with zipfile.ZipFile(zip_path) as zf:
            members = [i for i in zf.infolist() if not i.is_dir() and i.filename.lower().endswith(".pdf")]
            if not members:
                raise ValidationError(f"{zip_path.name}: ZIP contains no PDFs")
            if sum(i.file_size for i in members) > MAX_UNZIPPED_BYTES:
                raise ValidationError(f"{zip_path.name}: ZIP expands to an implausible size; refusing")
            for info in members:
                data = zf.read(info)  # raises BadZipFile on CRC mismatch
                name = PurePosixPath(info.filename.replace("\\", "/")).name
                validate_pdf_bytes(data, name)
                if not name.lower().startswith(code.lower()):
                    log.warning("  Unexpected file in ZIP: %s", name)
                chapters.append((name, data))
    except zipfile.BadZipFile as exc:
        raise ValidationError(f"{zip_path.name}: corrupt ZIP ({exc})") from exc
    chapters.sort(key=lambda item: chapter_sort_key(item[0], code))
    return chapters


def merge_pdfs(chapters: list[tuple[str, bytes]], out_part: Path, code: str) -> int:
    writer = PdfWriter()
    try:
        for name, data in chapters:
            writer.append(io.BytesIO(data), outline_item=chapter_label(name, code), import_outline=False)
        with out_part.open("wb") as fh:
            writer.write(fh)
    except Exception as exc:
        out_part.unlink(missing_ok=True)
        raise ValidationError(f"could not merge chapter PDFs ({exc})") from exc
    try:
        return validate_pdf_file(out_part)
    except ValidationError:
        out_part.unlink(missing_ok=True)
        raise


# --------------------------------------------------------------------------
# Per-book workflow
# --------------------------------------------------------------------------
def find_complete_book_url(client: OfficialClient, book: Book) -> tuple[str, str]:
    """Prefer a link found on the official book page; else the portal's naming scheme."""
    try:
        resp = client.get(book.page_url)
        with resp:
            if resp.status_code == 200:
                m = re.search(rf"""["']([^"'<>\s]*{re.escape(book.code)}dd\.zip)["']""", resp.text, re.I)
                if m:
                    url = urljoin(resp.url, m.group(1))
                    if is_official_url(url):
                        return url, "linked from the official book page"
    except (requests.RequestException, NcertError) as exc:
        log.debug("Could not read book page %s: %s", book.page_url, exc)
    url = urljoin(BASE_URL, f"textbook/pdf/{book.code}dd.zip")
    return url, "NCERT complete-book naming scheme, accepted only after content validation"


def download_chapter_pdfs(client: OfficialClient, book: Book, work_dir: Path) -> list[tuple[str, bytes]]:
    """Fallback: download front matter plus each numbered chapter PDF."""
    names = [f"{book.code}ps.pdf"] + [f"{book.code}{n:02d}.pdf"
                                      for n in range(max(1, book.chapter_start), book.chapter_end + 1)]
    chapters = []
    for name in names:
        url = urljoin(BASE_URL, f"textbook/pdf/{name}")
        part = work_dir / f"{name}.part"
        try:
            download_to_part(client, url, part, "pdf", name)
            data = part.read_bytes()
            validate_pdf_bytes(data, name)
        except (NotAvailableError, ValidationError) as exc:
            part.unlink(missing_ok=True)
            if name.endswith("ps.pdf"):
                log.info("  No front-matter PDF (%s); continuing.", exc)
                continue
            raise
        chapters.append((name, data))
    return chapters


def fetch_book_contents(client: OfficialClient, book: Book, work_dir: Path) -> tuple[list[tuple[str, bytes]], str]:
    zip_url, how = find_complete_book_url(client, book)
    zip_part = work_dir / f"{book.code}dd.zip.part"
    try:
        download_to_part(client, zip_url, zip_part, "zip", f"{book.code}dd.zip")
        chapters = read_pdfs_from_zip(zip_part, book.code)
        log.info("  Complete-book ZIP verified: %d PDF part(s).", len(chapters))
        return chapters, f"complete-book ZIP {zip_url} ({how})"
    except (NotAvailableError, ValidationError) as exc:
        zip_part.unlink(missing_ok=True)
        log.warning("  Complete-book ZIP unavailable (%s). Falling back to chapter PDFs.", exc)
    chapters = download_chapter_pdfs(client, book, work_dir)
    return chapters, "individual chapter PDFs (complete-book ZIP unavailable)"


def output_filename(book: Book, taken: set[str]) -> str:
    base = f"Class_{book.class_num}_{safe_name(book.subject)}_{safe_name(book.title)}"
    name = f"{base}.pdf"
    if name.lower() in taken:
        name = f"{base}_{book.code}.pdf"
    taken.add(name.lower())
    return name


def save_chapters(chapters: list[tuple[str, bytes]], folder: Path) -> None:
    folder.mkdir(parents=True, exist_ok=True)
    for name, data in chapters:
        tmp = folder / f"{name}.part"
        tmp.write_bytes(data)
        os.replace(tmp, folder / name)


def process_book(client: OfficialClient, book: Book, dest_root: Path, overwrite: bool,
                 keep_chapters: bool, final: Path, report: Report) -> None:
    log.info("  Book: %s  [code %s]", book.title, book.code)
    log.info("  Official page: %s", book.page_url)

    if final.exists() and not overwrite:
        try:
            pages = validate_pdf_file(final)
            log.info("  Skipped: valid file already exists (%d pages): %s", pages, final)
            report.skipped.append((book, final))
            return
        except ValidationError as exc:
            log.warning("  Existing file is invalid (%s); downloading again.", exc)

    work_dir = dest_root / PARTIAL_DIRNAME / book.code
    merged_part = final.with_name(final.name + ".part")
    try:
        chapters, source = fetch_book_contents(client, book, work_dir)
        pages = merge_pdfs(chapters, merged_part, book.code)
        os.replace(merged_part, final)  # atomic on the same drive
        if keep_chapters:
            save_chapters(chapters, final.with_name(f"{final.stem}_chapters"))
        shutil.rmtree(work_dir, ignore_errors=True)
        log.info("  Saved %d pages (%s) -> %s", pages, human_size(final.stat().st_size), final)
        report.downloaded.append((book, final, source))
    except TransientDownloadError as exc:
        log.error("  FAILED: %s", exc)
        report.failed.append((book, f"{exc}; partial data kept, re-run to resume"))
    except (NcertError, requests.RequestException, OSError) as exc:
        log.error("  FAILED: %s", exc)
        report.failed.append((book, str(exc)))


# --------------------------------------------------------------------------
# Reporting, logging, CLI
# --------------------------------------------------------------------------
def save_catalogue(books: list[Book], path: Path) -> None:
    data = [{**asdict(b), "page_url": b.page_url} for b in books]
    tmp = path.with_name(path.name + ".part")
    tmp.write_text(json.dumps(data, indent=2, ensure_ascii=False), encoding="utf-8")
    os.replace(tmp, path)


def print_summary(report: Report, dest_root: Path, log_path: Path) -> None:
    log.info("\n" + "=" * 72)
    log.info("SUMMARY")
    log.info("=" * 72)
    log.info("Total textbooks discovered : %d", len(report.discovered))
    log.info("Downloaded successfully    : %d", len(report.downloaded))
    log.info("Existing files skipped     : %d", len(report.skipped))
    log.info("Failed downloads           : %d", len(report.failed))
    log.info("Unavailable (not found)    : %d", len(report.unavailable))
    for book, path, source in report.downloaded:
        log.info("  + %s\n      from %s", path, source)
    for book, path in report.skipped:
        log.info("  = %s (already present)", path)
    if report.failed:
        log.info("\nFailed - download manually from the official page:")
        for book, reason in report.failed:
            log.info("  ! Class %d %s - %s: %s\n      %s",
                     book.class_num, book.subject, book.title, reason, book.page_url)
    if report.unavailable:
        log.info("\nNot discovered - check manually at %s:", CATALOGUE_URL)
        for class_num, subject, reason in report.unavailable:
            log.info("  ? Class %d %s: %s", class_num, subject, reason)
    log.info("\nDestination : %s", dest_root)
    log.info("Log file    : %s", log_path)


def setup_logging(log_path: Path) -> None:
    if hasattr(sys.stdout, "reconfigure"):
        try:
            sys.stdout.reconfigure(encoding="utf-8", errors="replace")
        except (ValueError, OSError):
            pass
    log.setLevel(logging.DEBUG)
    log.handlers.clear()
    log.propagate = False
    file_handler = logging.FileHandler(log_path, encoding="utf-8")
    file_handler.setLevel(logging.DEBUG)
    file_handler.setFormatter(logging.Formatter("%(asctime)s [%(levelname)s] %(message)s"))
    console = logging.StreamHandler(sys.stdout)
    console.setLevel(logging.INFO)
    console.setFormatter(logging.Formatter("%(message)s"))
    log.addHandler(file_handler)
    log.addHandler(console)
    logging.getLogger("pypdf").setLevel(logging.ERROR)


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Download official NCERT English-medium textbooks as PDFs.")
    p.add_argument("--dest", type=Path, default=DEFAULT_DEST, help=f"output folder (default: {DEFAULT_DEST})")
    p.add_argument("--overwrite", action="store_true", help="re-download even if a valid PDF already exists")
    p.add_argument("--classes", type=int, nargs="+", choices=sorted(ROMAN), default=sorted(ROMAN))
    p.add_argument("--subjects", nargs="+", choices=SUBJECTS, default=list(SUBJECTS))
    p.add_argument("--discovery", choices=("auto", "static", "browser"), default="auto",
                   help="auto: static parse, Playwright only for gaps (default)")
    p.add_argument("--dry-run", action="store_true", help="discover and list books without downloading")
    p.add_argument("--keep-chapters", action="store_true", help="also keep the individual chapter PDFs")
    p.add_argument("--delay", type=float, default=2.0, help="minimum seconds between requests (default 2)")
    p.add_argument("--connect-timeout", type=float, default=15.0)
    p.add_argument("--read-timeout", type=float, default=60.0)
    p.add_argument("--user-agent", default=DEFAULT_USER_AGENT)
    p.add_argument("--exclude", nargs="+", default=[], metavar="WORD",
                   help="skip books whose title contains any of these words (case-insensitive)")
    p.add_argument("--codes", nargs="+", default=[], metavar="CODE",
                   help="download only these book codes, e.g. fecu1 gees1")
    return p.parse_args(argv)

def apply_filters(books: list[Book], exclude: list[str], codes: list[str]) -> list[Book]:
    """Drop books by title keyword (--exclude) or keep only listed codes (--codes)."""
    words = [w.lower() for w in exclude]
    wanted = {c.lower() for c in codes}
    kept = []
    for book in books:
        if wanted and book.code not in wanted:
            continue
        if any(w in book.title.lower() for w in words):
            log.info("Excluded by filter: Class %d %s - %s", book.class_num, book.subject, book.title)
            continue
        kept.append(book)
    if wanted - {b.code for b in kept}:
        log.warning("Codes not found in catalogue: %s", ", ".join(sorted(wanted - {b.code for b in kept})))
    return kept

def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    dest_root = args.dest.expanduser().resolve()
    classes = sorted(set(args.classes))
    subjects = [s for s in SUBJECTS if s in args.subjects]

    for c in classes:
        for s in subjects:
            (dest_root / CLASS_DIRS[c] / s).mkdir(parents=True, exist_ok=True)
    log_path = dest_root / "download_log.txt"
    setup_logging(log_path)

    report = Report()
    client = OfficialClient(args.user_agent, max(0.5, args.delay), args.connect_timeout, args.read_timeout)
    try:
        with logging_redirect_tqdm(loggers=[log]):
            log.info("=" * 72)
            log.info("NCERT textbook downloader | classes %s | %s | dest %s",
                     classes, ", ".join(subjects), dest_root)
            client.load_robots()
            books, unavailable = discover_books(client, classes, subjects, args.discovery)
            save_catalogue(books, dest_root / "catalogue.json")  # full list, before filters
            books = apply_filters(books, args.exclude, args.codes)
            report.discovered, report.unavailable = books, unavailable

            taken: set[str] = set()
            planned = {b.code: dest_root / CLASS_DIRS[b.class_num] / b.subject / output_filename(b, taken)
                       for b in books}
            done = 0
            for c in classes:
                for s in subjects:
                    group = [b for b in books if b.class_num == c and b.subject == s]
                    log.info("\n=== Class %d / %s: %d book(s) ===", c, s, len(group))
                    if not group:
                        log.warning("  No book discovered (see summary for the manual link).")
                    for book in group:
                        done += 1
                        log.info("(%d/%d)", done, len(books))
                        if args.dry_run:
                            log.info("  [dry run] %s -> %s\n  %s", book.title, planned[book.code], book.page_url)
                            continue
                        process_book(client, book, dest_root, args.overwrite, args.keep_chapters,
                                     planned[book.code], report)
            print_summary(report, dest_root, log_path)
    except KeyboardInterrupt:
        log.warning("\nInterrupted. Partial downloads are kept; run the same command again to resume.")
        print_summary(report, dest_root, log_path)
        return 130
    return 1 if report.failed else 0

if __name__ == "__main__":
    sys.exit(main())