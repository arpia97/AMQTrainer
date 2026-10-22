"""Import AniList JSON or MyAnimeList XML exports and download AnisongDB songs.

This is intentionally a single-file, standard-library Python application.  The
Tkinter UI is a thin layer over the parser, AnisongDB client, and downloader so
the data model can be reused by a future training-data script.

The AnisongDB API is documented by its live OpenAPI schema:
https://anisongdb.com/openapi.json
"""

from __future__ import annotations

import argparse
import csv
import ctypes
import datetime as dt
import difflib
import json
import mimetypes
import os
import random
import re
import shutil
import sys
import subprocess
import tempfile
import threading
import time
import traceback
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from collections import OrderedDict
from dataclasses import asdict, dataclass, field
from itertools import product
from pathlib import Path
from typing import Any, Callable, Iterable, Optional


API_BASE = "https://anisongdb.com/api"
MEDIA_BASE = "https://naedist.animemusicquiz.com/"
LIBRARY_URL = "https://animemusicquiz.com/libraryMasterList"
MAX_BATCH = 500
DEFAULT_TIMEOUT = 45
APP_VERSION = "1.0.1"
# Public GitHub repository used for release/update checks.
UPDATE_REPOSITORY = os.environ.get("AMQ_TRAINER_UPDATE_REPOSITORY", "arpia97/AMQTrainer").strip()
UPDATE_ASSET_NAME = "AMQTrainer.exe"
DIRECT_SONG_COLLECTION_SOURCES = {"AMQ", "AniSongDB"}

ANILIST_STATUS_NAMES = {
    "CURRENT": "Watching",
    "REPEATING": "Rewatching",
    "COMPLETED": "Completed",
    "PAUSED": "On Hold",
    "DROPPED": "Dropped",
    "PLANNING": "Planning",
}

MAL_STATUS_NAMES = {
    "Watching": "Watching",
    "Completed": "Completed",
    "On-Hold": "On Hold",
    "Dropped": "Dropped",
    "Plan to Watch": "Planning",
    "Rewatching": "Rewatching",
}

SONG_TYPES = ("opening", "ending", "insert")
SONG_CATEGORIES = ("standard", "character", "chanting", "instrumental", "other")

UI_BACKGROUND = "#1c1b20"
UI_TRANSPARENT = "#ff00fe"
POPUP_WIDTH = 545
POPUP_HEIGHT = 536
UI_PANEL = "#201f24"
UI_PANEL_DARK = "#17161a"
UI_TEXT = "#f7f4f6"
UI_MUTED = "#b6afb8"
UI_PINK = "#f52d5b"
# Dominant active red from the Profile menu's Kanon button artwork.
UI_PINK_DARK = "#f12f5a"
UI_PINK_LIGHT = "#ff9db7"
UI_MAROON = "#7b3849"


def _ui_asset_root() -> Path:
    """Find bundled Kanon assets both from source and from a PyInstaller build."""
    candidates = [
        Path(__file__).resolve().parent / "Kanon-UI",
        Path(__file__).resolve().parent / "dist" / "Kanon-UI",
    ]
    bundle_root = getattr(sys, "_MEIPASS", None)
    if bundle_root:
        candidates.insert(0, Path(bundle_root) / "Kanon-UI")
    return next((path for path in candidates if path.exists()), candidates[0])


def _clean(value: Any) -> str:
    return str(value).strip() if value is not None else ""


def _first_nonempty(*values: Any) -> str:
    for value in values:
        if _clean(value):
            return _clean(value)
    return ""


def _safe_filename(value: str, limit: int = 150) -> str:
    value = re.sub(r"[<>:\"/\\|?*\x00-\x1f]", "_", value)
    value = re.sub(r"\s+", " ", value).strip(" .")
    return (value or "untitled")[:limit]


def _chunks(values: list[int], size: int = MAX_BATCH) -> Iterable[list[int]]:
    for index in range(0, len(values), size):
        yield values[index : index + size]


@dataclass
class AnimeEntry:
    """One anime entry in a normalized representation."""

    source_id: str
    title: str
    anilist_id: Optional[int] = None
    mal_id: Optional[int] = None
    status: str = ""
    source: str = ""
    extra: dict[str, Any] = field(default_factory=dict)

    @property
    def key(self) -> str:
        if self.anilist_id:
            return f"anilist:{self.anilist_id}"
        if self.mal_id:
            return f"mal:{self.mal_id}"
        return f"source:{self.source}:{self.source_id}"


@dataclass
class ListBucket:
    name: str
    kind: str
    entries: list[AnimeEntry] = field(default_factory=list)
    song_count: Optional[int] = None

    def add(self, entry: AnimeEntry) -> None:
        if all(existing.key != entry.key for existing in self.entries):
            self.entries.append(entry)


@dataclass
class AnimeCollection:
    source: str
    buckets: OrderedDict[str, ListBucket]
    path: str = ""
    songs: list[dict[str, Any]] = field(default_factory=list)

    @property
    def total_entries(self) -> int:
        return len({entry.key for bucket in self.buckets.values() for entry in bucket.entries})

    def all_entries(self) -> list[AnimeEntry]:
        entries: dict[str, AnimeEntry] = {}
        for bucket in self.buckets.values():
            for entry in bucket.entries:
                entries.setdefault(entry.key, entry)
        return list(entries.values())


def _bucket(buckets: OrderedDict[str, ListBucket], name: str, kind: str) -> ListBucket:
    if name not in buckets:
        buckets[name] = ListBucket(name=name, kind=kind)
    return buckets[name]


def _anilist_entry(raw: dict[str, Any]) -> AnimeEntry:
    media = raw.get("media") or {}
    title = media.get("title") or {}
    anilist_id = raw.get("mediaId") or media.get("id")
    mal_id = media.get("idMal")
    return AnimeEntry(
        source_id=str(anilist_id or ""),
        title=_first_nonempty(title.get("english"), title.get("romaji"), title.get("native"), f"AniList {anilist_id}"),
        anilist_id=int(anilist_id) if anilist_id else None,
        mal_id=int(mal_id) if mal_id else None,
        status=ANILIST_STATUS_NAMES.get(_clean(raw.get("status")).upper(), _clean(raw.get("status"))),
        source="AniList",
        extra={
            "progress": raw.get("progress"),
            "customLists": raw.get("customLists") or {},
            "title_english": _clean(title.get("english")),
            "title_romaji": _clean(title.get("romaji")),
            "title_native": _clean(title.get("native")),
        },
    )


def parse_anilist(path: str | Path) -> AnimeCollection:
    with open(path, "r", encoding="utf-8-sig") as handle:
        data = json.load(handle)

    lists = ((data.get("MediaListCollection") or {}).get("lists") or [])
    buckets: OrderedDict[str, ListBucket] = OrderedDict()
    for raw_list in lists:
        raw_name = _clean(raw_list.get("name")) or "Unnamed list"
        is_custom = bool(raw_list.get("isCustomList"))
        name = raw_name if is_custom else ANILIST_STATUS_NAMES.get(raw_name.upper(), raw_name)
        kind = "custom" if is_custom else "status"
        destination = _bucket(buckets, name, kind)
        for raw_entry in raw_list.get("entries") or []:
            if not isinstance(raw_entry, dict):
                continue
            entry = _anilist_entry(raw_entry)
            if entry.source_id:
                destination.add(entry)

            # Some AniList exports include custom lists only as boolean flags on
            # status entries.  Add those memberships without duplicating entries.
            for custom_name, enabled in (raw_entry.get("customLists") or {}).items():
                if enabled:
                    _bucket(buckets, _clean(custom_name), "custom").add(entry)

    if not buckets:
        raise ValueError("The JSON file does not contain MediaListCollection.lists.")
    return AnimeCollection(source="AniList", buckets=buckets, path=str(path))


def _xml_text(element: ET.Element, tag: str) -> str:
    child = element.find(tag)
    return _clean(child.text if child is not None else "")


def parse_mal(path: str | Path) -> AnimeCollection:
    root = ET.parse(path).getroot()
    buckets: OrderedDict[str, ListBucket] = OrderedDict()
    for raw in root.findall(".//anime"):
        mal_id = _xml_text(raw, "series_animedb_id")
        if not mal_id:
            continue
        status_raw = _xml_text(raw, "my_status")
        status = MAL_STATUS_NAMES.get(status_raw, status_raw or "Uncategorized")
        entry = AnimeEntry(
            source_id=mal_id,
            title=_xml_text(raw, "series_title") or f"MAL {mal_id}",
            mal_id=int(mal_id),
            status=status,
            source="MAL",
        extra={"type": _xml_text(raw, "series_type"), "tags": _xml_text(raw, "my_tags")},
        )
        _bucket(buckets, status, "status").add(entry)

        # The old MAL XML export does not have a first-class custom-list field.
        # Its my_tags field is the closest portable representation, so expose
        # each tag as a selectable custom bucket.
        tags = [tag.strip() for tag in re.split(r"[,;]", entry.extra.get("tags", "")) if tag.strip()]
        for tag in tags:
            _bucket(buckets, f"Tag: {tag}", "custom").add(entry)

    if not buckets:
        raise ValueError("The XML file does not contain any <anime> entries.")
    return AnimeCollection(source="MAL", buckets=buckets, path=str(path))


def _amq_song_type(song_info: dict[str, Any]) -> str:
    type_name = {1: "Opening", 2: "Ending", 3: "Insert"}.get(song_info.get("type"), "Other")
    number = song_info.get("typeNumber")
    return f"{type_name} {number}" if number not in (None, "", 0) else type_name


def _amq_song_record(raw: dict[str, Any]) -> dict[str, Any]:
    info = raw.get("songInfo") or {}
    site_ids = info.get("siteIds") or {}
    names = info.get("animeNames") or {}
    composer = info.get("composerInfo") or {}
    arranger = info.get("arrangerInfo") or {}
    return {
        "annId": info.get("annId"),
        "annSongId": info.get("annSongId"),
        "amqSongId": info.get("annSongId"),
        "linked_ids": {
            "anilist": site_ids.get("aniListId"),
            "myanimelist": site_ids.get("malId"),
            "ann": site_ids.get("annId") or info.get("annId"),
        },
        "animeENName": names.get("english") or names.get("romaji") or "Unknown anime",
        "animeJPName": names.get("romaji") or names.get("english") or "Unknown anime",
        "animeAltName": ", ".join(info.get("altAnimeNames") or []),
        "animeVintage": info.get("vintage") or "",
        "animeType": info.get("animeType") or "",
        "songType": _amq_song_type(info),
        "songCategory": "standard",
        "songName": info.get("songName") or "Untitled",
        "songArtist": info.get("artist") or "Unknown artist",
        "songComposer": composer.get("name") or "",
        "songArranger": arranger.get("name") or "",
        "songDifficulty": info.get("animeDifficulty"),
        "rebroadcast": info.get("rebroadcast", 0),
        "dub": info.get("dub", 0),
        "audio": raw.get("videoUrl") or "",
        "HQ": "",
        "MQ": "",
        "_source": "AMQ",
        "_amq_song_number": raw.get("songNumber"),
    }


def parse_amq(path: str | Path) -> AnimeCollection:
    with open(path, "r", encoding="utf-8-sig") as handle:
        data = json.load(handle)
    raw_songs = data.get("songs") if isinstance(data, dict) else None
    if not isinstance(raw_songs, list):
        raise ValueError("The JSON file does not contain an AMQ songs export.")

    songs: list[dict[str, Any]] = []
    entries_by_key: OrderedDict[str, AnimeEntry] = OrderedDict()
    for raw in raw_songs:
        if not isinstance(raw, dict) or not isinstance(raw.get("songInfo"), dict):
            continue
        song = _amq_song_record(raw)
        song_id = song.get("annSongId") or song.get("_amq_song_number")
        if any((existing.get("annSongId") or existing.get("_amq_song_number")) == song_id for existing in songs):
            continue
        songs.append(song)
        linked = song.get("linked_ids") or {}
        key = f"ann:{linked.get('ann') or song.get('animeENName')}"
        if key not in entries_by_key:
            entries_by_key[key] = AnimeEntry(
                source_id=str(linked.get("ann") or song.get("_amq_song_number") or ""),
                title=song.get("animeENName") or song.get("animeJPName") or "Unknown anime",
                anilist_id=int(linked["anilist"]) if linked.get("anilist") else None,
                mal_id=int(linked["myanimelist"]) if linked.get("myanimelist") else None,
                source="AMQ",
                extra={"animeType": song.get("animeType"), "vintage": song.get("animeVintage")},
            )

    if not songs:
        raise ValueError("The AMQ JSON file does not contain any usable songs.")
    bucket = ListBucket(name="AMQ Export", kind="AMQ", entries=list(entries_by_key.values()), song_count=len(songs))
    return AnimeCollection(source="AMQ", buckets=OrderedDict([(bucket.name, bucket)]), path=str(path), songs=songs)


def _anisongdb_song_record(raw: dict[str, Any]) -> dict[str, Any]:
    """Normalize a raw AnisongDB SongList record for the downloader/player."""
    record = dict(raw)
    record["linked_ids"] = dict(raw.get("linked_ids") or {})
    record["annId"] = raw.get("annId") or raw.get("annSongId")
    record["annSongId"] = raw.get("annSongId") or raw.get("amqSongId")
    record["amqSongId"] = raw.get("amqSongId") or raw.get("annSongId")
    alt_names = raw.get("animeAltName") or []
    if isinstance(alt_names, (list, tuple)):
        alt_names = ", ".join(_clean(name) for name in alt_names if _clean(name))
    record["animeAltName"] = _clean(alt_names)
    record["songCategory"] = _clean(raw.get("songCategory")) or "standard"
    record["dub"] = raw.get("dub", raw.get("isDub", 0))
    record["rebroadcast"] = raw.get("rebroadcast", raw.get("isRebroadcast", 0))
    record["_source"] = "AniSongDB"
    return record


def parse_anisongdb(path: str | Path) -> AnimeCollection:
    """Read the array-of-song-records JSON exported by AnisongDB."""
    with open(path, "r", encoding="utf-8-sig") as handle:
        data = json.load(handle)
    if not isinstance(data, list):
        raise ValueError("The JSON file does not contain an AnisongDB song list.")

    songs = [
        _anisongdb_song_record(raw)
        for raw in data
        if isinstance(raw, dict) and (_clean(raw.get("annSongId")) or _clean(raw.get("animeENName")) or _clean(raw.get("animeJPName")))
    ]
    if not songs:
        raise ValueError("The AnisongDB JSON file does not contain any usable songs.")

    entries_by_key: OrderedDict[str, AnimeEntry] = OrderedDict()
    for song in songs:
        linked = song.get("linked_ids") or {}
        anilist_id = linked.get("anilist")
        mal_id = linked.get("myanimelist")
        title_english = _clean(song.get("animeENName"))
        title_romaji = _clean(song.get("animeJPName"))
        title = title_english or title_romaji or "Unknown anime"
        source_id = str(anilist_id or mal_id or title)
        entry = AnimeEntry(
            source_id=source_id,
            title=title,
            anilist_id=int(anilist_id) if anilist_id else None,
            mal_id=int(mal_id) if mal_id else None,
            source="AniSongDB",
            extra={
                "animeType": song.get("animeType"),
                "vintage": song.get("animeVintage"),
                "title_english": title_english,
                "title_romaji": title_romaji,
            },
        )
        entries_by_key.setdefault(entry.key, entry)

    bucket = ListBucket(
        name="AniSongDB Export",
        kind="AniSongDB",
        entries=list(entries_by_key.values()),
        song_count=len(songs),
    )
    return AnimeCollection(
        source="AniSongDB",
        buckets=OrderedDict([(bucket.name, bucket)]),
        path=str(path),
        songs=songs,
    )


def parse_profile_export(data: dict[str, Any], path: str | Path) -> AnimeCollection:
    """Read an AMQ Trainer profile export produced by the profile editor."""
    if data.get("format") != "AMQ Trainer Profile Export":
        raise ValueError("The JSON file is not an AMQ Trainer profile export.")
    buckets: OrderedDict[str, ListBucket] = OrderedDict()
    for raw_bucket in data.get("lists") or data.get("buckets") or []:
        if not isinstance(raw_bucket, dict):
            continue
        name = _clean(raw_bucket.get("name"))
        if not name:
            continue
        bucket = ListBucket(
            name=name,
            kind=_clean(raw_bucket.get("kind")) or "custom",
            song_count=raw_bucket.get("song_count"),
        )
        for raw_entry in raw_bucket.get("entries") or []:
            if isinstance(raw_entry, dict):
                try:
                    bucket.add(AnimeEntry(**raw_entry))
                except TypeError:
                    continue
        buckets[name] = bucket
    songs = [song for song in data.get("songs") or [] if isinstance(song, dict)]
    if not buckets:
        raise ValueError("The profile export does not contain any lists.")
    return AnimeCollection(source="AMQ", buckets=buckets, path=str(path), songs=songs)


def parse_export(path: str | Path) -> AnimeCollection:
    path = Path(path)
    suffix = path.suffix.lower()
    if suffix == ".json":
        with open(path, "r", encoding="utf-8-sig") as handle:
            data = json.load(handle)
        if isinstance(data, dict) and data.get("format") == "AMQ Trainer Profile Export":
            return parse_profile_export(data, path)
        if isinstance(data, dict) and isinstance(data.get("songs"), list):
            return parse_amq(path)
        if isinstance(data, list):
            return parse_anisongdb(path)
        return parse_anilist(path)
    if suffix == ".xml":
        return parse_mal(path)
    raise ValueError("Choose an AniList/MAL/AMQ/AnisongDB export (.json or .xml).")


def parse_export_group(paths: Iterable[str | Path], list_name: str) -> AnimeCollection:
    """Merge multiple JSON exports into one named custom list.

    Each file is parsed with the normal AniList/AMQ parser first, then entries
    and song records are deduplicated by their stable identifiers.  Keeping
    this at the normalized collection layer means grouped imports behave the
    same as a single imported list everywhere else in the application.
    """
    normalized_paths = [Path(path) for path in paths]
    if not normalized_paths:
        raise ValueError("Choose at least one JSON file.")
    if not _clean(list_name):
        raise ValueError("A name is required for the JSON list group.")
    collections = [parse_export(path) for path in normalized_paths]
    if any(collection.source not in {"AniList", "AMQ", "AniSongDB"} for collection in collections):
        raise ValueError("Grouped imports support JSON files only.")

    entries: OrderedDict[str, AnimeEntry] = OrderedDict()
    songs: list[dict[str, Any]] = []
    song_keys: set[str] = set()
    for collection in collections:
        for entry in collection.all_entries():
            entries.setdefault(entry.key, entry)
        for index, song in enumerate(collection.songs):
            key = _clean(song.get("annSongId") or song.get("amqSongId") or song.get("_amq_song_number") or song.get("download_path"))
            key = key or f"song-{index}-{len(songs)}"
            if key not in song_keys:
                song_keys.add(key)
                songs.append(song)

    source = collections[0].source if all(collection.source == collections[0].source for collection in collections) else "Mixed"
    bucket = ListBucket(name=_clean(list_name), kind="custom", entries=list(entries.values()), song_count=len(songs) if songs else None)
    return AnimeCollection(
        source=source,
        buckets=OrderedDict([(bucket.name, bucket)]),
        path=";".join(str(path) for path in normalized_paths),
        songs=songs,
    )


class AnisongDBClient:
    def __init__(self, base_url: str = API_BASE, timeout: int = DEFAULT_TIMEOUT):
        self.base_url = base_url.rstrip("/")
        self.timeout = timeout

    def _post(self, endpoint: str, payload: dict[str, Any]) -> list[dict[str, Any]]:
        body = json.dumps(payload).encode("utf-8")
        request = urllib.request.Request(
            f"{self.base_url}/{endpoint}",
            data=body,
            headers={"Content-Type": "application/json", "Accept": "application/json", "User-Agent": "AMQTrainer/1.0"},
            method="POST",
        )
        try:
            with urllib.request.urlopen(request, timeout=self.timeout) as response:
                decoded = json.loads(response.read().decode("utf-8"))
        except urllib.error.HTTPError as exc:
            detail = exc.read().decode("utf-8", errors="replace")
            raise RuntimeError(f"AnisongDB returned HTTP {exc.code}: {detail[:500]}") from exc
        except urllib.error.URLError as exc:
            raise RuntimeError(f"Could not reach AnisongDB: {exc.reason}") from exc
        if not isinstance(decoded, list):
            raise RuntimeError("AnisongDB returned an unexpected response shape.")
        return decoded

    def songs_for_entries(
        self,
        entries: Iterable[AnimeEntry],
        song_types: Optional[list[str]] = None,
        song_categories: Optional[list[str]] = None,
    ) -> list[dict[str, Any]]:
        entries_by_id: dict[int, AnimeEntry] = {}
        title_fallback: list[AnimeEntry] = []
        for entry in entries:
            # The current public API batches MAL IDs (and ANN IDs), but not
            # AniList IDs. AniList exports normally include idMal, so use that
            # stable cross-link and retain a title fallback for missing links.
            identifier = entry.mal_id
            if identifier:
                entries_by_id[int(identifier)] = entry
            elif entry.source == "AniList":
                title_fallback.append(entry)
        if not entries_by_id:
            songs: dict[int, dict[str, Any]] = {}
        else:
            songs = {}

        for batch in _chunks(list(entries_by_id)):
            payload: dict[str, Any] = {"mal_ids": batch, "ignore_duplicate": False}
            filters: dict[str, Any] = {}
            if song_types:
                filters["song_types"] = song_types
            if song_categories:
                filters["song_categories"] = song_categories
            if filters:
                payload["filters"] = filters
            for song in self._post("mal_ids_request", payload):
                song_id = song.get("annSongId") or song.get("amqSongId")
                if song_id is not None:
                    songs[int(song_id)] = song

        # Missing AniList-to-MAL links are uncommon, but should not disappear
        # silently. Search by title and retain only results that link back to
        # the AniList ID when the service supplies that link.
        for entry in title_fallback:
            payload = {
                "anime_search_filter": {"search": entry.title, "partial_match": True, "match_case": False},
                "ignore_duplicate": False,
            }
            filters = {}
            if song_types:
                filters["song_types"] = song_types
            if song_categories:
                filters["song_categories"] = song_categories
            if filters:
                payload["filters"] = filters
            try:
                candidates = self._post("search_request", payload)
            except RuntimeError:
                continue
            for song in candidates:
                linked = song.get("linked_ids") or {}
                if entry.anilist_id and linked.get("anilist") and int(linked["anilist"]) != int(entry.anilist_id):
                    continue
                song_id = song.get("annSongId") or song.get("amqSongId")
                if song_id is not None:
                    songs[int(song_id)] = song
        return list(songs.values())


def song_label(song: dict[str, Any]) -> str:
    return f"{song.get('animeENName') or song.get('animeJPName') or 'Unknown anime'} — {song.get('songType', '').upper()} — {song.get('songName', '')} — {song.get('songArtist', '')}"


class SongDownloader:
    def __init__(self, output_dir: str | Path, preferred_media: str = "audio", timeout: int = DEFAULT_TIMEOUT):
        self.output_dir = Path(output_dir)
        self.preferred_media = preferred_media
        self.timeout = timeout

    def _media_url(self, song: dict[str, Any]) -> tuple[str, str]:
        choices = [self.preferred_media] + [value for value in ("audio", "HQ", "MQ") if value != self.preferred_media]
        for key in choices:
            url = _clean(song.get(key))
            if url:
                # AnisongDB commonly returns AMQ media as a filename such as
                # "qi299l.mp3". Older records may contain a full URL, so only
                # prefix values that do not already have a URL scheme.
                if not urllib.parse.urlparse(url).scheme:
                    url = urllib.parse.urljoin(MEDIA_BASE, url.lstrip("/"))
                return url, key
        return "", ""

    def destination_for(self, song: dict[str, Any]) -> Optional[Path]:
        url, _media_key = self._media_url(song)
        if not url:
            return None
        extension = Path(urllib.parse.urlparse(url).path).suffix.lower()
        if not extension or len(extension) > 5:
            extension = mimetypes.guess_extension(_clean(song.get("mimeType"))) or ".mp3"
        filename = _safe_filename(
            f"{song.get('annId', 'unknown')} - {song.get('animeENName') or song.get('animeJPName', 'unknown')} - "
            f"{song.get('songType', 'song')} - {song.get('songName', 'untitled')} - {song.get('songArtist', 'unknown')}"
        ) + extension
        return self.output_dir / filename

    def existing_count(self, songs: list[dict[str, Any]]) -> int:
        return sum(1 for song in songs if (destination := self.destination_for(song)) and destination.exists() and destination.stat().st_size > 0)

    def download(
        self,
        songs: list[dict[str, Any]],
        progress: Optional[Callable[[int, int, dict[str, Any], str], None]] = None,
        cancel_event: Optional[threading.Event] = None,
    ) -> list[dict[str, Any]]:
        self.output_dir.mkdir(parents=True, exist_ok=True)
        manifest: list[dict[str, Any]] = []
        total = len(songs)
        for index, song in enumerate(songs, start=1):
            if cancel_event is not None and cancel_event.is_set():
                break
            url, media_key = self._media_url(song)
            record = dict(song)
            record.pop("_list_entry", None)
            record.update({"download_status": "", "download_path": "", "download_source": media_key})
            if not url:
                record["download_status"] = "no media link"
                manifest.append(record)
                if progress:
                    progress(index, total, record, "no media link")
                continue

            destination = self.destination_for(song)
            if destination is None:
                record["download_status"] = "no media link"
                manifest.append(record)
                if progress:
                    progress(index, total, record, "no media link")
                continue
            record["download_path"] = str(destination)
            if destination.exists() and destination.stat().st_size > 0:
                record["download_status"] = "skipped (already exists)"
            else:
                partial = destination.with_suffix(destination.suffix + ".part")
                try:
                    request = urllib.request.Request(url, headers={"User-Agent": "AMQTrainer/1.0"})
                    with urllib.request.urlopen(request, timeout=self.timeout) as response, open(partial, "wb") as output:
                        while True:
                            block = response.read(1024 * 256)
                            if not block:
                                break
                            output.write(block)
                    partial.replace(destination)
                    record["download_status"] = "downloaded"
                except Exception as exc:  # keep going so one dead link does not stop a whole list
                    try:
                        partial.unlink(missing_ok=True)
                    except OSError:
                        pass
                    record["download_status"] = f"error: {exc}"
            manifest.append(record)
            if progress:
                progress(index, total, record, record["download_status"])
        return manifest


def write_manifest(records: list[dict[str, Any]], output_dir: str | Path) -> tuple[Path, Path]:
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    json_path = output_dir / "download_manifest.json"
    csv_path = output_dir / "download_manifest.csv"
    with open(json_path, "w", encoding="utf-8") as handle:
        json.dump(records, handle, ensure_ascii=False, indent=2)
    columns = [
        "annId", "annSongId", "amqSongId", "animeENName", "animeJPName", "animeVintage", "animeType",
        "songType", "songCategory", "songName", "songArtist", "songComposer", "songArranger",
        "songDifficulty", "songLength", "HQ", "MQ", "audio", "download_status", "download_path", "download_source",
    ]
    with open(csv_path, "w", encoding="utf-8-sig", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=columns, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(records)
    return json_path, csv_path


PROFILE_ROOT = Path(os.environ.get("LOCALAPPDATA") or (Path.home() / "Documents")) / "AniSongListDownloader" / "profiles"
APP_DATA_ROOT = PROFILE_ROOT.parent
SETTINGS_PATH = APP_DATA_ROOT / "settings.json"

DEFAULT_APP_SETTINGS: dict[str, Any] = {
    "settings_version": 2,
    "patch_notes_seen_versions": [],
    "title_language": "English",
    "last_profile": "",
    "volume": 50,
    "menu_autoplay": True,
    "song_path": "",
    "learn_new_ratio": 50,
    "learn_existing_ratio": 50,
    "review_hard_ratio": 80,
    "review_easy_ratio": 20,
    "review_boundary": 50,
    "flagged_ratio": 100,
    "other_ratio": 0,
    "session_count": 20,
    "session_guess_time": 20,
    "session_autoskip_seconds": 1,
    "session_year_min": 1924,
    "session_year_max": dt.datetime.now().year,
    "session_custom_percent": 50,
    "session_difficulty_min": 0,
    "session_difficulty_max": 100,
    "session_sample_point": "Random",
    "session_opening": True,
    "session_ending": True,
    "session_insert": True,
    "session_standard": True,
    "session_character": True,
    "session_chanting": True,
    "session_instrumental": True,
    "session_other": True,
    "session_duplicate": False,
    "session_rebroadcast": True,
    "session_dub": False,
    "session_autoskip": True,
    "session_completely_random": False,
}


def load_app_settings() -> dict[str, Any]:
    settings = dict(DEFAULT_APP_SETTINGS)
    saved: dict[str, Any] = {}
    try:
        with open(SETTINGS_PATH, "r", encoding="utf-8") as handle:
            loaded = json.load(handle)
            saved = loaded if isinstance(loaded, dict) else {}
        if isinstance(saved, dict):
            settings.update({key: saved[key] for key in DEFAULT_APP_SETTINGS if key in saved})
    except (OSError, ValueError, TypeError):
        pass
    # Older builds used 100% as the implicit volume. Move an untouched legacy
    # settings file to the new 50% default while preserving later user edits.
    if "settings_version" not in saved and saved.get("volume") == 100:
        settings["volume"] = 50
    settings["settings_version"] = 2
    if settings.get("title_language") not in {"English", "Romaji"}:
        settings["title_language"] = "English"
    settings["last_profile"] = _clean(settings.get("last_profile"))
    try:
        settings["volume"] = max(0, min(100, int(settings["volume"])))
    except (TypeError, ValueError):
        settings["volume"] = DEFAULT_APP_SETTINGS["volume"]
    for key in ("learn_new_ratio", "learn_existing_ratio", "review_hard_ratio", "review_easy_ratio", "flagged_ratio", "other_ratio"):
        try:
            settings[key] = max(0, min(100, int(settings[key])))
        except (TypeError, ValueError):
            settings[key] = DEFAULT_APP_SETTINGS[key]
    try:
        settings["review_boundary"] = max(0, min(100, float(settings["review_boundary"])))
    except (TypeError, ValueError):
        settings["review_boundary"] = DEFAULT_APP_SETTINGS["review_boundary"]
    for key in ("session_count", "session_guess_time", "session_autoskip_seconds"):
        try:
            settings[key] = max(0 if key == "session_autoskip_seconds" else 1, int(settings[key]))
        except (TypeError, ValueError):
            settings[key] = DEFAULT_APP_SETTINGS[key]
    current_year = dt.datetime.now().year
    for key, minimum, maximum in (("session_year_min", 1924, current_year), ("session_year_max", 1924, current_year), ("session_custom_percent", 0, 100), ("session_difficulty_min", 0, 100), ("session_difficulty_max", 0, 100)):
        try:
            settings[key] = max(minimum, min(maximum, int(settings[key])))
        except (TypeError, ValueError):
            settings[key] = DEFAULT_APP_SETTINGS[key]
    if settings["session_year_min"] > settings["session_year_max"]:
        settings["session_year_min"], settings["session_year_max"] = settings["session_year_max"], settings["session_year_min"]
    if settings["session_difficulty_min"] > settings["session_difficulty_max"]:
        settings["session_difficulty_min"], settings["session_difficulty_max"] = settings["session_difficulty_max"], settings["session_difficulty_min"]
    if settings.get("session_sample_point") not in {"Start", "End", "Random", "Custom (%)"}:
        settings["session_sample_point"] = DEFAULT_APP_SETTINGS["session_sample_point"]
    for key in ("menu_autoplay", "session_opening", "session_ending", "session_insert", "session_standard", "session_character", "session_chanting", "session_instrumental", "session_other", "session_duplicate", "session_rebroadcast", "session_dub", "session_autoskip", "session_completely_random"):
        settings[key] = bool(settings.get(key, DEFAULT_APP_SETTINGS[key]))
    seen_patch_versions = settings.get("patch_notes_seen_versions")
    settings["patch_notes_seen_versions"] = [
        _clean(version) for version in seen_patch_versions
        if _clean(version)
    ] if isinstance(seen_patch_versions, list) else []
    return settings


def save_app_settings(settings: dict[str, Any]) -> None:
    APP_DATA_ROOT.mkdir(parents=True, exist_ok=True)
    with open(SETTINGS_PATH, "w", encoding="utf-8") as handle:
        json.dump(settings, handle, ensure_ascii=False, indent=2)


def _profile_slug(name: str) -> str:
    slug = re.sub(r"[^A-Za-z0-9._ -]+", "", name).strip().replace(" ", "_")
    return slug[:80] or "Default"


def _collection_to_dict(collection: Optional[AnimeCollection]) -> Optional[dict[str, Any]]:
    if collection is None:
        return None
    return {
        "source": collection.source,
        "path": collection.path,
        "songs": collection.songs,
        "buckets": [
            {
                "name": bucket.name,
                "kind": bucket.kind,
                "song_count": bucket.song_count,
                "entries": [asdict(entry) for entry in bucket.entries],
            }
            for bucket in collection.buckets.values()
        ],
    }


def _collection_from_dict(data: Optional[dict[str, Any]]) -> Optional[AnimeCollection]:
    if not data:
        return None
    buckets: OrderedDict[str, ListBucket] = OrderedDict()
    for raw_bucket in data.get("buckets") or []:
        bucket = ListBucket(
            name=_clean(raw_bucket.get("name")),
            kind=_clean(raw_bucket.get("kind")) or "status",
            song_count=raw_bucket.get("song_count"),
        )
        for raw_entry in raw_bucket.get("entries") or []:
            bucket.add(AnimeEntry(**raw_entry))
        buckets[bucket.name] = bucket
    return AnimeCollection(
        source=_clean(data.get("source")),
        buckets=buckets,
        path=_clean(data.get("path")),
        songs=data.get("songs") or [],
    )


def _profile_names() -> list[str]:
    if not PROFILE_ROOT.exists():
        return []
    names: list[str] = []
    for folder in PROFILE_ROOT.iterdir():
        profile_path = folder / "profile.json"
        if folder.is_dir() and profile_path.exists():
            try:
                with open(profile_path, "r", encoding="utf-8") as handle:
                    names.append(_clean(json.load(handle).get("profile_name")) or folder.name.replace("_", " "))
            except (OSError, ValueError):
                names.append(folder.name.replace("_", " "))
    return sorted(names, key=str.casefold)


def _fmt_count(value: Optional[int]) -> str:
    return "—" if value is None else str(value)


def count_songs_by_bucket(collection: AnimeCollection, songs: Iterable[dict[str, Any]]) -> dict[str, int]:
    """Count distinct returned songs per exported list.

    AniList lookups use each entry's MAL cross-link because AnisongDB's batch
    endpoint is MAL-ID based. Responses can contain either the AniList link,
    the MAL link, or both, so AniList buckets must accept both identifiers.
    """
    by_identifier: dict[int, set[int]] = {}
    for song in songs:
        linked = song.get("linked_ids") or {}
        identifiers = (linked.get("anilist"), linked.get("myanimelist")) if collection.source == "AniList" else (linked.get("myanimelist"),)
        song_id = song.get("annSongId") or song.get("amqSongId")
        if not song_id:
            continue
        for identifier in identifiers:
            if identifier:
                by_identifier.setdefault(int(identifier), set()).add(int(song_id))
    totals: dict[str, int] = {}
    for name, bucket in collection.buckets.items():
        song_ids: set[int] = set()
        for entry in bucket.entries:
            identifiers = (entry.anilist_id, entry.mal_id) if collection.source == "AniList" else (entry.mal_id,)
            for identifier in identifiers:
                if identifier:
                    song_ids.update(by_identifier.get(int(identifier), set()))
        totals[name] = len(song_ids)
    return totals


def display_bucket_type(collection: AnimeCollection, bucket: ListBucket) -> str:
    if bucket.kind == "custom":
        return "Custom List"
    if bucket.kind in DIRECT_SONG_COLLECTION_SOURCES:
        return bucket.kind
    if collection.source in ("AniList", "MAL"):
        return collection.source
    return bucket.kind.title()


def _collection_has_embedded_songs(collection: Optional[AnimeCollection]) -> bool:
    """Whether the collection already contains song records and needs no API lookup."""
    return bool(collection and collection.songs and (collection.source in DIRECT_SONG_COLLECTION_SOURCES or collection.source == "Mixed"))


def _search_clean(value: Any, keep_special: bool = False) -> str:
    text = unicodedata.normalize("NFKD", _clean(value)).encode("ascii", "ignore").decode("ascii").lower()
    if keep_special:
        text = re.sub(r"\s+", " ", text).strip()
    else:
        text = re.sub(r"[^\w\s]", " ", text)
        text = re.sub(r"\s+", " ", text).strip()
    return text


class LibraryIndex:
    """AMQ title index with the matching stages used by the supplied userscript."""

    def __init__(self, records: Optional[list[dict[str, Any]]] = None):
        self.records: list[dict[str, Any]] = []
        self.replace(records or [])

    def replace(self, records: list[dict[str, Any]]) -> None:
        self.records = []
        self._search_cache: dict[tuple[str, int], list[str]] = {}
        seen: set[str] = set()
        for record in records:
            title = _clean(record.get("title"))
            aliases = [_clean(alias) for alias in record.get("aliases", []) if _clean(alias)]
            aliases.insert(0, title)
            if not title:
                continue
            key = _search_clean(title)
            if key in seen:
                continue
            seen.add(key)
            aliases = list(dict.fromkeys(aliases))
            self.records.append({
                "title": title,
                "aliases": aliases,
                "_clean_aliases": [_search_clean(alias) for alias in aliases],
                "_literal_aliases": [_search_clean(alias, keep_special=True) for alias in aliases],
            })

    @classmethod
    def from_library_payload(cls, payload: dict[str, Any]) -> "LibraryIndex":
        records: list[dict[str, Any]] = []
        for raw in (payload.get("animeMap") or {}).values():
            main_names = raw.get("mainNames") or {}
            aliases = [main_names.get("EN"), main_names.get("JA")]
            aliases.extend(item.get("name") for item in raw.get("names") or [] if isinstance(item, dict))
            title = _first_nonempty(main_names.get("EN"), main_names.get("JA"), *(aliases or [f"Anime {raw.get('annId', '')}"]))
            records.append({"title": title, "aliases": aliases})
        return cls(records)

    @classmethod
    def from_song_records(cls, records: list[dict[str, Any]]) -> "LibraryIndex":
        grouped: dict[str, dict[str, Any]] = {}
        for song in records:
            title = _first_nonempty(song.get("animeENName"), song.get("animeJPName"), "Unknown anime")
            key = _search_clean(title)
            grouped.setdefault(key, {"title": title, "aliases": []})["aliases"].extend(
                [song.get("animeENName"), song.get("animeJPName"), song.get("animeAltName")]
            )
        return cls(list(grouped.values()))

    def search(self, query: str, limit: int = 12) -> list[str]:
        query = _clean(query)
        if not query:
            return []
        clean_query = _search_clean(query)
        cache_key = (clean_query, int(limit))
        cached = self._search_cache.get(cache_key)
        if cached is not None:
            return list(cached)
        query_words = clean_query.split()
        literal_query = _search_clean(query, keep_special=True)
        matched: dict[int, list[tuple[int, float, int, str]]] = {}

        # The old implementation ran SequenceMatcher against every known
        # title for every keystroke.  The library can contain tens of
        # thousands of titles, so a one-letter query could briefly block the
        # Tk event loop.  Exact/prefix/contains/word-order matching is cheap
        # and is enough for almost every keystroke; fuzzy matching is deferred
        # until the fast pass did not produce enough results.
        for record_index, record in enumerate(self.records):
            aliases = record["aliases"]
            clean_aliases = record.get("_clean_aliases") or [_search_clean(alias) for alias in aliases]
            literal_aliases = record.get("_literal_aliases") or [_search_clean(alias, keep_special=True) for alias in aliases]
            matches: list[tuple[int, float, int, str]] = []
            for display, alias, literal_alias in zip(aliases, clean_aliases, literal_aliases):
                if not alias:
                    continue
                priority: Optional[int] = None
                score = 0.0
                # Preserve punctuation for the strongest matches.  This lets
                # an exact "Aikatsu!" query beat the broader normalized
                # prefix match for "Aikatsu Friends!".
                if literal_query and literal_alias == literal_query:
                    priority, score = -1, 1.2
                elif literal_query and literal_alias.startswith(literal_query):
                    priority, score = 0, 1.05
                elif alias.startswith(clean_query):
                    priority, score = 0, 1.0
                elif clean_query in alias:
                    priority = min(priority if priority is not None else 9, 1)
                    score = max(score, 0.9)
                words = alias.split()
                if query_words and all(any(word.startswith(part) or part in word for word in words) for part in query_words):
                    priority = min(priority if priority is not None else 9, 2)
                    score = max(score, 0.8)
                if priority is not None:
                    matches.append((priority, -score, len(alias), display))
            if matches:
                matched[record_index] = matches

        def scored_records() -> list[tuple[int, float, int, str, list[str]]]:
            scored: list[tuple[int, float, int, str, list[str]]] = []
            for record_index, matches in matched.items():
                record = self.records[record_index]
                matches.sort(key=lambda item: (item[0], item[1], item[2], item[3].casefold()))
                best_priority, best_score, best_length, _best_display = matches[0]
                # Keep every known name for a matched anime in the dropdown,
                # while putting the variant that matched the query first.
                ordered_names = list(dict.fromkeys(item[3] for item in matches))
                ordered_names.extend(alias for alias in record["aliases"] if alias not in ordered_names)
                scored.append((best_priority, best_score, best_length, record["title"], ordered_names))
            # For shared starts-with matches, prefer the shortest matching
            # title so "Aikatsu!" appears before "Aikatsu Friends!".
            scored.sort(key=lambda item: (item[0], item[1], item[2], item[3].casefold()))
            return scored

        def collect(scored: list[tuple[int, float, int, str, list[str]]]) -> list[str]:
            results: list[str] = []
            seen: set[str] = set()
            for _priority, _score, _length, _title, names in scored:
                for name in names:
                    clean_name = _search_clean(name)
                    if not clean_name or clean_name in seen:
                        continue
                    seen.add(clean_name)
                    results.append(name)
                    if len(results) >= limit:
                        return results
            return results

        results = collect(scored_records())
        if not matched and len(clean_query) >= 3:
            # Fuzzy matching is only a fallback.  Restrict it to aliases that
            # contain the query's first two characters in order, which retains
            # typo support without comparing every title on every keypress.
            prefix_hint = clean_query[:2]
            for record_index, record in enumerate(self.records):
                if record_index in matched:
                    continue
                fuzzy_matches: list[tuple[int, float, int, str]] = []
                for display, alias in zip(record["aliases"], record.get("_clean_aliases", [])):
                    if not alias.startswith(prefix_hint) and prefix_hint not in alias:
                        continue
                    score = difflib.SequenceMatcher(None, clean_query, alias).ratio()
                    if score >= 0.45:
                        fuzzy_matches.append((3, -score, len(alias), display))
                if fuzzy_matches:
                    matched[record_index] = fuzzy_matches
            results = collect(scored_records())

        self._search_cache[cache_key] = list(results)
        if len(self._search_cache) > 128:
            self._search_cache.pop(next(iter(self._search_cache)))
        return results


class LibraryManager:
    CACHE_PATH = PROFILE_ROOT.parent / "libraryMasterList.json"
    REFRESH_SECONDS = 24 * 60 * 60

    def __init__(self):
        self.index = LibraryIndex()
        self.fetched_at = 0.0
        self.refreshing = False
        self.load_cache()

    def load_cache(self) -> None:
        try:
            with open(self.CACHE_PATH, "r", encoding="utf-8") as handle:
                payload = json.load(handle)
            if payload.get("records"):
                self.index = LibraryIndex(payload["records"])
            else:
                # Read caches written by older builds, which stored the full
                # libraryMasterList response instead of the small title index.
                self.index = LibraryIndex.from_library_payload(payload.get("payload") or payload)
            self.fetched_at = float(payload.get("fetched_at", 0))
        except (OSError, ValueError, TypeError):
            self.index = LibraryIndex()
            self.fetched_at = 0.0

    def refresh_async(self, callback: Optional[Callable[[Optional[Exception]], None]] = None, force: bool = False) -> None:
        if self.refreshing or (not force and dt.datetime.now().timestamp() - self.fetched_at < self.REFRESH_SECONDS):
            if callback:
                callback(None)
            return
        self.refreshing = True
        def work() -> None:
            error: Optional[Exception] = None
            try:
                request = urllib.request.Request(LIBRARY_URL, headers={"Accept": "application/json", "User-Agent": "AMQTrainer/1.0"})
                with urllib.request.urlopen(request, timeout=45) as response:
                    payload = json.loads(response.read().decode("utf-8"))
                index = LibraryIndex.from_library_payload(payload)
                self.CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
                with open(self.CACHE_PATH, "w", encoding="utf-8") as handle:
                    json.dump(
                        {
                            "fetched_at": dt.datetime.now().timestamp(),
                            "records": [{"title": record["title"], "aliases": record["aliases"]} for record in index.records],
                        },
                        handle,
                        ensure_ascii=False,
                    )
                self.index = index
                self.fetched_at = dt.datetime.now().timestamp()
            except Exception as exc:
                error = exc
            finally:
                self.refreshing = False
                if callback:
                    callback(error)
        threading.Thread(target=work, daemon=True).start()


class MCIPlayer:
    """Small Windows-native MP3 player using the built-in MCI multimedia API."""

    def __init__(self, alias: str = "anisong_training_player"):
        self.alias = alias
        self.available = os.name == "nt"
        self._send = ctypes.windll.winmm.mciSendStringW if self.available else None

    def _command(self, command: str) -> tuple[int, str]:
        if not self._send:
            return 1, "Windows audio playback is unavailable on this platform."
        buffer = ctypes.create_unicode_buffer(256)
        result = self._send(command, buffer, len(buffer), None)
        return result, buffer.value

    def stop(self) -> None:
        if self._send:
            self._command(f"stop {self.alias}")
            self._command(f"close {self.alias}")

    def set_volume(self, volume: int) -> None:
        volume_value = max(0, min(100, int(volume))) * 10
        self._command(f"setaudio {self.alias} volume to {volume_value}")

    def play(self, path: str, sample_point: str, custom_percent: float, guess_time: int, volume: int = 50) -> None:
        self.stop()
        result, detail = self._command(f'open "{path}" type mpegvideo alias {self.alias}')
        if result:
            raise RuntimeError(detail or "Windows could not open this audio file.")
        self.set_volume(volume)
        _result, length_text = self._command(f"status {self.alias} length")
        try:
            length = max(0, int(length_text))
        except ValueError:
            length = 0
        window = max(1000, guess_time * 1000)
        if sample_point == "End":
            offset = max(0, length - window)
        elif sample_point == "Custom (%)":
            offset = int(max(0.0, min(100.0, custom_percent)) / 100.0 * max(0, length - window))
        elif sample_point == "Random":
            offset = random.randint(0, max(0, length - window)) if length > window else 0
        else:
            offset = 0
        result, detail = self._command(f"play {self.alias} from {offset}")
        if result:
            self.stop()
            raise RuntimeError(detail or "Windows could not play this audio file.")

    def play_full(self, path: str, volume: int = 50) -> None:
        """Play a downloaded song from the beginning without the quiz clip window."""
        self.stop()
        result, detail = self._command(f'open "{path}" type mpegvideo alias {self.alias}')
        if result:
            raise RuntimeError(detail or "Windows could not open this audio file.")
        self.set_volume(volume)
        result, detail = self._command(f"play {self.alias}")
        if result:
            self.stop()
            raise RuntimeError(detail or "Windows could not play this audio file.")


def _record_key(record: dict[str, Any], index: int = 0) -> str:
    return _clean(record.get("annSongId") or record.get("amqSongId") or record.get("_amq_song_number") or record.get("download_path")) or f"song-{index}"


def _record_flag(record: dict[str, Any], name: str) -> bool:
    value = record.get(name)
    return value is True or str(value).strip().lower() in {"1", "true", "yes"}


def _record_guess_rate(stats: dict[str, Any]) -> float:
    encounters = int(stats.get("encounters", 0) or 0)
    return (100.0 * int(stats.get("correct", 0) or 0) / encounters) if encounters else 0.0


class App:
    def __init__(self, root: Any):
        import tkinter as tk
        import tkinter.font as tkfont
        from tkinter import filedialog, messagebox, simpledialog, ttk

        self.tk, self.tkfont, self.filedialog, self.messagebox, self.simpledialog, self.ttk = tk, tkfont, filedialog, messagebox, simpledialog, ttk
        self._native_messageboxes = {
            name: getattr(messagebox, name)
            for name in ("askyesno", "showinfo", "showwarning", "showerror")
        }
        self.messagebox.askyesno = self._askyesno
        self.messagebox.showinfo = self._showinfo
        self.messagebox.showwarning = self._showwarning
        self.messagebox.showerror = self._showerror
        self.root = root
        self.root.title("AMQ Trainer")
        icon_candidates = [Path(__file__).resolve().parent / "geso.ico"]
        bundle_root = getattr(sys, "_MEIPASS", None)
        if bundle_root:
            icon_candidates.insert(0, Path(bundle_root) / "geso.ico")
        for icon_path in icon_candidates:
            if icon_path.exists():
                try:
                    self.root.iconbitmap(default=str(icon_path))
                except self.tk.TclError:
                    pass
                break
        # Keep one predictable design surface so the Kanon layout is easy to
        # tune and every popup can fit alongside the main window.
        self.root.geometry("1280x720")
        self.root.minsize(1280, 720)
        self.root.maxsize(1280, 720)
        self.root.resizable(False, False)
        self.style = ttk.Style(self.root)
        self.app_settings = load_app_settings()
        self.asset_root = _ui_asset_root()
        # Let Tk own cursor selection for the whole widget tree. Repeatedly
        # calling Win32 SetCursor races Tk's normal WM_SETCURSOR handling and
        # is the source of the visible custom/default cursor flicker.
        self._app_cursor = ""
        cursor_path = self.asset_root / "msfearful.cur"
        if cursor_path.exists():
            try:
                self._app_cursor = f"@{cursor_path.as_posix()}"
                self.root.configure(cursor=self._app_cursor)
            except self.tk.TclError:
                self._app_cursor = ""
        self._ui_images: dict[str, Any] = {}
        self._ui_font_family = "Poppins"
        self._register_ui_fonts()
        self.collection: Optional[AnimeCollection] = None
        self.import_paths: list[str] = []
        self.enabled_lists: set[str] = set()
        self.excluded_song_keys: set[str] = set()
        self.client = AnisongDBClient()
        self.download_records: list[dict[str, Any]] = []
        self._playable_records_cache: Optional[list[dict[str, Any]]] = None
        self._playable_records_cache_signature: Optional[tuple[Any, ...]] = None
        self._profile_membership_cache: Optional[tuple[tuple[Any, ...], set[str], set[str]]] = None
        self._song_query_cache: dict[tuple[Any, ...], list[dict[str, Any]]] = {}
        self.play_stats: dict[str, dict[str, Any]] = {}
        self.current_manifest_path = ""
        self.count_refresh_job: Optional[str] = None
        self._profile_save_job: Optional[str] = None
        self.list_rows: dict[str, str] = {}
        self.busy = False
        self.startup_loading = True
        self._no_profiles_detected = False
        self._startup_overlay: Any = None
        self._startup_progress_canvas: Any = None
        self._startup_progress_fill: Any = None
        self._startup_message_label: Any = None
        self.new_profile_mode = False
        self._profile_before_new_name = ""
        self.menu_player = MCIPlayer("anisong_menu_player")
        self._menu_player_record: Optional[dict[str, Any]] = None
        self._menu_player_paused = False
        self._menu_player_active = False
        self._menu_player_suspended = False
        self._menu_player_loop_enabled = False
        self._menu_player_poll_job: Optional[str] = None
        self._menu_player_history: list[dict[str, Any]] = []
        self._menu_player_history_index = -1
        self._update_check_in_progress = False
        self._update_install_in_progress = False

        self.profile_var = tk.StringVar(value=_clean(self.app_settings.get("last_profile")) or "Default")
        self.profile_name_var = tk.StringVar(value="Default")
        self.path_var = tk.StringVar()
        self.output_var = tk.StringVar(value=str(Path.cwd() / "downloads"))
        self.media_var = tk.StringVar(value="audio")
        self.status_var = tk.StringVar(value="Choose a profile to begin.")
        self.year_min_var = tk.StringVar(value="1924")
        self.year_max_var = tk.StringVar(value=str(dt.datetime.now().year))
        self.season_var = tk.StringVar(value="All")
        self.opening_var = tk.BooleanVar(value=True)
        self.ending_var = tk.BooleanVar(value=True)
        self.insert_var = tk.BooleanVar(value=True)
        self.standard_var = tk.BooleanVar(value=True)
        self.character_var = tk.BooleanVar(value=True)
        self.chanting_var = tk.BooleanVar(value=True)
        self.instrumental_var = tk.BooleanVar(value=True)
        self.other_var = tk.BooleanVar(value=True)
        self.library = LibraryManager()
        self.library.refresh_async()

        self._apply_theme()
        self.root.report_callback_exception = self._report_callback_exception
        self._build()
        self._schedule_menu_player_poll()
        # Let Tk paint the first screen before reading/parsing a potentially
        # large saved profile.  The overlay also prevents a premature click on
        # Settings while startup restoration is still in progress.
        self.root.after(60, self._start_profile_initialization)
        self.root.after(2500, lambda: self.check_for_updates(silent=True))

    def _report_callback_exception(self, exc: type[BaseException], value: BaseException, tb: Any) -> None:
        """Keep callback failures from looking like a silent/frozen UI."""
        details = "".join(traceback.format_exception(exc, value, tb))
        try:
            APP_DATA_ROOT.mkdir(parents=True, exist_ok=True)
            with open(APP_DATA_ROOT / "ui_error.log", "a", encoding="utf-8") as handle:
                handle.write(f"\n[{dt.datetime.now().isoformat(timespec='seconds')}]\n{details}")
        except OSError:
            pass
        try:
            self.status_var.set("A UI error was logged. You can continue using the application.")
        except Exception:
            pass

    def _show_startup_loading(self, message: str = "Loading profile…", progress: int = 0) -> None:
        """Show a Kanon-styled startup shield above the navigation buttons."""
        if not hasattr(self, "content") or not self.content.winfo_exists():
            return
        if self._startup_overlay is None or not self._startup_overlay.winfo_exists():
            overlay = self.tk.Frame(self.content, bg=UI_BACKGROUND, cursor=self._app_cursor)
            overlay.place(relx=0, rely=0, relwidth=1, relheight=1)
            overlay.bind("<Button-1>", lambda _event: "break")
            overlay.bind("<ButtonRelease-1>", lambda _event: "break")
            overlay.bind("<Key>", lambda _event: "break")
            title = self.tk.Label(overlay, text="Preparing AniSong Trainer", bg=UI_BACKGROUND, fg=UI_TEXT, font=(self._ui_font_family, 25, "bold"))
            title.place(relx=0.5, rely=0.43, anchor="center")
            message_label = self.tk.Label(overlay, text=message, bg=UI_BACKGROUND, fg=UI_MUTED, font=(self._ui_font_family, 13))
            message_label.place(relx=0.5, rely=0.49, anchor="center")
            progress_canvas = self.tk.Canvas(overlay, width=640, height=30, bg=UI_PANEL_DARK, highlightthickness=1, highlightbackground=UI_MUTED)
            progress_canvas.place(relx=0.5, rely=0.56, anchor="center")
            fill = progress_canvas.create_rectangle(2, 2, 2, 28, fill=UI_PINK, outline="")
            self._startup_overlay = overlay
            self._startup_message_label = message_label
            self._startup_progress_canvas = progress_canvas
            self._startup_progress_fill = fill
        self._set_startup_progress(message, progress)

    def _set_startup_progress(self, message: str, progress: int) -> None:
        if self._startup_overlay is None or not self._startup_overlay.winfo_exists():
            return
        progress = max(0, min(100, int(progress)))
        if self._startup_message_label is not None:
            self._startup_message_label.configure(text=message)
        if self._startup_progress_canvas is not None and self._startup_progress_fill is not None:
            width = 640 * progress / 100
            self._startup_progress_canvas.coords(self._startup_progress_fill, 2, 2, max(2, width - 2), 28)
        self.root.update_idletasks()

    def _finish_startup_loading(self) -> None:
        if self._startup_overlay is None or not self._startup_overlay.winfo_exists():
            self.startup_loading = False
            return
        self._set_startup_progress("Ready", 100)
        def close_overlay() -> None:
            self.startup_loading = False
            if self._startup_overlay is not None and self._startup_overlay.winfo_exists():
                self._startup_overlay.destroy()
            self._startup_overlay = None
            self._startup_progress_canvas = None
            self._startup_progress_fill = None
            self._startup_message_label = None
            if self._no_profiles_detected:
                self._no_profiles_detected = False
                self.root.after(80, self._show_no_profiles_prompt)
        self.root.after(180, close_overlay)

    def _start_profile_initialization(self) -> None:
        self._show_startup_loading("Checking local profiles…", 8)
        self.root.after(25, self._initialize_profiles)

    def _show_no_profiles_prompt(self) -> None:
        """Ask whether a first profile should be created without forcing one."""
        dialog = self.tk.Toplevel(self.root)
        dialog.title("Profiles")
        dialog.configure(bg=UI_PINK)
        dialog.overrideredirect(True)
        dialog.transient(self.root)
        dialog.grab_set()
        self._center_window(dialog, 470, 270)
        surface = self.tk.Frame(dialog, bg=UI_BACKGROUND)
        surface.pack(fill="both", expand=True, padx=4, pady=4)
        self.tk.Label(
            surface,
            text="There are currently no registered profiles.\nCreate a new profile?",
            bg=UI_BACKGROUND,
            fg=UI_TEXT,
            font=(self._ui_font_family, 15, "bold"),
            justify="center",
        ).pack(fill="x", pady=(58, 30))
        buttons = self.tk.Frame(surface, bg=UI_BACKGROUND)
        buttons.pack()
        def choose_new() -> None:
            dialog.destroy()
            self.new_profile()
        self._make_kanon_button(buttons, "Yes", choose_new, width=95, height=36, font_size=10, active_color=UI_PINK_DARK, hover_color=UI_PINK_DARK).pack(side="left", padx=8)
        self._make_kanon_button(buttons, "Later", dialog.destroy, width=95, height=36, font_size=10).pack(side="left", padx=8)
        dialog.protocol("WM_DELETE_WINDOW", dialog.destroy)
        dialog.bind("<Escape>", lambda _event: dialog.destroy())
        self._activate_dialog(dialog)

    def _register_ui_fonts(self) -> None:
        """Register the bundled Poppins font when running on Windows."""
        font_path = self.asset_root / "Fonts" / "Poppins" / "Poppins-Regular.ttf"
        if not font_path.exists():
            self._ui_font_family = "TkDefaultFont"
            return
        try:
            if sys.platform == "win32":
                ctypes.windll.gdi32.AddFontResourceExW(str(font_path), 0x10, 0)
        except (AttributeError, OSError):
            self._ui_font_family = "TkDefaultFont"

    def _ui_image(self, relative_path: str) -> Any:
        if relative_path not in self._ui_images:
            path = self.asset_root / relative_path
            self._ui_images[relative_path] = self.tk.PhotoImage(file=str(path))
        return self._ui_images[relative_path]

    def _ui_background(self) -> Any:
        """Return the supplied 16:9 background fitted exactly to 1280x720."""
        cache_key = "background-1280x720"
        if cache_key not in self._ui_images:
            # 1920x1080 × 2/3 gives an exact 1280x720 image using Tk's
            # built-in image operations, so the standalone build needs no
            # additional imaging dependency.
            self._ui_images[cache_key] = self._ui_image("Backgrounds/Background 1.png").zoom(2, 2).subsample(3, 3)
        return self._ui_images[cache_key]

    def _apply_theme(self) -> None:
        """Apply the fixed Kanon palette to all native widgets."""
        try:
            self.style.theme_use("clam")
        except self.tk.TclError:
            self.style.theme_use("clam")
        self.root.configure(bg=UI_BACKGROUND)
        self.style.configure(".", background=UI_BACKGROUND, foreground=UI_TEXT, font=(self._ui_font_family, 10))
        self.style.configure("TFrame", background=UI_BACKGROUND)
        self.style.configure("TLabel", background=UI_BACKGROUND, foreground=UI_TEXT)
        self.style.configure("TLabelframe", background=UI_PANEL, foreground=UI_TEXT)
        self.style.configure("TLabelframe.Label", background=UI_PANEL, foreground=UI_TEXT)
        self.style.configure("TButton", background=UI_PANEL, foreground=UI_TEXT, borderwidth=1, padding=(12, 7))
        self.style.configure("Accent.TButton", background=UI_PINK, foreground=UI_TEXT, borderwidth=1, padding=(12, 7))
        self.style.map("TButton", background=[("active", UI_PINK), ("pressed", UI_PINK)], foreground=[("active", "#ffffff")])
        self.style.map("Accent.TButton", background=[("active", UI_PINK_LIGHT), ("pressed", UI_PINK)], foreground=[("active", "#ffffff")])
        self.style.configure("TEntry", fieldbackground=UI_PANEL_DARK, foreground=UI_TEXT, insertcolor=UI_TEXT)
        self.style.configure("TCombobox", fieldbackground=UI_PANEL_DARK, foreground=UI_TEXT, arrowcolor=UI_TEXT)
        self.style.map(
            "TCombobox",
            fieldbackground=[("readonly", UI_PANEL_DARK), ("disabled", UI_PANEL_DARK)],
            foreground=[("readonly", UI_TEXT), ("disabled", UI_MUTED)],
            selectbackground=[("readonly", UI_PINK)],
            selectforeground=[("readonly", UI_TEXT)],
        )
        self.root.option_add("*TCombobox*Listbox.background", UI_PANEL_DARK)
        self.root.option_add("*TCombobox*Listbox.foreground", UI_TEXT)
        self.root.option_add("*TCombobox*Listbox.selectBackground", UI_PINK)
        self.root.option_add("*TCombobox*Listbox.selectForeground", UI_TEXT)
        self.style.configure("TCheckbutton", background=UI_BACKGROUND, foreground=UI_TEXT)
        self.style.configure("Treeview", background=UI_PANEL_DARK, fieldbackground=UI_PANEL_DARK, foreground=UI_TEXT, rowheight=26)
        self.style.map("Treeview", background=[("selected", UI_PINK)], foreground=[("selected", "#ffffff")])
        self.style.configure("Download.Treeview", background=UI_PANEL_DARK, fieldbackground=UI_PANEL_DARK, foreground=UI_TEXT, rowheight=27)
        self.style.map("Download.Treeview", background=[("selected", UI_PINK)], foreground=[("selected", "#ffffff")])
        self.style.configure("Download.Treeview.Heading", background=UI_PANEL, foreground=UI_TEXT, relief="flat")
        self.style.configure(
            "Pink.Horizontal.TProgressbar",
            troughcolor=UI_PANEL_DARK,
            background=UI_PINK,
            lightcolor=UI_PINK,
            darkcolor=UI_PINK,
            bordercolor=UI_PANEL_DARK,
        )
        self.style.configure("Vertical.TScrollbar", background=UI_PANEL, troughcolor=UI_BACKGROUND, arrowcolor=UI_TEXT)
        # Tk focus can be stolen by a canvas or a parent frame after a screen
        # transition.  Reassert focus on every editable entry click so the
        # profile name, search boxes, session fields, and answer box all behave
        # consistently.
        self.root.bind_class("Entry", "<ButtonPress-1>", self._force_text_focus, add="+")
        self.root.bind_class("TEntry", "<ButtonPress-1>", self._force_text_focus, add="+")
        self.root.bind_class("Entry", "<ButtonRelease-1>", self._force_text_focus, add="+")
        self.root.bind_class("TEntry", "<ButtonRelease-1>", self._force_text_focus, add="+")

    def _force_text_focus(self, event: Any) -> None:
        try:
            if str(event.widget.cget("state")) not in {"disabled", "readonly"}:
                event.widget.focus_force()
        except (AttributeError, self.tk.TclError):
            pass

    def _messagebox_target(self, parent: Any = None) -> Any:
        """Prefer the currently grabbed popup as the native dialog owner."""
        target = parent or self.root
        if parent is None or parent is self.root:
            try:
                grabbed = self.root.grab_current()
                if grabbed is not None:
                    target = grabbed.winfo_toplevel()
            except (AttributeError, self.tk.TclError):
                pass
        return target

    def _call_messagebox(self, kind: str, title: str, message: str, parent: Any = None, **kwargs: Any) -> Any:
        """Keep all native messageboxes above the active AMQ Trainer window."""
        target = self._messagebox_target(parent)
        windows: list[Any] = []
        for window in (self.root, target):
            if window is not None and all(window is not existing for existing in windows):
                windows.append(window)
        for window in windows:
            window.lift()
        target.focus_force()
        self.root.update_idletasks()
        native = self._native_messageboxes[kind]
        # The native dialog is parented to the active AMQ Trainer window, so it
        # stays above this app without becoming globally topmost.
        return native(title, message, parent=target, **kwargs)

    def _askyesno(self, title: str, message: str, parent: Any = None, **kwargs: Any) -> bool:
        return bool(self._call_messagebox("askyesno", title, message, parent=parent, **kwargs))

    def _showinfo(self, title: str, message: str, parent: Any = None, **kwargs: Any) -> Any:
        return self._call_messagebox("showinfo", title, message, parent=parent, **kwargs)

    def _showwarning(self, title: str, message: str, parent: Any = None, **kwargs: Any) -> Any:
        return self._call_messagebox("showwarning", title, message, parent=parent, **kwargs)

    def _showerror(self, title: str, message: str, parent: Any = None, **kwargs: Any) -> Any:
        return self._call_messagebox("showerror", title, message, parent=parent, **kwargs)

    def _save_app_settings(self) -> None:
        try:
            save_app_settings(self.app_settings)
        except OSError as exc:
            self.messagebox.showerror("Could not save settings", str(exc), parent=self.root)

    @staticmethod
    def _version_key(value: str) -> tuple[int, ...]:
        numbers = re.findall(r"\d+", _clean(value))
        return tuple(int(number) for number in numbers) or (0,)

    def check_for_updates(self, silent: bool = False) -> None:
        """Check GitHub Releases without blocking Tk's UI thread."""
        repository = os.environ.get("AMQ_TRAINER_UPDATE_REPOSITORY", UPDATE_REPOSITORY).strip().strip("/")
        if not repository or "/" not in repository:
            if not silent:
                self.messagebox.showinfo(
                    "Updates not configured",
                    "Set UPDATE_REPOSITORY to your GitHub owner/repository before building the release EXE.",
                    parent=self.root,
                )
            return
        if not getattr(sys, "frozen", False):
            if not silent:
                self.messagebox.showinfo(
                    "Packaged EXE required",
                    "Automatic replacement is available in the packaged AMQTrainer.exe build, not when running the .py source.",
                    parent=self.root,
                )
            return
        if self._update_check_in_progress or self._update_install_in_progress:
            return
        self._update_check_in_progress = True
        self.status_var.set("Checking for updates…")

        def work() -> None:
            result: Optional[dict[str, str]] = None
            error: Optional[str] = None
            try:
                api_url = f"https://api.github.com/repos/{urllib.parse.quote(repository, safe='/')}/releases/latest"
                request = urllib.request.Request(
                    api_url,
                    headers={"Accept": "application/vnd.github+json", "User-Agent": "AMQTrainer-Updater"},
                )
                with urllib.request.urlopen(request, timeout=15) as response:
                    payload = json.loads(response.read().decode("utf-8"))
                tag = _clean(payload.get("tag_name"))
                asset = next(
                    (
                        item for item in payload.get("assets", [])
                        if isinstance(item, dict) and _clean(item.get("name")).casefold() == UPDATE_ASSET_NAME.casefold()
                    ),
                    None,
                )
                if not tag:
                    raise RuntimeError("The latest GitHub release has no version tag.")
                if not isinstance(asset, dict) or not _clean(asset.get("browser_download_url")):
                    raise RuntimeError(f"The latest release does not contain an {UPDATE_ASSET_NAME} asset.")
                result = {
                    "version": tag,
                    "download_url": _clean(asset.get("browser_download_url")),
                    "release_url": _clean(payload.get("html_url")),
                    "notes": _clean(payload.get("body")),
                }
            except Exception as exc:
                error = str(exc)
            try:
                self.root.after(0, lambda: self._finish_update_check(result, error, silent))
            except self.tk.TclError:
                pass

        threading.Thread(target=work, daemon=True).start()

    def _finish_update_check(self, release: Optional[dict[str, str]], error: Optional[str], silent: bool) -> None:
        self._update_check_in_progress = False
        if error:
            self.status_var.set("Update check failed.")
            if not silent:
                self.messagebox.showerror("Update check failed", error, parent=self.root)
            return
        if not release or self._version_key(release["version"]) <= self._version_key(APP_VERSION):
            self.status_var.set("AMQ Trainer is up to date.")
            if not silent:
                self.messagebox.showinfo("No update available", f"You are running AMQ Trainer {APP_VERSION}.", parent=self.root)
            return
        version = release["version"]
        seen_patch_versions = self.app_settings.setdefault("patch_notes_seen_versions", [])
        show_patch_notes = version not in seen_patch_versions
        if show_patch_notes:
            notes = _clean(release.get("notes"))
            if len(notes) > 3500:
                notes = notes[:3500].rstrip() + "…"
            if not notes:
                notes = "No patch notes were provided for this release."
            update_message = (
                f"AMQ Trainer {version} is available.\n\n"
                f"Patch Notes:\n{notes}\n\n"
                "Download and install it now?"
            )
            # Mark this release as seen before asking, so declining the update
            # does not cause the same patch notes to appear on every startup.
            seen_patch_versions.append(version)
            self._save_app_settings()
        else:
            update_message = f"AMQ Trainer {version} is still available. Download and install it now?"
        if self.messagebox.askyesno(
            "Update available",
            update_message,
            parent=self.root,
        ):
            self._download_and_install_update(release)

    def _download_and_install_update(self, release: dict[str, str]) -> None:
        if self._update_install_in_progress:
            return
        self._update_install_in_progress = True
        self.status_var.set(f"Downloading AMQ Trainer {release['version']}…")
        target = Path(sys.executable).resolve()
        temporary = Path(tempfile.gettempdir()) / f"AMQTrainer-update-{os.getpid()}.exe"

        def work() -> None:
            error: Optional[str] = None
            try:
                if temporary.exists():
                    temporary.unlink()
                request = urllib.request.Request(
                    release["download_url"],
                    headers={"Accept": "application/octet-stream", "User-Agent": "AMQTrainer-Updater"},
                )
                with urllib.request.urlopen(request, timeout=120) as response, open(temporary, "wb") as handle:
                    shutil.copyfileobj(response, handle)
                if not temporary.exists() or temporary.stat().st_size < 1024 * 100:
                    raise RuntimeError("The downloaded update was incomplete.")
            except Exception as exc:
                error = str(exc)
                try:
                    temporary.unlink(missing_ok=True)
                except OSError:
                    pass
            try:
                self.root.after(0, lambda: self._finish_update_download(temporary, target, release["version"], error))
            except self.tk.TclError:
                pass

        threading.Thread(target=work, daemon=True).start()

    def _finish_update_download(self, temporary: Path, target: Path, version: str, error: Optional[str]) -> None:
        self._update_install_in_progress = False
        if error:
            self.status_var.set("Update download failed.")
            self.messagebox.showerror("Update download failed", error, parent=self.root)
            return
        if not temporary.exists():
            self.messagebox.showerror("Update failed", "The downloaded update could not be found.", parent=self.root)
            return
        if not os.access(target.parent, os.W_OK):
            temporary.unlink(missing_ok=True)
            self.messagebox.showerror(
                "Update failed",
                "The folder containing AMQTrainer.exe is not writable. Move the portable EXE to a folder you can write to and try again.",
                parent=self.root,
            )
            return
        script_path = Path(tempfile.gettempdir()) / f"AMQTrainer-updater-{os.getpid()}.cmd"
        source_text = str(temporary).replace('"', "")
        target_text = str(target).replace('"', "")
        script = f'''@echo off
setlocal
:wait_for_app
tasklist /FI "PID eq {os.getpid()}" /NH | findstr /C:"{os.getpid()}" >nul
if not errorlevel 1 (
  timeout /t 1 /nobreak >nul
  goto wait_for_app
)
move /Y "{source_text}" "{target_text}" >nul
start "" "{target_text}"
del "%~f0"
'''
        try:
            script_path.write_text(script, encoding="mbcs")
            flags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
            subprocess.Popen([os.environ.get("COMSPEC", "cmd.exe"), "/D", "/C", str(script_path)], creationflags=flags)
        except (OSError, subprocess.SubprocessError) as exc:
            temporary.unlink(missing_ok=True)
            script_path.unlink(missing_ok=True)
            self.messagebox.showerror("Update failed", str(exc), parent=self.root)
            return
        self.status_var.set(f"Installing AMQ Trainer {version}…")
        self.root.after(150, self.root.destroy)

    def _display_title(self, record: dict[str, Any]) -> str:
        if self.app_settings.get("title_language") == "Romaji":
            return _first_nonempty(record.get("animeJPName"), record.get("animeENName"), "Unknown anime")
        return _first_nonempty(record.get("animeENName"), record.get("animeJPName"), "Unknown anime")

    def _display_entry_title(self, entry: AnimeEntry) -> str:
        if self.app_settings.get("title_language") == "Romaji":
            return _first_nonempty(entry.extra.get("title_romaji"), entry.extra.get("title_english"), entry.title)
        return _first_nonempty(entry.extra.get("title_english"), entry.extra.get("title_romaji"), entry.title)

    def _display_song_label(self, song: dict[str, Any]) -> str:
        return f"{self._display_title(song)} — {song.get('songType', '').upper()} — {song.get('songName', '')} — {song.get('songArtist', '')}"

    def _build(self) -> None:
        self.content = self.ttk.Frame(self.root)
        self.content.pack(fill="both", expand=True)
        self.root.bind("<Escape>", lambda _event: self.show_quit_popup())
        self._build_main_menu()

    def _build_main_menu(self) -> None:
        """Render the asset-backed main menu and its five requested actions."""
        self._clear_content()
        self._resume_menu_player_if_allowed()
        canvas = self.tk.Canvas(self.content, bg=UI_BACKGROUND, highlightthickness=0)
        canvas.pack(fill="both", expand=True)
        self._main_canvas = canvas

        background = self._ui_background()
        canvas.create_image(0, 0, anchor="nw", image=background, tags=("background",))
        # The supplied Ika Musume composition sits beneath the media player.
        # The player is a child widget created below this canvas, so it stays
        # visually above the artwork even where their bounds overlap.
        logo = self._ui_images.setdefault("main-ika-logo", self._ui_image("ikamusume-logo.png").zoom(7, 7).subsample(4, 4))
        subtitle = self._ui_images.setdefault("main-ika-subtitle", self._ui_image("cooltext517429454677538.png").zoom(5, 5).subsample(9, 9))
        geso = self._ui_images.setdefault("main-geso", self._ui_image("geso1-display.png"))
        canvas.create_image(190, 94, anchor="nw", image=logo)
        canvas.create_image(160, 440, anchor="nw", image=subtitle)
        canvas.create_image(840, 70, anchor="nw", image=geso)

        # Compact media player: it uses its own MCI alias so it cannot
        # interrupt a quiz player. Keep the current record when returning
        # from another menu; only choose a new record when the current one is
        # unavailable or has not started yet.
        menu_records = self._playable_records()
        available_keys = {_record_key(record) for record in menu_records}
        if menu_records and (not self._menu_player_active or _record_key(self._menu_player_record or {}) not in available_keys):
            had_existing_record = self._menu_player_record is not None
            was_paused = self._menu_player_paused
            # A changed profile/song pool invalidates the old Prev history.
            self._menu_player_history.clear()
            self._menu_player_history_index = -1
            self._set_menu_player_record(random.choice(menu_records))
            self._menu_player_active = False
            # Autoplay is only applied when the app is starting without an
            # existing player state. Replacing a missing song later should
            # preserve the user's current play/pause intent.
            self._menu_player_paused = (
                not bool(self.app_settings.get("menu_autoplay", True))
                if not had_existing_record
                else was_paused
            )
        elif not menu_records:
            self._menu_player_record = None
            self._menu_player_active = False
            self._menu_player_paused = False
            self._menu_player_history.clear()
            self._menu_player_history_index = -1
        player_panel = self.tk.Frame(
            self.content,
            bg=UI_PANEL_DARK,
            highlightthickness=2,
            highlightbackground=UI_PINK,
            highlightcolor=UI_PINK,
        )
        # Match the player panel's outer left/top inset to the play control's
        # inner left inset so the whole composition starts on one grid.
        player_panel.place(x=24, y=24, width=340, height=141)
        player_content_x = 10
        player_content_width = 316
        player_season = self.tk.StringVar(value="Unknown season")
        player_title = self.tk.StringVar(value="Song Player")
        player_detail = self.tk.StringVar(value="No downloaded songs available")
        player_time = self.tk.StringVar(value="0:00 / 0:00")
        seek_var = self.tk.DoubleVar(value=0.0)
        # All player content shares one inset rectangle.  The five-pixel gaps
        # between rows and the nine-pixel top/bottom padding keep the layout
        # visually balanced inside the bordered panel.
        self.tk.Label(player_panel, textvariable=player_season, bg=UI_PANEL_DARK, fg=UI_MUTED, font=(self._ui_font_family, 8, "bold"), anchor="w").place(x=player_content_x, y=9, width=player_content_width, height=15)
        self.tk.Label(player_panel, textvariable=player_title, bg=UI_PANEL_DARK, fg=UI_TEXT, font=(self._ui_font_family, 10, "bold"), anchor="w", width=38).place(x=player_content_x, y=29, width=player_content_width, height=18)
        self.tk.Label(player_panel, textvariable=player_detail, bg=UI_PANEL_DARK, fg=UI_MUTED, font=(self._ui_font_family, 8), anchor="w", width=48).place(x=player_content_x, y=52, width=player_content_width, height=15)
        seek_row = self.tk.Frame(player_panel, bg=UI_PANEL_DARK)
        seek_row.place(x=player_content_x, y=72, width=player_content_width, height=22)
        self.tk.Label(seek_row, textvariable=player_time, bg=UI_PANEL_DARK, fg=UI_TEXT, font=(self._ui_font_family, 8), width=10, anchor="w").pack(side="left", fill="y")
        player_controls = self.tk.Frame(player_panel, bg=UI_PANEL_DARK)
        player_controls.place(x=player_content_x, y=99, width=player_content_width, height=29)
        for column in range(4):
            player_controls.grid_columnconfigure(column, weight=1)
        player_state = {"playing": bool(menu_records) and not self._menu_player_paused}
        loop_state = {"enabled": bool(self._menu_player_loop_enabled)}
        seek_state = {"dragging": False}
        player_poll_job: list[Optional[str]] = [None]
        displayed_record_key: list[str] = [""]
        marquee_states = {
            "title": {"full": "", "offset": 0, "direction": 1},
            "detail": {"full": "", "offset": 0, "direction": 1},
        }

        def set_marquee_text(state_name: str, variable: Any, text: str, maximum: int) -> None:
            state = marquee_states[state_name]
            state["full"] = text
            state["offset"] = 0
            state["direction"] = 1
            state["hold_until"] = time.monotonic() + 1.0
            variable.set(text[:maximum])

        def advance_marquee() -> None:
            if not player_panel.winfo_exists():
                return
            for state_name, variable, maximum in (("title", player_title, 38), ("detail", player_detail, 48)):
                state = marquee_states[state_name]
                full = str(state["full"])
                if len(full) <= maximum:
                    variable.set(full)
                    continue
                offset = int(state["offset"])
                variable.set(full[offset:offset + maximum])
                now = time.monotonic()
                if now < float(state.get("hold_until", 0.0)):
                    continue
                last_offset = len(full) - maximum
                if offset >= last_offset and state["direction"] > 0:
                    state["direction"] = -1
                    state["hold_until"] = now + 1.0
                elif offset <= 0 and state["direction"] < 0:
                    state["direction"] = 1
                    state["hold_until"] = now + 1.0
                else:
                    state["offset"] = offset + int(state["direction"])
            self.root.after(300, advance_marquee)

        def update_player_labels() -> None:
            record = self._menu_player_record
            if not record:
                player_season.set("No song selected")
                player_title.set("Song Player")
                player_detail.set("No downloaded songs available")
                return
            player_season.set(_clean(record.get("animeVintage")) or "Unknown season")
            set_marquee_text("title", player_title, self._display_title(record), 38)
            set_marquee_text("detail", player_detail, f"{_clean(record.get('songType'))} · {_clean(record.get('songName'))} · {_clean(record.get('songArtist'))}", 48)

        def play_menu_record() -> None:
            if not player_panel.winfo_exists():
                return
            if self._play_menu_player_audio():
                player_state["playing"] = True
                update_play_button_visual()
            else:
                player_state["playing"] = False
                player_detail.set("Could not play this song")
                update_play_button_visual()
            update_player_labels()
            displayed_record_key[0] = _record_key(self._menu_player_record or {})

        def format_player_time(milliseconds: int) -> str:
            seconds = max(0, int(milliseconds / 1000))
            return f"{seconds // 60}:{seconds % 60:02d}"

        def poll_player_progress() -> None:
            if not player_panel.winfo_exists():
                return
            if self._menu_player_active and self._menu_player_record:
                _result, position_text = self.menu_player._command(f"status {self.menu_player.alias} position")
                _result, length_text = self.menu_player._command(f"status {self.menu_player.alias} length")
                try:
                    position = max(0, int(position_text))
                except (TypeError, ValueError):
                    position = 0
                try:
                    length = max(0, int(length_text))
                except (TypeError, ValueError):
                    length = 0
                if length:
                    current_key = _record_key(self._menu_player_record)
                    if current_key != displayed_record_key[0]:
                        update_player_labels()
                        displayed_record_key[0] = current_key
                    if not seek_state["dragging"]:
                        seek_var.set(min(100.0, 100.0 * position / length))
                    player_time.set(f"{format_player_time(position)} / {format_player_time(length)}")
                else:
                    player_time.set("0:00 / 0:00")
            player_poll_job[0] = self.root.after(500, poll_player_progress)

        def next_menu_record() -> None:
            records = self._playable_records() or menu_records
            if not records:
                return
            current_key = _record_key(self._menu_player_record or {})
            if self._menu_player_history_index + 1 < len(self._menu_player_history):
                candidate = self._menu_player_history[self._menu_player_history_index + 1]
                if _record_key(candidate) in {_record_key(record) for record in records}:
                    self._set_menu_player_record(candidate, remember=False)
                else:
                    self._menu_player_history = self._menu_player_history[: self._menu_player_history_index + 1]
                    choices = [record for record in records if _record_key(record) != current_key] or records
                    self._set_menu_player_record(random.choice(choices))
            else:
                choices = [record for record in records if record is not self._menu_player_record and _record_key(record) != current_key]
                if not choices and len(records) > 1:
                    choices = [record for record in records if record is not self._menu_player_record]
                choices = choices or records
                self._set_menu_player_record(random.choice(choices))
            play_menu_record()

        def previous_menu_record() -> None:
            records = self._playable_records() or menu_records
            if not records or not self._menu_player_record:
                return
            valid_keys = {_record_key(record) for record in records}
            while self._menu_player_history_index > 0:
                self._menu_player_history_index -= 1
                candidate = self._menu_player_history[self._menu_player_history_index]
                if _record_key(candidate) in valid_keys:
                    self._menu_player_record = candidate
                    play_menu_record()
                    return
            # At the beginning of history, Prev restarts the current song;
            # it never falls back to an unrelated random selection.
            play_menu_record()

        def toggle_menu_player() -> None:
            if not self._menu_player_record:
                return
            if player_state["playing"]:
                # MCI pause/resume is supported by the same native API used
                # for quiz clips and avoids reopening the file.
                self.menu_player._command(f"pause {self.menu_player.alias}")
                player_state["playing"] = False
                self._menu_player_paused = True
                update_play_button_visual()
            else:
                if not self._menu_player_active:
                    play_menu_record()
                else:
                    self.menu_player._command(f"resume {self.menu_player.alias}")
                    player_state["playing"] = True
                    self._menu_player_paused = False
                    self._menu_player_suspended = False
                    update_play_button_visual()

        def toggle_loop() -> None:
            loop_state["enabled"] = not loop_state["enabled"]
            self._menu_player_loop_enabled = loop_state["enabled"]
            loop_button._kanon_active = loop_state["enabled"]
            loop_button._render_kanon_state(loop_state["enabled"])

        def seek_changed(value: str) -> None:
            if not seek_state["dragging"] or not self._menu_player_active or not self._menu_player_record:
                return
            _result, length_text = self.menu_player._command(f"status {self.menu_player.alias} length")
            try:
                length = max(0, int(length_text))
                target = int(float(value) / 100.0 * length)
            except (TypeError, ValueError):
                return
            self.menu_player._command(f"seek {self.menu_player.alias} to {target}")

        def begin_seek(_event: Any = None) -> None:
            seek_state["dragging"] = True

        def finish_seek(_event: Any = None) -> None:
            if not seek_state["dragging"] or not self._menu_player_active or not self._menu_player_record:
                seek_state["dragging"] = False
                return
            seek_changed(str(seek_var.get()))
            if player_state["playing"]:
                self.menu_player._command(f"play {self.menu_player.alias}")
            seek_state["dragging"] = False

        def make_player_slider(master: Any, variable: Any, callback: Optional[Callable[[str], None]] = None) -> Any:
            """Create the compact Kanon slider used by the menu player."""
            slider = self.tk.Canvas(master, width=240, height=22, bg=UI_PANEL_DARK, highlightthickness=0)
            track_y = 9
            # A rounded, five-pixel track is centered on the same horizontal
            # axis as the timestamp label.  The knob moves independently and
            # does not recolor the track.
            # Leave one knob radius of room at each canvas edge so the circle
            # remains fully visible at both 0:00 and the song's end.
            track_start, track_end = 11.0, 229.0
            slider.create_line(track_start, track_y, track_end, track_y, fill=UI_MUTED, width=5, capstyle="round")
            seek = self._ui_images.setdefault("player-seek-small", self._ui_image("Elements/Settings/seek.png").subsample(5, 5))
            knob_y = track_y
            knob_id = slider.create_image(22, knob_y, anchor="center", image=seek)
            # Match the knob's travel range to the visible track endpoints so
            # 0:00 and the full duration land exactly on the bar's edges.

            def render(*_args: Any) -> None:
                try:
                    value = max(0.0, min(100.0, float(variable.get())))
                except (TypeError, ValueError):
                    value = 0.0
                x = track_start + (value / 100.0) * (track_end - track_start)
                slider.coords(knob_id, x, knob_y)

            def set_from_event(event: Any) -> None:
                value = max(0.0, min(100.0, (float(event.x) - track_start) / (track_end - track_start) * 100.0))
                variable.set(int(round(value)))
                render()
                if callback:
                    callback(str(value))

            slider.bind("<Button-1>", set_from_event)
            slider.bind("<B1-Motion>", set_from_event)
            variable.trace_add("write", render)
            slider.render = render
            render()
            return slider

        def make_play_control() -> Any:
            """Create the circular play/pause control used by the player."""
            diameter = 30
            control = self.tk.Canvas(
                player_controls,
                width=diameter,
                height=diameter,
                bg=UI_PANEL_DARK,
                highlightthickness=0,
                cursor=self._app_cursor,
            )
            circle_id = control.create_oval(2, 2, diameter - 2, diameter - 2, width=1, outline=UI_MUTED, fill=UI_PANEL)
            pause_left_id = control.create_rectangle(10, 9, 13, 21, fill=UI_TEXT, outline="")
            pause_right_id = control.create_rectangle(17, 9, 20, 21, fill=UI_TEXT, outline="")
            play_id = control.create_polygon(11, 8, 11, 22, 21, 15, fill=UI_TEXT, outline="")
            control._kanon_active = False
            control._kanon_hover = False

            def render(playing: bool) -> None:
                control._kanon_active = playing
                fill = UI_PINK if playing else UI_PANEL
                if control._kanon_hover:
                    fill = UI_PINK_LIGHT if playing else "#343238"
                control.itemconfigure(circle_id, fill=fill, outline=UI_TEXT)
                control.itemconfigure(pause_left_id, state="normal" if playing else "hidden")
                control.itemconfigure(pause_right_id, state="normal" if playing else "hidden")
                control.itemconfigure(play_id, state="hidden" if playing else "normal")

            control._render_play_state = render
            control.bind("<Button-1>", lambda _event: toggle_menu_player())
            control.bind("<Enter>", lambda _event: (setattr(control, "_kanon_hover", True), render(bool(control._kanon_active))))
            control.bind("<Leave>", lambda _event: (setattr(control, "_kanon_hover", False), render(bool(control._kanon_active))))
            control.grid(row=0, column=0, padx=4)
            return control

        def kanon_control(label: str, command: Callable[[], None], column: int) -> Any:
            """Draw a crisp capsule instead of scaling the raster button border."""
            width, height = 70, 29
            button = self.tk.Canvas(player_controls, width=width, height=height, bg=UI_PANEL_DARK, highlightthickness=0, cursor=self._app_cursor)
            # Keep the rounded caps inside the canvas.  The previous right
            # endpoint extended past the 70px canvas and clipped that border.
            cap_inset = height / 2 - 0.5
            outer_items = (button.create_line(cap_inset, height / 2, width - cap_inset, height / 2, width=height - 2, fill=UI_MUTED, capstyle="round"),)
            inner_items = (button.create_line(cap_inset, height / 2, width - cap_inset, height / 2, width=height - 4, fill=UI_PANEL_DARK, capstyle="round"),)
            text_id = button.create_text(width / 2, height / 2, text=label, fill=UI_TEXT, font=(self._ui_font_family, 8, "bold"))
            button._kanon_active = False
            button._kanon_hover = False

            def render(active: bool) -> None:
                button._kanon_active = active
                highlighted = active or button._kanon_hover
                border_color = UI_PINK if highlighted else UI_MUTED
                fill_color = UI_PINK if highlighted else UI_PANEL_DARK
                for item in outer_items:
                    button.itemconfigure(item, fill=border_color)
                for item in inner_items:
                    button.itemconfigure(item, fill=fill_color)
                button.itemconfigure(text_id, fill=UI_TEXT)

            button._render_kanon_state = render
            button.bind("<Button-1>", lambda _event: command())
            button.bind("<Enter>", lambda _event: (setattr(button, "_kanon_hover", True), render(bool(button._kanon_active))))
            button.bind("<Leave>", lambda _event: (setattr(button, "_kanon_hover", False), render(bool(button._kanon_active))))
            button.grid(row=0, column=column, padx=3)
            render(False)
            return button

        play_button = make_play_control()

        def update_play_button_visual() -> None:
            playing = bool(player_state["playing"])
            play_button._kanon_active = playing
            play_button._render_play_state(playing)

        update_play_button_visual()
        previous_button = kanon_control("Prev", previous_menu_record, 1)
        next_button = kanon_control("Next", next_menu_record, 2)
        loop_button = kanon_control("Loop", toggle_loop, 3)
        seek_canvas = make_player_slider(seek_row, seek_var, seek_changed)
        seek_canvas.pack(side="left", fill="x", expand=True)
        seek_canvas.bind("<ButtonPress-1>", begin_seek, add="+")
        seek_canvas.bind("<ButtonRelease-1>", finish_seek, add="+")
        update_player_labels()
        self.root.after_idle(advance_marquee)
        if menu_records and not self._menu_player_active and not self._menu_player_paused:
            self.root.after_idle(play_menu_record)
        self.root.after_idle(poll_player_progress)

        buttons = (
            ("Play", "new-game-icon.png", self._build_play_home),
            ("Profile", "load-icon.png", self.show_profile_menu),
            ("Stats", "about-icon.png", self._build_stats_page),
            ("Settings", "preferences-icon.png", self.open_settings),
            ("Quit", "quit-icon.png", self.show_quit_popup),
        )
        start_x, y, gap = 33, 530, 8
        normal = self._ui_images.setdefault("main-button-normal-1280", self._ui_image("Elements/Main Menu/button.png").zoom(2, 2).subsample(3, 3))
        hover = self._ui_images.setdefault("main-button-hover-1280", self._ui_image("Elements/Main Menu/button-hover.png").zoom(2, 2).subsample(3, 3))
        for index, (label, icon_name, callback) in enumerate(buttons):
            x = start_x + index * (237 + gap)
            tag = f"main-button-{index}"
            bg = canvas.create_image(x, y, anchor="nw", image=normal, tags=(tag,))
            icon_key = f"main-icon-1280-{icon_name}"
            icon_image = self._ui_images.setdefault(icon_key, self._ui_image(f"Elements/Main Menu/Icons/{icon_name}").zoom(2, 2).subsample(3, 3))
            icon = canvas.create_image(x + 18, y + 10, anchor="nw", image=icon_image, tags=(tag,))
            text = canvas.create_text(x + 150, y + 42, text=label, fill=UI_TEXT, font=(self._ui_font_family, 18), tags=(tag,))
            canvas.tag_bind(tag, "<Enter>", lambda _event, item=bg: canvas.itemconfigure(item, image=hover))
            canvas.tag_bind(tag, "<Leave>", lambda _event, item=bg: canvas.itemconfigure(item, image=normal))
            def dispatch_main_click(event: Any, expected_tag: str = tag, action: Callable[[], None] = callback) -> None:
                if expected_tag in canvas.gettags("current"):
                    action()
                    return "break"
                return None
            canvas.bind("<Button-1>", dispatch_main_click, add="+")

        canvas.create_text(640, 695, text=f"{self.profile_var.get()}  ·  {self.status_var.get()}", fill=UI_TEXT, font=(self._ui_font_family, 10), tags=("status",))
        if self.startup_loading:
            # Profile restoration rebuilds the main menu. Recreate the shield
            # after that rebuild so the navigation cannot be clicked midway.
            self._show_startup_loading("Restoring saved profile…", 55)

    def _center_window(self, window: Any, width: int, height: int) -> None:
        self.root.update_idletasks()
        x = self.root.winfo_rootx() + max(0, (self.root.winfo_width() - width) // 2)
        y = self.root.winfo_rooty() + max(0, (self.root.winfo_height() - height) // 2)
        window.geometry(f"{width}x{height}+{x}+{y}")

    def _activate_dialog(self, dialog: Any) -> None:
        """Bring a borderless popup above the main canvas and give it focus."""
        try:
            self.root.update_idletasks()
            # The popup artwork has transparent rounded corners. On Windows,
            # make the canvas background color transparent too so the main
            # menu remains visible through those corners instead of showing a
            # rectangular dark/black window behind the artwork.
            dialog.wm_attributes("-transparentcolor", UI_TRANSPARENT)
            dialog.lift()
            dialog.focus_force()
        except self.tk.TclError:
            pass

    def _popup_button(self, canvas: Any, x: int, y: int, text: str, command: Callable[[], None], primary: bool = False, hover_options: bool = True, hover_image: Any = None) -> None:
        if hover_options:
            normal = self._ui_images.setdefault("popup-choice-normal", self._ui_image("Elements/Main Menu/button.png").zoom(3, 3).subsample(5, 5))
            hover = self._ui_images.setdefault("popup-choice-hover", self._ui_image("Elements/Main Menu/button-hover.png").zoom(3, 3).subsample(5, 5))
        else:
            normal_path = "Elements/Popup/button-primary.png" if primary else "Elements/Popup/button-secondary.png"
            normal = self._ui_image(normal_path)
            hover = hover_image or normal
        tag = f"popup-button-{id(command)}"
        button_item = canvas.create_image(x, y, anchor="nw", image=normal, tags=(tag,))
        canvas.create_text(x + (normal.width() // 2), y + (normal.height() // 2), text=text, fill=UI_TEXT, font=(self._ui_font_family, 15), tags=(tag,))
        canvas.tag_bind(tag, "<Button-1>", lambda _event: command())
        if hover_options or hover_image is not None:
            canvas.tag_bind(tag, "<Enter>", lambda _event, item=button_item: canvas.itemconfigure(item, image=hover))
            canvas.tag_bind(tag, "<Leave>", lambda _event, item=button_item: canvas.itemconfigure(item, image=normal))
        canvas.tag_bind(tag, "<Enter>", lambda _event: canvas.configure(cursor=self._app_cursor), add="+")
        canvas.tag_bind(tag, "<Leave>", lambda _event: canvas.configure(cursor=self._app_cursor), add="+")

    def _open_choice_popup(
        self,
        title: str,
        choices: list[tuple[str, Callable[[], None]]],
        hover_options: bool = False,
        show_back_button: bool = False,
        back_command: Optional[Callable[[], None]] = None,
    ) -> None:
        dialog = self.tk.Toplevel(self.root)
        dialog.title(title)
        dialog.configure(bg=UI_PINK)
        dialog.overrideredirect(True)
        dialog.transient(self.root)
        dialog.grab_set()
        # Profile now has three actions.  Start that shorter list lower so it
        # remains balanced beneath the arrow/title row instead of leaving a
        # large empty area at the bottom of the popup.
        choice_start = 150 if show_back_button else (150 if hover_options and len(choices) == 3 else (120 if hover_options and len(choices) == 4 else 94))
        choice_gap = 97 if hover_options and len(choices) == 4 else (90 if hover_options and len(choices) > 4 else (84 if len(choices) > 4 else 96))
        choice_height = 77 if hover_options else 88
        popup_height = max(POPUP_HEIGHT, choice_start + max(0, len(choices) - 1) * choice_gap + choice_height)
        self._center_window(dialog, POPUP_WIDTH, popup_height)
        surface = self.tk.Frame(dialog, bg=UI_BACKGROUND)
        surface.pack(fill="both", expand=True, padx=4, pady=4)
        canvas = self.tk.Canvas(surface, width=POPUP_WIDTH - 8, height=popup_height - 8, bg=UI_BACKGROUND, highlightthickness=0)
        canvas.pack(fill="both", expand=True)
        # The popup arrow is centered at local y=85 (hitbox y=35 plus its
        # centered sprite at y=50), so keep the heading on that same tip line.
        title_y = 85 if show_back_button else 55
        canvas.create_text(273, title_y, text=title, fill=UI_TEXT, font=(self._ui_font_family, 24, "bold"))
        if show_back_button:
            def leave_popup(_event: Any = None) -> str:
                dialog.destroy()
                (back_command or self._build_profile_home)()
                return "break"
            # Use a transparent canvas as a generous hitbox so the whole
            # arrow area responds, rather than only the sprite pixels.
            back_hitbox = self.tk.Canvas(surface, width=120, height=100, bg=UI_BACKGROUND, highlightthickness=0, cursor=self._app_cursor)
            back_hitbox.place(x=35, y=35)
            back_arrow = self._ui_images.setdefault("popup-back-arrow", self._ui_image("Elements/back-button.png").zoom(3, 3).subsample(4, 4))
            back_hitbox.create_image(60, 50, image=back_arrow)
            back_hitbox.bind("<Button-1>", leave_popup)
        choice_normal = self._ui_images.setdefault("popup-choice-normal", self._ui_image("Elements/Main Menu/button.png").zoom(3, 3).subsample(5, 5)) if hover_options else None
        choice_hover = self._ui_images.setdefault("popup-choice-hover", self._ui_image("Elements/Main Menu/button-hover.png").zoom(3, 3).subsample(5, 5)) if hover_options else None
        for index, (label, callback) in enumerate(choices):
            def run(action=callback, popup=dialog):
                popup.destroy()
                action()
            if hover_options:
                image = choice_normal
                hover_image = choice_hover
            else:
                image_path = "Elements/Popup/button-primary.png" if index == 0 else "Elements/Popup/button-secondary.png"
                image = self._ui_image(image_path)
                hover_image = image
            x = (POPUP_WIDTH - image.width()) // 2
            y = choice_start + index * choice_gap
            tag = f"choice-{index}"
            button_item = canvas.create_image(x, y, anchor="nw", image=image, tags=(tag,))
            canvas.create_text(273, y + image.height() // 2, text=label, fill=UI_TEXT, font=(self._ui_font_family, 15), tags=(tag,))
            def dispatch_choice_click(event: Any, expected_tag: str = tag, action: Callable[[], None] = run) -> None:
                if expected_tag in canvas.gettags("current"):
                    action()
                    return "break"
                return None
            canvas.bind("<Button-1>", dispatch_choice_click, add="+")
            if hover_options:
                canvas.tag_bind(tag, "<Enter>", lambda _event, item=button_item, active=hover_image: canvas.itemconfigure(item, image=active))
                canvas.tag_bind(tag, "<Leave>", lambda _event, item=button_item, idle=image: canvas.itemconfigure(item, image=idle))
            canvas.tag_bind(tag, "<Enter>", lambda _event: canvas.configure(cursor=self._app_cursor), add="+")
            canvas.tag_bind(tag, "<Leave>", lambda _event: canvas.configure(cursor=self._app_cursor), add="+")
        dialog.protocol("WM_DELETE_WINDOW", dialog.destroy)
        dialog.bind("<Escape>", lambda _event: dialog.destroy())
        self._activate_dialog(dialog)

    def show_profile_menu(self) -> None:
        self._open_choice_popup("Profile", [
            ("Select Profile", self.select_profile),
            ("New Profile", self.new_profile),
            ("Edit Profile", self.edit_profile),
        ], hover_options=True, show_back_button=True)

    def show_play_menu(self) -> None:
        self._build_play_home()

    def show_stats_menu(self) -> None:
        self._open_choice_popup("Stats", [("View Stats", self._build_stats_page)])

    def show_settings_menu(self) -> None:
        self._open_choice_popup("Settings", [("Open Settings", self.open_settings)])

    def show_quit_popup(self) -> None:
        dialog = self.tk.Toplevel(self.root)
        dialog.title("Quit")
        dialog.configure(bg=UI_PINK)
        dialog.overrideredirect(True)
        dialog.transient(self.root)
        dialog.grab_set()
        self._center_window(dialog, POPUP_WIDTH, POPUP_HEIGHT)
        surface = self.tk.Frame(dialog, bg=UI_BACKGROUND)
        surface.pack(fill="both", expand=True, padx=4, pady=4)
        canvas = self.tk.Canvas(surface, width=POPUP_WIDTH - 8, height=POPUP_HEIGHT - 8, bg=UI_BACKGROUND, highlightthickness=0)
        canvas.pack(fill="both", expand=True)
        canvas.create_text(273, 150, text="Are you sure you\nwant to quit? > <", fill=UI_TEXT, font=(self._ui_font_family, 24, "bold"), justify="center")
        def quit_app() -> None:
            dialog.destroy()
            self.root.destroy()
        self._popup_button(canvas, 166, 270, "Yes, bye-bye!", quit_app, primary=True)
        self._popup_button(canvas, 166, 375, "I'm staying!", dialog.destroy, primary=False)
        dialog.protocol("WM_DELETE_WINDOW", dialog.destroy)
        dialog.bind("<Escape>", lambda _event: dialog.destroy())
        self._activate_dialog(dialog)

    def _schedule_menu_player_poll(self, delay_ms: int = 500) -> None:
        """Keep menu autoplay alive even when its visual page is rebuilt."""
        if self._menu_player_poll_job is not None:
            return
        try:
            self._menu_player_poll_job = self.root.after(delay_ms, self._poll_menu_player)
        except self.tk.TclError:
            self._menu_player_poll_job = None

    def _play_menu_player_audio(self) -> bool:
        """Start the currently selected menu track without depending on a widget."""
        record = self._menu_player_record
        path = _clean(record.get("download_path")) if record else ""
        if not path or not Path(path).exists():
            self._menu_player_active = False
            return False
        try:
            self.menu_player.play_full(path, self.app_settings.get("volume", 50))
        except Exception:
            self._menu_player_active = False
            return False
        self._menu_player_active = True
        self._menu_player_paused = False
        self._menu_player_suspended = False
        return True

    def _set_menu_player_record(self, record: dict[str, Any], remember: bool = True) -> None:
        """Select a menu track and keep a bounded history for Prev/Next."""
        self._menu_player_record = record
        if not remember:
            # Forward navigation through existing history must move the
            # cursor as well; otherwise repeated Next presses replay the same
            # history entry forever after using Prev.
            for history_index in range(len(self._menu_player_history) - 1, -1, -1):
                history_record = self._menu_player_history[history_index]
                if history_record is record or _record_key(history_record) == _record_key(record):
                    self._menu_player_history_index = history_index
                    break
            return
        if self._menu_player_history_index + 1 < len(self._menu_player_history):
            self._menu_player_history = self._menu_player_history[: self._menu_player_history_index + 1]
        key = _record_key(record)
        if self._menu_player_history and _record_key(self._menu_player_history[-1]) == key:
            self._menu_player_history[-1] = record
        else:
            self._menu_player_history.append(record)
        # Keep navigation bounded if the user leaves the app playing for a
        # long time, while retaining enough history for normal Prev use.
        if len(self._menu_player_history) > 100:
            overflow = len(self._menu_player_history) - 100
            del self._menu_player_history[:overflow]
        self._menu_player_history_index = len(self._menu_player_history) - 1

    def _advance_menu_player(self) -> None:
        """Perform the same forward transition as the Next button."""
        records = self._playable_records()
        if not records:
            self.menu_player.stop()
            self._menu_player_record = None
            self._menu_player_active = False
            return
        valid_keys = {_record_key(record) for record in records}
        if self._menu_player_history_index + 1 < len(self._menu_player_history):
            candidate = self._menu_player_history[self._menu_player_history_index + 1]
            if _record_key(candidate) in valid_keys:
                self._set_menu_player_record(candidate, remember=False)
                self._play_menu_player_audio()
                return
            self._menu_player_history = self._menu_player_history[: self._menu_player_history_index + 1]
        current_key = _record_key(self._menu_player_record or {})
        choices = [record for record in records if record is not self._menu_player_record and _record_key(record) != current_key]
        if not choices and len(records) > 1:
            # Some imported records can share a fallback key. Object identity
            # still lets autoplay choose a genuinely different track.
            choices = [record for record in records if record is not self._menu_player_record]
        choices = choices or records
        self._set_menu_player_record(random.choice(choices))
        self._play_menu_player_audio()

    def _poll_menu_player(self) -> None:
        """Monitor menu audio independently from whichever page is visible."""
        self._menu_player_poll_job = None
        try:
            if not self.root.winfo_exists():
                return
            if self._menu_player_active and self._menu_player_record and not self._menu_player_paused and not self._menu_player_suspended:
                _result, position_text = self.menu_player._command(f"status {self.menu_player.alias} position")
                _result, length_text = self.menu_player._command(f"status {self.menu_player.alias} length")
                _result, mode_text = self.menu_player._command(f"status {self.menu_player.alias} mode")
                try:
                    position = max(0, int(position_text))
                    length = max(0, int(length_text))
                except (TypeError, ValueError):
                    position = length = 0
                mode = _clean(mode_text).casefold()
                if mode in {"stopped", "stop"} or (length and position >= max(0, length - 250)):
                    if self._menu_player_loop_enabled:
                        self._play_menu_player_audio()
                    else:
                        self._advance_menu_player()
        except (self.tk.TclError, OSError, RuntimeError):
            # A transient MCI/Tk teardown must not terminate the mainloop.
            pass
        finally:
            self._schedule_menu_player_poll()

    def _suspend_menu_player(self) -> None:
        """Pause menu music for pages that own the audio channel."""
        if not getattr(self, "_menu_player_active", False) or getattr(self, "_menu_player_paused", False):
            return
        if not getattr(self, "_menu_player_suspended", False):
            self.menu_player._command(f"pause {self.menu_player.alias}")
            self._menu_player_suspended = True

    def _resume_menu_player_if_allowed(self) -> None:
        """Resume the same menu track when returning from an exclusive page."""
        if not getattr(self, "_menu_player_active", False):
            return
        self.menu_player.set_volume(self.app_settings.get("volume", 50))
        if getattr(self, "_menu_player_suspended", False) and not getattr(self, "_menu_player_paused", False):
            self.menu_player._command(f"resume {self.menu_player.alias}")
            self._menu_player_suspended = False

    def _clear_content(self) -> None:
        # Menu audio intentionally stays open while navigation pages are
        # rebuilt. Exclusive pages call _suspend_menu_player() themselves.
        for child in self.content.winfo_children():
            child.destroy()
        self.list_rows = {}

    def _profile_paths(self) -> list[Path]:
        if not PROFILE_ROOT.exists():
            return []
        return [folder / "profile.json" for folder in PROFILE_ROOT.iterdir() if folder.is_dir() and (folder / "profile.json").exists()]

    def _read_profile_payload(self, path: Path) -> Optional[dict[str, Any]]:
        try:
            with open(path, "r", encoding="utf-8") as handle:
                payload = json.load(handle)
            return payload if isinstance(payload, dict) else None
        except (OSError, ValueError, TypeError):
            return None

    def _write_profile_payload(self, path: Path, payload: dict[str, Any]) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, ensure_ascii=False, indent=2)

    def _song_paths_from_payload(self, payload: dict[str, Any]) -> set[Path]:
        paths: set[Path] = set()
        records = [*(payload.get("downloads") or [])]
        collection = payload.get("collection") or {}
        records.extend(collection.get("songs") or [])
        for record in records:
            path = _clean(record.get("download_path")) if isinstance(record, dict) else ""
            if path:
                paths.add(Path(path))
                paths.add(Path(path + ".part"))
        manifest = _clean(payload.get("manifest_path"))
        if manifest:
            paths.add(Path(manifest))
            paths.add(Path(manifest).with_name("download_manifest.csv"))
        output_dir = _clean(payload.get("output_dir"))
        if output_dir:
            output = Path(output_dir)
            paths.update({output / "download_manifest.json", output / "download_manifest.csv"})
        return paths

    def _clear_downloads_everywhere(self) -> int:
        deleted = 0
        for profile_path in self._profile_paths():
            payload = self._read_profile_payload(profile_path)
            if not payload:
                continue
            for path in self._song_paths_from_payload(payload):
                try:
                    if path.is_file():
                        path.unlink()
                        deleted += 1
                except OSError:
                    pass
            payload["downloads"] = []
            payload["manifest_path"] = ""
            collection = payload.get("collection")
            if isinstance(collection, dict):
                for song in collection.get("songs") or []:
                    if isinstance(song, dict):
                        song["download_path"] = ""
                        song["download_status"] = ""
            try:
                self._write_profile_payload(profile_path, payload)
            except OSError:
                continue
        self.download_records = []
        self.current_manifest_path = ""
        for song in (self.collection.songs if self.collection else []):
            song["download_path"] = ""
            song["download_status"] = ""
        return deleted

    def _clear_play_history_everywhere(self) -> None:
        for profile_path in self._profile_paths():
            payload = self._read_profile_payload(profile_path)
            if payload is not None:
                payload["play_stats"] = {}
                try:
                    self._write_profile_payload(profile_path, payload)
                except OSError:
                    pass
        self.play_stats = {}

    def _unflag_everywhere(self) -> int:
        count = 0
        for profile_path in self._profile_paths():
            payload = self._read_profile_payload(profile_path)
            if payload is None:
                continue
            stats = payload.get("play_stats") or {}
            changed = False
            for value in stats.values():
                if isinstance(value, dict) and value.get("flagged"):
                    value["flagged"] = False
                    count += 1
                    changed = True
            if changed:
                payload["play_stats"] = stats
                try:
                    self._write_profile_payload(profile_path, payload)
                except OSError:
                    pass
        for value in self.play_stats.values():
            if value.get("flagged"):
                value["flagged"] = False
        return count

    def _make_kanon_button(
        self,
        parent: Any,
        text: str,
        command: Callable[[], None],
        width: int = 112,
        height: int = 35,
        font_size: int = 10,
        active_color: str = UI_PINK,
        initial_active: bool = False,
        hover_color: str = UI_PINK_LIGHT,
    ) -> Any:
        """Create a reusable rounded Kanon-style button."""
        # Odd heights give the capsule a true half-pixel center, keeping the
        # top and bottom borders identical after Tk rasterizes the stroke.
        if height % 2 == 0:
            height += 1
        button = self.tk.Canvas(
            parent,
            width=width,
            height=height,
            bg=UI_BACKGROUND,
            highlightthickness=0,
            cursor=self._app_cursor,
        )
        cap_inset = height / 2 - 0.5
        outer_items = (
            button.create_line(
                cap_inset,
                height / 2,
                width - cap_inset,
                height / 2,
                width=height - 2,
                fill=UI_MUTED,
                capstyle="round",
            ),
        )
        inner_items = (
            button.create_line(
                cap_inset,
                height / 2,
                width - cap_inset,
                height / 2,
                width=height - 4,
                fill=UI_PANEL_DARK,
                capstyle="round",
            ),
        )
        text_id = button.create_text(
            width / 2,
            height / 2,
            text=text,
            fill=UI_TEXT,
            font=(self._ui_font_family, font_size, "bold"),
        )
        button._kanon_active = bool(initial_active)
        button._kanon_hover = False
        button._kanon_enabled = True
        button._kanon_command = command

        def render(active: bool = False) -> None:
            button._kanon_active = bool(active)
            highlighted = button._kanon_active or button._kanon_hover
            if not button._kanon_enabled:
                border_color = UI_MUTED
                fill_color = UI_PANEL_DARK
            else:
                border_color = active_color if highlighted else UI_MUTED
                fill_color = active_color if button._kanon_active else (hover_color if button._kanon_hover else UI_PANEL_DARK)
            for item in outer_items:
                button.itemconfigure(item, fill=border_color)
            for item in inner_items:
                button.itemconfigure(item, fill=fill_color)
            button.itemconfigure(text_id, fill=UI_TEXT)

        button._render_kanon_state = render
        button._set_kanon_enabled = lambda enabled: (setattr(button, "_kanon_enabled", bool(enabled)), render(button._kanon_active))
        button.bind("<Button-1>", lambda _event: command() if button._kanon_enabled else "break")
        button.bind("<Enter>", lambda _event: (setattr(button, "_kanon_hover", True), render(button._kanon_active)))
        button.bind("<Leave>", lambda _event: (setattr(button, "_kanon_hover", False), render(button._kanon_active)))
        render(button._kanon_active)
        return button

    def _delete_all_profiles(self) -> None:
        try:
            if PROFILE_ROOT.exists():
                shutil.rmtree(PROFILE_ROOT)
            PROFILE_ROOT.mkdir(parents=True, exist_ok=True)
        except OSError as exc:
            self.messagebox.showerror("Could not delete profiles", str(exc), parent=self.root)
            return
        self.profile_var.set("No profile selected")
        self.profile_name_var.set("")
        self.collection = None
        self.import_paths = []
        self.enabled_lists = set()
        self.excluded_song_keys = set()
        self.download_records = []
        self.play_stats = {}
        self.current_manifest_path = ""
        self.new_profile_mode = False
        self.path_var.set("")
        self._build_profile_home()
        self.root.after(80, self._show_no_profiles_prompt)
        self.status_var.set("All profiles were deleted. Create a new profile to begin.")

    def _make_ui_slider(self, parent: Any, label: str, variable: Any, minimum: float = 0, maximum: float = 100, suffix: str = "%", value_formatter: Optional[Callable[[float], str]] = None, center: bool = False) -> Any:
        frame = self.tk.Frame(parent, bg=UI_BACKGROUND)
        frame.pack(fill="x", pady=(0, 6))
        enabled_state = {"value": True}
        value_label = self.tk.Label(frame, text="", bg=UI_BACKGROUND, fg=UI_TEXT, font=(self._ui_font_family, 14))
        value_label.pack(anchor="center" if center else "w")
        slider = self.tk.Canvas(frame, width=400, height=60, bg=UI_BACKGROUND, highlightthickness=0)
        slider.pack(anchor="center" if center else "w")
        bar = self._ui_images.setdefault("settings-bar-half", self._ui_image("Elements/Settings/bar-empty.png").subsample(2, 2))
        seek = self._ui_images.setdefault("settings-seek-half", self._ui_image("Elements/Settings/seek.png").subsample(2, 2))
        slider.create_image(20, 5, anchor="nw", image=bar)
        # The track starts with a rounded cap. Fill its left half as well as
        # the rectangular middle so the minimum end never looks hollow.
        fill_cap_id = slider.create_arc(25, 10, 65, 50, start=90, extent=180, style="pieslice", fill=UI_PINK_LIGHT, outline="")
        fill_id = slider.create_rectangle(45, 10, 45, 50, fill=UI_PINK_LIGHT, outline="")
        knob_id = slider.create_image(45, 30, anchor="center", image=seek)

        def render(*_args: Any) -> None:
            try:
                value = max(float(minimum), min(float(maximum), float(variable.get())))
            except (TypeError, ValueError):
                value = float(minimum)
            ratio = (value - float(minimum)) / max(1.0, float(maximum) - float(minimum))
            x = 45 + ratio * 310
            slider.coords(fill_id, 45, 10, max(45, x), 50)
            slider.coords(knob_id, x, 30)
            fill_color = UI_PINK_LIGHT if enabled_state["value"] else UI_PANEL
            slider.itemconfigure(fill_cap_id, fill=fill_color)
            slider.itemconfigure(fill_id, fill=fill_color)
            slider.itemconfigure(knob_id, state="normal" if enabled_state["value"] else "hidden")
            value_label.configure(fg=UI_TEXT if enabled_state["value"] else UI_MUTED)
            shown = int(value) if value == int(value) else round(value, 1)
            value_label.configure(text=value_formatter(value) if value_formatter else f"{label}: {shown}{suffix}")

        def set_from_event(event: Any) -> None:
            ratio = max(0.0, min(1.0, (event.x - 45) / 310.0))
            value = float(minimum) + ratio * (float(maximum) - float(minimum))
            variable.set(int(round(value)) if float(minimum).is_integer() and float(maximum).is_integer() else round(value, 1))
            render()

        slider.bind("<Button-1>", set_from_event)
        slider.bind("<B1-Motion>", set_from_event)
        variable.trace_add("write", render)

        def set_enabled(enabled: bool) -> None:
            enabled_state["value"] = bool(enabled)
            slider.configure(state="normal" if enabled_state["value"] else "disabled")
            render()

        frame.set_enabled = set_enabled
        render()
        return frame

    def _make_ui_range_slider(self, parent: Any, label: str, low_variable: Any, high_variable: Any, minimum: int, maximum: int, suffix: str = "", center: bool = False) -> Any:
        frame = self.tk.Frame(parent, bg=UI_BACKGROUND)
        frame.pack(fill="x", pady=(0, 6))
        value_label = self.tk.Label(frame, text="", bg=UI_BACKGROUND, fg=UI_TEXT, font=(self._ui_font_family, 14))
        value_label.pack(anchor="center" if center else "w")
        slider = self.tk.Canvas(frame, width=400, height=60, bg=UI_BACKGROUND, highlightthickness=0)
        slider.pack(anchor="center" if center else "w")
        bar = self._ui_images.setdefault("settings-bar-half", self._ui_image("Elements/Settings/bar-empty.png").subsample(2, 2))
        seek = self._ui_images.setdefault("settings-seek-half", self._ui_image("Elements/Settings/seek.png").subsample(2, 2))
        slider.create_image(20, 5, anchor="nw", image=bar)
        fill_cap_id = slider.create_arc(25, 10, 65, 50, start=90, extent=180, style="pieslice", fill=UI_PINK_LIGHT, outline="", state="hidden")
        fill_id = slider.create_rectangle(45, 10, 355, 50, fill=UI_PINK_LIGHT, outline="")
        low_knob = slider.create_image(45, 30, anchor="center", image=seek)
        high_knob = slider.create_image(355, 30, anchor="center", image=seek)
        active_handle = {"name": "low"}

        def value_to_x(value: Any) -> float:
            ratio = (float(value) - minimum) / max(1.0, maximum - minimum)
            return 45 + max(0.0, min(1.0, ratio)) * 310

        def render(*_args: Any) -> None:
            try:
                low = max(minimum, min(maximum, int(low_variable.get())))
                high = max(minimum, min(maximum, int(high_variable.get())))
            except (TypeError, ValueError):
                low, high = minimum, maximum
            if low > high:
                low, high = high, low
                low_variable.set(low)
                high_variable.set(high)
            low_x, high_x = value_to_x(low), value_to_x(high)
            slider.itemconfigure(fill_cap_id, state="normal" if low_x <= 45.0 else "hidden")
            slider.coords(fill_id, low_x, 10, high_x, 50)
            slider.coords(low_knob, low_x, 30)
            slider.coords(high_knob, high_x, 30)
            value_label.configure(text=f"{label}: {low}{suffix} – {high}{suffix}")

        def set_from_event(event: Any) -> None:
            x = max(45.0, min(355.0, float(event.x)))
            value = int(round(minimum + (x - 45.0) / 310.0 * (maximum - minimum)))
            low = int(low_variable.get())
            high = int(high_variable.get())
            active_handle["name"] = "low" if abs(x - value_to_x(low)) <= abs(x - value_to_x(high)) else "high"
            if active_handle["name"] == "low":
                low_variable.set(min(value, high))
            else:
                high_variable.set(max(value, low))
            render()

        def drag(event: Any) -> None:
            x = max(45.0, min(355.0, float(event.x)))
            value = int(round(minimum + (x - 45.0) / 310.0 * (maximum - minimum)))
            low = int(low_variable.get())
            high = int(high_variable.get())
            if active_handle["name"] == "low":
                low_variable.set(min(value, high))
            else:
                high_variable.set(max(value, low))
            render()

        slider.bind("<Button-1>", set_from_event)
        slider.bind("<B1-Motion>", drag)
        low_variable.trace_add("write", render)
        high_variable.trace_add("write", render)
        render()
        return frame

    def open_settings(self) -> None:
        if self.count_refresh_job:
            try:
                self.root.after_cancel(self.count_refresh_job)
            except self.tk.TclError:
                pass
            self.count_refresh_job = None
        # Settings is a full application page rather than a modal popup. This
        # keeps the 1280x720 design surface consistent with Stats/Profile and
        # avoids leaving a hidden Toplevel grab behind when returning home.
        self._clear_content()
        surface = self.tk.Frame(self.content, bg=UI_BACKGROUND)
        surface.pack(fill="both", expand=True)
        back = self._ui_image("Elements/back-button.png")
        back_button = self.tk.Label(surface, image=back, bg=UI_BACKGROUND, cursor=self._app_cursor)
        back_button.place(x=25, y=22)
        self.tk.Label(surface, text="Settings", bg=UI_BACKGROUND, fg=UI_TEXT, font=(self._ui_font_family, 24, "bold")).place(relx=0.5, y=78, anchor="center")

        settings_area = self.tk.Frame(surface, bg=UI_BACKGROUND)
        settings_area.place(x=140, y=126, width=1000, height=495)
        left_column = self.tk.Frame(settings_area, bg=UI_BACKGROUND)
        left_column.place(x=0, y=0, width=470, height=495)
        right_column = self.tk.Frame(settings_area, bg=UI_BACKGROUND)
        right_column.place(x=530, y=0, width=470, height=495)
        title_var = self.tk.StringVar(value=self.app_settings.get("title_language", "English"))
        self.tk.Label(left_column, text="Anime Titles", bg=UI_BACKGROUND, fg=UI_TEXT, font=(self._ui_font_family, 16, "bold")).pack(anchor="w")
        language_row = self.tk.Frame(left_column, bg=UI_BACKGROUND)
        language_row.pack(anchor="w", pady=(5, 14))
        language_buttons: dict[str, Any] = {}
        for language in ("English", "Romaji"):
            language_buttons[language] = self._make_kanon_button(
                language_row,
                language,
                lambda value=language: title_var.set(value),
                width=105,
                height=34,
                font_size=10,
            )
            language_buttons[language].pack(side="left", padx=(0, 8))
        def refresh_language_buttons(*_args: Any) -> None:
            for language, button in language_buttons.items():
                button._render_kanon_state(title_var.get() == language)
        title_var.trace_add("write", refresh_language_buttons)
        refresh_language_buttons()

        autoplay_var = self.tk.BooleanVar(value=bool(self.app_settings.get("menu_autoplay", True)))
        autoplay_button = self._make_kanon_button(
            left_column,
            "Autoplay",
            lambda: autoplay_var.set(not autoplay_var.get()),
            width=132,
            height=34,
            font_size=10,
        )
        autoplay_button.pack(anchor="w", pady=(0, 14))
        autoplay_var.trace_add("write", lambda *_args: autoplay_button._render_kanon_state(bool(autoplay_var.get())))
        autoplay_button._render_kanon_state(bool(autoplay_var.get()))

        song_path_var = self.tk.StringVar(value=_clean(self.app_settings.get("song_path")))

        def choose_song_path() -> None:
            current = _clean(song_path_var.get()) or _clean(self.output_var.get())
            selected = self.filedialog.askdirectory(
                parent=self.root,
                initialdir=str(Path(current).expanduser()) if current else None,
                title="Choose Song Folder",
            )
            if selected:
                song_path_var.set(str(Path(selected).expanduser()))

        volume_var = self.tk.IntVar(value=int(self.app_settings.get("volume", 50)))
        learn_var = self.tk.IntVar(value=int(self.app_settings.get("learn_new_ratio", 50)))
        flagged_var = self.tk.IntVar(value=int(self.app_settings.get("flagged_ratio", 100)))
        boundary_var = self.tk.IntVar(value=int(float(self.app_settings.get("review_boundary", 50))))
        review_hard_ratio_var = self.tk.IntVar(value=int(self.app_settings.get("review_hard_ratio", 80)))
        self._make_ui_slider(left_column, "Volume", volume_var)
        self._make_ui_slider(left_column, "Learn - New Songs", learn_var)
        self._make_ui_slider(left_column, "Flagged Songs", flagged_var)
        self._make_ui_slider(right_column, "Review Difficulty Boundary", boundary_var)
        self._make_ui_slider(
            right_column,
            "Review Ratio",
            review_hard_ratio_var,
            value_formatter=lambda value: f"Review Ratio — Hard: {int(round(value))}% / Easy: {100 - int(round(value))}%",
        )
        self._make_kanon_button(right_column, "Check for Updates", self.check_for_updates, width=180, height=34, font_size=9).pack(anchor="w", pady=(0, 4))

        actions_frame = self.tk.LabelFrame(
            right_column,
            text="Data Management",
            bg=UI_BACKGROUND,
            fg=UI_TEXT,
            bd=1,
            relief="groove",
            font=(self._ui_font_family, 14),
            padx=2,
            pady=2,
        )
        actions_frame.pack(fill="x", pady=(5, 8))
        for column in range(2):
            actions_frame.columnconfigure(column, weight=1)
        for row, column, label, command in (
            (0, 0, "Delete all Downloads", lambda: self._settings_delete_downloads(self.root)),
            (0, 1, "Delete all Profiles", lambda: self._settings_delete_profiles(self.root)),
            (1, 0, "Clear Play History", lambda: self._settings_clear_history(self.root)),
            (1, 1, "Unflag all Flagged Songs", lambda: self._settings_unflag(self.root)),
        ):
            self._make_kanon_button(actions_frame, label, command, width=210, height=34, font_size=9).grid(row=row, column=column, padx=5, pady=5)
        self._make_kanon_button(actions_frame, "Open Song Directory", lambda: self.open_song_directory(self.root), width=210, height=34, font_size=9).grid(row=2, column=0, padx=5, pady=5)
        self._make_kanon_button(actions_frame, "Change Song Path", choose_song_path, width=210, height=34, font_size=9).grid(row=2, column=1, padx=5, pady=5)

        initial_values = {
            "title_language": title_var.get(),
            "menu_autoplay": bool(autoplay_var.get()),
            "song_path": song_path_var.get(),
            "volume": int(volume_var.get()),
            "learn_new_ratio": int(learn_var.get()),
            "flagged_ratio": int(flagged_var.get()),
            "review_boundary": int(boundary_var.get()),
            "review_hard_ratio": int(review_hard_ratio_var.get()),
        }
        restore_defaults_requested = {"value": False}

        def form_values() -> dict[str, Any]:
            return {
                "title_language": title_var.get(),
                "menu_autoplay": bool(autoplay_var.get()),
                "song_path": song_path_var.get(),
                "volume": int(volume_var.get()),
                "learn_new_ratio": int(learn_var.get()),
                "flagged_ratio": int(flagged_var.get()),
                "review_boundary": int(boundary_var.get()),
                "review_hard_ratio": int(review_hard_ratio_var.get()),
            }

        def has_unsaved_changes() -> bool:
            return restore_defaults_requested["value"] or form_values() != initial_values

        def leave_settings() -> None:
            if has_unsaved_changes() and not self.messagebox.askyesno(
                "Unsaved Settings",
                "You have unsaved settings changes. Leave without saving?",
                parent=self.root,
            ):
                return
            self._build_profile_home()

        back_button.bind("<Button-1>", lambda _event: leave_settings())

        def restore_defaults() -> None:
            if not self.messagebox.askyesno(
                "Restore Defaults",
                "Restore all settings to their default values?",
                parent=self.root,
            ):
                return
            title_var.set(str(DEFAULT_APP_SETTINGS["title_language"]))
            autoplay_var.set(bool(DEFAULT_APP_SETTINGS["menu_autoplay"]))
            song_path_var.set(str(DEFAULT_APP_SETTINGS["song_path"]))
            volume_var.set(int(DEFAULT_APP_SETTINGS["volume"]))
            learn_var.set(int(DEFAULT_APP_SETTINGS["learn_new_ratio"]))
            flagged_var.set(int(DEFAULT_APP_SETTINGS["flagged_ratio"]))
            boundary_var.set(int(DEFAULT_APP_SETTINGS["review_boundary"]))
            review_hard_ratio_var.set(int(DEFAULT_APP_SETTINGS["review_hard_ratio"]))
            restore_defaults_requested["value"] = True
            self.status_var.set("Default settings restored in the form. Press Save to apply them.")

        def apply() -> None:
            hard = max(0, min(100, int(review_hard_ratio_var.get())))
            easy = 100 - hard
            if restore_defaults_requested["value"]:
                self.app_settings.clear()
                self.app_settings.update(DEFAULT_APP_SETTINGS)
            self.app_settings.update({
                "menu_autoplay": bool(autoplay_var.get()),
                "volume": max(0, min(100, int(volume_var.get()))),
                "learn_new_ratio": max(0, min(100, int(learn_var.get()))),
                "learn_existing_ratio": 100 - max(0, min(100, int(learn_var.get()))),
                "flagged_ratio": max(0, min(100, int(flagged_var.get()))),
                "other_ratio": 100 - max(0, min(100, int(flagged_var.get()))),
                "review_boundary": max(0, min(100, int(boundary_var.get()))),
                "review_hard_ratio": hard,
                "review_easy_ratio": easy,
                "title_language": title_var.get(),
                "song_path": _clean(song_path_var.get()),
            })
            self._playable_records_cache_signature = None
            self._playable_records_cache = None
            self._save_app_settings()
            # Apply the new volume immediately to the already-open menu track.
            if getattr(self, "_menu_player_active", False):
                self.menu_player.set_volume(self.app_settings.get("volume", 50))
            self.status_var.set("Settings saved.")
            self._build_profile_home()

        button_row = self.tk.Frame(surface, bg=UI_BACKGROUND)
        button_row.place(x=835, y=650, width=315, height=50)
        self._make_kanon_button(button_row, "Restore Defaults", restore_defaults, width=150, height=36, font_size=9, active_color=UI_PINK_DARK, hover_color=UI_PINK_DARK).pack(side="left", padx=(0, 8))
        self._make_kanon_button(button_row, "Save", apply, width=90, height=36, font_size=10, active_color=UI_PINK_DARK, hover_color=UI_PINK_DARK).pack(side="left")

    def open_song_directory(self, parent: Any = None) -> None:
        """Open the active profile's download folder in the system file browser."""
        parent = parent or self.root
        directory = Path(_clean(self.app_settings.get("song_path")) or _clean(self.output_var.get()) or (Path.cwd() / "downloads")).expanduser()
        try:
            directory.mkdir(parents=True, exist_ok=True)
            if os.name == "nt":
                startfile = getattr(os, "startfile", None)
                if startfile is None:
                    raise OSError("Windows Explorer is unavailable.")
                startfile(str(directory))
            elif sys.platform == "darwin":
                import subprocess
                subprocess.Popen(["open", str(directory)])
            else:
                import subprocess
                subprocess.Popen(["xdg-open", str(directory)])
        except OSError as exc:
            self.messagebox.showerror("Could not open Song Directory", str(exc), parent=parent)

    def _settings_delete_downloads(self, parent: Any) -> None:
        if not self.messagebox.askyesno("Delete all Downloads", "Delete all downloaded songs? This action cannot be undone", parent=parent):
            return
        deleted = self._clear_downloads_everywhere()
        try:
            self.save_profile()
        except Exception:
            pass
        self.status_var.set(f"Deleted {deleted:,} downloaded files and cleared download records.")
        self.messagebox.showinfo("Downloads deleted", f"Deleted {deleted:,} downloaded files.", parent=parent)

    def _settings_delete_profiles(self, parent: Any) -> None:
        if not self.messagebox.askyesno("Delete all Profiles", "Delete all profiles? This action cannot be undone", parent=parent):
            return
        self._delete_all_profiles()
        if parent is not self.root:
            parent.destroy()

    def _settings_clear_history(self, parent: Any) -> None:
        if not self.messagebox.askyesno("Clear Play History", "Clear play history and guess rates for all songs? This action cannot be undone", parent=parent):
            return
        self._clear_play_history_everywhere()
        self.status_var.set("Play history and guess rates were cleared for all profiles.")
        self.messagebox.showinfo("Play history cleared", "Play history and guess rates were cleared for all songs.", parent=parent)

    def _settings_unflag(self, parent: Any) -> None:
        if not self.messagebox.askyesno("Unflag all Flagged Songs", "Unflag all flagged songs? This action cannot be undone", parent=parent):
            return
        count = self._unflag_everywhere()
        self.status_var.set(f"Unflagged {count:,} songs across all profiles.")
        self.messagebox.showinfo("Songs unflagged", f"Unflagged {count:,} songs.", parent=parent)

    def _build_profile_home(self) -> None:
        self._build_main_menu()
        return
        self._clear_content()
        ttk = self.ttk
        frame = ttk.LabelFrame(self.content, text="Profile")
        frame.pack(fill="both", expand=True, padx=10, pady=10)
        ttk.Label(frame, text=f"Current profile: {self.profile_var.get()}", font=("TkDefaultFont", 14, "bold")).pack(anchor="w", padx=18, pady=(24, 8))
        summary = "No list imported yet."
        if self.collection:
            summary = f"{self.collection.source} · {self.collection.total_entries:,} entries · {len(self.download_records):,} saved song records"
        ttk.Label(frame, text=summary).pack(anchor="w", padx=18, pady=4)
        buttons = ttk.Frame(frame)
        buttons.pack(anchor="w", padx=18, pady=22)
        ttk.Button(buttons, text="Select Profile", command=self.select_profile).pack(side="left")
        ttk.Button(buttons, text="New Profile", command=self.new_profile).pack(side="left", padx=8)
        if self.collection:
            ttk.Button(buttons, text="Open Downloads", command=self.open_downloads).pack(side="left", padx=(0, 8))
        ttk.Button(buttons, text="Edit Profile", command=self.edit_profile, state="normal" if self.collection else "disabled").pack(side="left")

    def _stats_tags(self, record: dict[str, Any]) -> list[str]:
        raw_values: list[Any] = []
        for key in ("tags", "songTags", "animeTags", "tag"):
            if key in record:
                raw_values.append(record.get(key))
        tags: list[str] = []
        for raw in raw_values:
            if isinstance(raw, dict):
                tags.extend(_clean(key) for key, enabled in raw.items() if enabled and _clean(key))
            elif isinstance(raw, (list, tuple, set)):
                tags.extend(_clean(value) for value in raw if _clean(value))
            elif _clean(raw):
                tags.extend(part.strip() for part in re.split(r"[,;|]", _clean(raw)) if part.strip())
        return list(dict.fromkeys(tags)) or ["Untagged"]

    def _stats_vintage_range(self, record: dict[str, Any]) -> str:
        match = re.search(r"(?:Winter|Spring|Summer|Fall)\s+(\d{4})", _clean(record.get("animeVintage")), re.IGNORECASE)
        if not match:
            return "Unknown"
        year = int(match.group(1))
        start = year - (year % 5)
        return f"{start}–{start + 4}"

    def _build_stats_page(self) -> None:
        self._clear_content()
        ttk = self.ttk
        frame = ttk.LabelFrame(self.content, text=f"Stats — {self.profile_var.get()}")
        frame.pack(fill="both", expand=True, padx=10, pady=10)
        top = ttk.Frame(frame)
        top.pack(fill="x", padx=10, pady=(10, 4))
        ttk.Label(top, text="Current performance", font=("TkDefaultFont", 14, "bold")).pack(side="left")
        self._make_kanon_button(top, "Back to Profile", self._build_profile_home, width=145, height=34, font_size=9, active_color=UI_PINK_DARK, hover_color=UI_PINK_DARK).pack(side="right")
        ttk.Label(frame, text="Select the fields to use for grouping your performance. All stats shown here belong to the current profile.").pack(anchor="w", padx=10, pady=(0, 8))

        dimensions = (
            ("anime", "Anime"),
            ("song", "Song"),
            ("song_type", "Song Type"),
            ("category", "Song Category"),
        )
        toggle_frame = ttk.LabelFrame(frame, text="Group by")
        toggle_frame.pack(fill="x", padx=10, pady=(0, 8))
        toggle_vars: dict[str, Any] = {}
        for column, (key, label) in enumerate(dimensions):
            toggle_vars[key] = self.tk.BooleanVar(value=True)
            ttk.Checkbutton(toggle_frame, text=label, variable=toggle_vars[key], command=lambda: render()).grid(row=0, column=column, sticky="w", padx=(8, 12), pady=7)
        ttk.Label(toggle_frame, text="Search:").grid(row=0, column=len(dimensions), sticky="e", padx=(12, 4), pady=7)
        search_var = self.tk.StringVar()
        search_entry = ttk.Entry(toggle_frame, textvariable=search_var, width=28)
        search_entry.grid(row=0, column=len(dimensions) + 1, sticky="ew", padx=(0, 8), pady=7)
        toggle_frame.columnconfigure(len(dimensions) + 1, weight=1)

        table_frame = ttk.Frame(frame)
        table_frame.pack(fill="both", expand=True, padx=10)
        dimension_columns = [key for key, _label in dimensions]
        all_columns = ["group", *dimension_columns, "songs", "encounters", "correct", "wrong", "rate", "flagged"]
        headings = {
            "group": "Group", "anime": "Anime", "song": "Song", "song_type": "Song Type",
            "category": "Song Category",
            "songs": "Songs", "encounters": "Encounters", "correct": "Correct",
            "wrong": "Incorrect", "rate": "GR%", "flagged": "Flagged",
        }
        tree = ttk.Treeview(table_frame, columns=all_columns, show="headings")
        numeric_columns = {"songs", "encounters", "correct", "wrong", "rate", "flagged"}
        sort_column = "group"
        sort_descending = False
        row_record_ids: dict[str, set[str]] = {}
        def sort_by(column: str) -> None:
            nonlocal sort_column, sort_descending
            if sort_column == column:
                sort_descending = not sort_descending
            else:
                sort_column = column
                sort_descending = column in numeric_columns
            render()
        for column in all_columns:
            tree.heading(column, text=headings[column], command=lambda selected_column=column: sort_by(selected_column))
            width = {"group": 180, "anime": 185, "song": 205, "song_type": 100, "category": 110, "songs": 58, "encounters": 78, "correct": 65, "wrong": 70, "rate": 58, "flagged": 60}.get(column, 80)
            tree.column(column, width=width, minwidth=width, stretch=False, anchor="w" if column in dimension_columns or column == "group" else "center")
        scrollbar = ttk.Scrollbar(table_frame, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=scrollbar.set)
        tree.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        summary_var = self.tk.StringVar()
        ttk.Label(frame, textvariable=summary_var, anchor="w").pack(fill="x", padx=10, pady=7)

        def render() -> None:
            records = self._playable_records()
            active = [key for key, _label in dimensions if toggle_vars[key].get()]
            if active:
                tree.configure(displaycolumns=[*active, "songs", "encounters", "correct", "wrong", "rate", "flagged"])
            else:
                tree.configure(displaycolumns=["group", "songs", "encounters", "correct", "wrong", "rate", "flagged"])
            for item in tree.get_children(""):
                tree.delete(item)
            row_record_ids.clear()
            aggregates: dict[tuple[str, ...], dict[str, Any]] = {}
            total_encounters = total_correct = total_wrong = 0
            total_songs_played = 0
            total_songs_learned = 0
            for record in records:
                dimensions_for_record: dict[str, list[str]] = {
                    "anime": [self._display_title(record)],
                    "song": [_first_nonempty(record.get("songName"), "Unknown song")],
                    "song_type": [_first_nonempty(record.get("songType"), "Unknown")],
                    "category": [_first_nonempty(record.get("songCategory"), "Unknown")],
                }
                group_values = [dimensions_for_record[key] for key in active]
                if not group_values:
                    group_values = [["Overall"]]
                stats = self.play_stats.get(_record_key(record), {})
                encounters = int(stats.get("encounters", 0) or 0)
                correct = int(stats.get("correct", 0) or 0)
                wrong = int(stats.get("wrong", 0) or 0)
                total_encounters += encounters
                total_correct += correct
                total_wrong += wrong
                if encounters > 0:
                    total_songs_played += 1
                    if (100.0 * correct / encounters) > 75.0:
                        total_songs_learned += 1
                for combination in product(*group_values):
                    aggregate = aggregates.setdefault(tuple(combination), {"song_ids": set(), "encounters": 0, "correct": 0, "wrong": 0, "flagged": 0})
                    record_id = _record_key(record)
                    if record_id in aggregate["song_ids"]:
                        continue
                    aggregate["song_ids"].add(record_id)
                    aggregate["encounters"] += encounters
                    aggregate["correct"] += correct
                    aggregate["wrong"] += wrong
                    aggregate["flagged"] += 1 if stats.get("flagged") else 0
            rows: list[dict[str, Any]] = []
            for combination, aggregate in aggregates.items():
                encounter_count = aggregate["encounters"]
                correct_count = aggregate["correct"]
                rate_value = (100.0 * correct_count / encounter_count) if encounter_count else 0.0
                rate = f"{rate_value:.1f}%" if encounter_count else "—"
                dimension_values = {key: "" for key in dimension_columns}
                for key, value in zip(active, combination):
                    dimension_values[key] = value
                group_label = " · ".join(combination)
                search_blob = " ".join((group_label, *dimension_values.values())).casefold()
                if _search_clean(search_var.get()) and _search_clean(search_var.get()) not in _search_clean(search_blob):
                    continue
                row_values = (group_label, *[dimension_values[key] for key in dimension_columns], len(aggregate["song_ids"]), encounter_count, correct_count, aggregate["wrong"], rate, "⚑" if aggregate["flagged"] else "⚐")
                rows.append({
                    "values": row_values,
                    "record_ids": set(aggregate["song_ids"]),
                    "sort": {
                        "group": group_label.casefold(),
                        **{key: dimension_values[key].casefold() for key in dimension_columns},
                        "songs": len(aggregate["song_ids"]),
                        "encounters": encounter_count,
                        "correct": correct_count,
                        "wrong": aggregate["wrong"],
                        "rate": rate_value,
                        "flagged": aggregate["flagged"],
                    },
                })
            rows.sort(key=lambda row: row["sort"].get(sort_column, ""), reverse=sort_descending)
            for row in rows:
                item = tree.insert("", "end", values=row["values"])
                row_record_ids[item] = row["record_ids"]
            overall_rate = f"{100.0 * total_correct / total_encounters:.1f}%" if total_encounters else "—"
            summary_var.set(f"Total Songs Played: {total_songs_played:,} · Total Songs Learned (>75%): {total_songs_learned:,} · {total_encounters:,} encounters · {total_correct:,} correct · {total_wrong:,} incorrect · Overall guess rate: {overall_rate}")

        def toggle_stats_flag(event: Any) -> str | None:
            if tree.identify_region(event.x, event.y) != "cell":
                return None
            display_columns = list(tree.cget("displaycolumns"))
            if display_columns == ["#all"]:
                display_columns = list(all_columns)
            try:
                flagged_column_index = display_columns.index("flagged") + 1
            except ValueError:
                return None
            if tree.identify_column(event.x) != f"#{flagged_column_index}":
                return None
            item = tree.identify_row(event.y)
            record_ids = row_record_ids.get(item)
            if not record_ids:
                return None
            new_value = not all(bool(self.play_stats.get(key, {}).get("flagged")) for key in record_ids)
            for key in record_ids:
                stats = self.play_stats.setdefault(key, {"encounters": 0, "correct": 0, "wrong": 0, "flagged": False})
                stats["flagged"] = new_value
            self.save_profile()
            render()
            return "break"

        tree.bind("<Button-1>", toggle_stats_flag, add="+")
        search_var.trace_add("write", lambda *_args: render())

        summary_var.set("Loading statistics…")
        frame.after(40, lambda: render() if frame.winfo_exists() else None)

    def _build_play_home(self) -> None:
        """Show Play mode selection in the main 1280x720 application page."""
        self._clear_content()
        self._resume_menu_player_if_allowed()
        surface = self.tk.Frame(self.content, bg=UI_BACKGROUND)
        surface.pack(fill="both", expand=True)
        canvas = self.tk.Canvas(surface, bg=UI_BACKGROUND, highlightthickness=0)
        canvas.place(x=0, y=0, relwidth=1, relheight=1)
        canvas.create_image(0, 0, anchor="nw", image=self._ui_background(), tags=("background",))
        canvas.create_image(25, 22, anchor="nw", image=self._ui_image("Elements/back-button.png"), tags=("play-back-arrow",))
        canvas.create_text(640, 78, text="Play", fill=UI_TEXT, font=(self._ui_font_family, 24, "bold"), tags=("play-title",))
        canvas.create_text(640, 185, text="Choose a training mode", fill=UI_TEXT, font=(self._ui_font_family, 24, "bold"))
        count_item = canvas.create_text(640, 225, text="Playable downloaded songs: loading…", fill=UI_MUTED, font=(self._ui_font_family, 13))

        def dispatch_back_click(event: Any) -> Any:
            # Keep the arrow artwork transparent while making its full upper-left
            # interaction area easy to hit, including transparent pixels.
            if 0 <= event.x <= 180 and 0 <= event.y <= 185:
                self._build_profile_home()
                return "break"
            return None

        canvas.bind("<Button-1>", dispatch_back_click)
        normal = self._ui_images.setdefault("play-button-normal-1280", self._ui_image("Elements/Main Menu/button.png").zoom(2, 2).subsample(3, 3))
        hover = self._ui_images.setdefault("play-button-hover-1280", self._ui_image("Elements/Main Menu/button-hover.png").zoom(2, 2).subsample(3, 3))
        modes = ("Random", "Learn", "Review", "Flagged")
        start_x, y, gap = 136, 370, 20
        for index, mode in enumerate(modes):
            x = start_x + index * (237 + gap)
            tag = f"play-mode-{index}"
            bg = canvas.create_image(x, y, anchor="nw", image=normal, tags=(tag,))
            canvas.create_text(x + 118, y + 42, text=mode, fill=UI_TEXT, font=(self._ui_font_family, 18), tags=(tag,))
            canvas.tag_bind(tag, "<Enter>", lambda _event, item=bg: canvas.itemconfigure(item, image=hover))
            canvas.tag_bind(tag, "<Leave>", lambda _event, item=bg: canvas.itemconfigure(item, image=normal))
            def dispatch_play_click(event: Any, expected_tag: str = tag, selected_mode: str = mode) -> Any:
                if expected_tag in canvas.gettags("current"):
                    self._open_session_settings(selected_mode)
                    return "break"
                return None
            canvas.bind("<Button-1>", dispatch_play_click, add="+")
        canvas.create_text(640, 650, text="Songs are selected from this profile's downloaded files. Session history is saved locally.", fill=UI_TEXT, font=(self._ui_font_family, 12))

        def update_playable_count() -> None:
            if not canvas.winfo_exists():
                return
            records = self._playable_records()
            canvas.itemconfigure(count_item, text=f"Playable downloaded songs: {len(records):,}")
            self.library.refresh_async()

        surface.after(40, update_playable_count)

    def _playable_records(self) -> list[dict[str, Any]]:
        membership = self._profile_membership_index()
        membership_signature = self._profile_membership_cache[0] if self._profile_membership_cache else None
        collection_song_count = len(self.collection.songs) if self.collection else 0
        signature = (
            id(self.collection),
            len(self.download_records),
            collection_song_count,
            tuple(sorted(self.enabled_lists)),
            membership_signature,
            self.current_manifest_path,
            _clean(self.app_settings.get("song_path")),
            _clean(self.output_var.get()),
        )
        if self._playable_records_cache_signature == signature and self._playable_records_cache is not None:
            return self._playable_records_cache

        records: list[dict[str, Any]] = []
        for record in self.download_records:
            if not self._record_enabled_for_profile(record, membership):
                continue
            path = self._resolved_download_path(record)
            try:
                if path and Path(path).exists() and Path(path).stat().st_size > 0:
                    playable = record if path == _clean(record.get("download_path")) else {**record, "download_path": path}
                    records.append(playable)
            except OSError:
                continue
        if not records and _collection_has_embedded_songs(self.collection):
            for record in self.collection.songs:
                if not self._record_enabled_for_profile(record, membership):
                    continue
                path = self._resolved_download_path(record)
                if path and Path(path).exists() and Path(path).stat().st_size > 0:
                    playable = record if path == _clean(record.get("download_path")) else {**record, "download_path": path}
                    records.append(playable)
        self._playable_records_cache_signature = signature
        self._playable_records_cache = records
        return records

    def _resolved_download_path(self, record: dict[str, Any]) -> str:
        """Resolve stored media paths against the user-selected song folder."""
        stored = _clean(record.get("download_path"))
        candidates: list[Path] = []
        if stored:
            candidates.append(Path(stored).expanduser())
        song_root = _clean(self.app_settings.get("song_path")) or _clean(self.output_var.get())
        if song_root and stored:
            candidates.append(Path(song_root).expanduser() / Path(stored).name)
        for candidate in candidates:
            try:
                if candidate.is_file() and candidate.stat().st_size > 0:
                    return str(candidate)
            except OSError:
                continue
        return stored

    def _profile_membership_index(self) -> tuple[set[str], set[str]]:
        """Build one fast membership index for all currently enabled lists."""
        if not self.collection or not self.enabled_lists:
            return set(), set()
        signature = (
            id(self.collection),
            tuple(sorted(self.enabled_lists)),
            tuple((name, len(self.collection.buckets[name].entries)) for name in sorted(self.enabled_lists) if name in self.collection.buckets),
        )
        if self._profile_membership_cache and self._profile_membership_cache[0] == signature:
            return self._profile_membership_cache[1], self._profile_membership_cache[2]
        entry_keys: set[str] = set()
        entry_titles: set[str] = set()

        def title_key(value: Any) -> str:
            return re.sub(r"[^a-z0-9]+", "", _clean(value).casefold())

        for name in self.enabled_lists:
            bucket = self.collection.buckets.get(name)
            if not bucket:
                continue
            for entry in bucket.entries:
                entry_keys.add(entry.key)
                entry_titles.update(
                    key for key in (
                        title_key(entry.title),
                        title_key(entry.extra.get("title_english")),
                        title_key(entry.extra.get("title_romaji")),
                        title_key(entry.extra.get("title_native")),
                    ) if key
                )
        self._profile_membership_cache = (signature, entry_keys, entry_titles)
        return entry_keys, entry_titles

    def _record_enabled_for_profile(self, record: dict[str, Any], membership: Optional[tuple[set[str], set[str]]] = None) -> bool:
        """Return whether a song belongs to one of this profile's enabled lists."""
        if not self.collection:
            return True
        if not self.enabled_lists:
            return False
        entry_keys, entry_titles = membership or self._profile_membership_index()
        linked = record.get("linked_ids") or {}
        record_keys = {
            f"anilist:{linked.get('anilist')}",
            f"mal:{linked.get('myanimelist')}",
            f"source:AMQ:{linked.get('ann')}",
        }
        if record_keys.intersection(entry_keys):
            return True
        def title_key(value: Any) -> str:
            return re.sub(r"[^a-z0-9]+", "", _clean(value).casefold())
        record_titles = {
            key for key in (
                title_key(record.get("animeENName")),
                title_key(record.get("animeJPName")),
                *(title_key(value) for value in _clean(record.get("animeAltName")).split(",")),
            ) if key
        }
        return bool(record_titles.intersection(entry_titles))

    def _record_matches_bucket(self, record: dict[str, Any], bucket: ListBucket) -> bool:
        """Match a song to an imported list using IDs first and titles second."""
        if self._record_matches_bucket_ids(record, bucket):
            return True

        def title_key(value: Any) -> str:
            return re.sub(r"[^a-z0-9]+", "", _clean(value).casefold())

        record_titles = {
            title_key(record.get("animeENName")),
            title_key(record.get("animeJPName")),
            *(title_key(value) for value in _clean(record.get("animeAltName")).split(",")),
        }
        record_titles.discard("")
        for entry in bucket.entries:
            entry_titles = {
                title_key(entry.title),
                title_key(entry.extra.get("title_english")),
                title_key(entry.extra.get("title_romaji")),
                title_key(entry.extra.get("title_native")),
            }
            entry_titles.discard("")
            if record_titles.intersection(entry_titles):
                return True
        return False

    def _record_matches_bucket_ids(self, record: dict[str, Any], bucket: ListBucket) -> bool:
        """Fast list membership check used while constructing Edit Profile."""
        linked = record.get("linked_ids") or {}
        record_keys = {
            f"anilist:{linked.get('anilist')}",
            f"mal:{linked.get('myanimelist')}",
            f"source:AMQ:{linked.get('ann')}",
        }
        entry_keys = {entry.key for entry in bucket.entries}
        return bool(entry_keys.intersection(record_keys))

    def _bucket_has_downloads(self, bucket: ListBucket) -> bool:
        """Whether a list currently has at least one usable downloaded file."""
        for record in self._profile_song_records():
            path_text = _clean(record.get("download_path"))
            if not path_text:
                continue
            if not self._record_matches_bucket_ids(record, bucket):
                continue
            try:
                if Path(path_text).is_file() and Path(path_text).stat().st_size > 0:
                    return True
            except OSError:
                continue
        return False

    def _open_session_settings(self, mode: str) -> None:
        records = self._playable_records()
        if not records:
            self.messagebox.showinfo("No downloaded songs", "Download songs for this profile before starting a play session.", parent=self.root)
            return
        if not self.library.index.records:
            fallback = LibraryIndex.from_song_records(records)
            self.library.index = fallback
        self._clear_content()
        surface = self.tk.Frame(self.content, bg=UI_BACKGROUND)
        surface.pack(fill="both", expand=True)
        self.tk.Label(surface, text=f"Session Settings — {mode}", bg=UI_BACKGROUND, fg=UI_TEXT, font=(self._ui_font_family, 24, "bold")).place(relx=0.5, y=78, anchor="center")
        scroll_host = self.tk.Frame(surface, bg=UI_BACKGROUND)
        scroll_host.place(x=140, y=126, width=1000, height=495)
        scroll_canvas = self.tk.Canvas(scroll_host, bg=UI_BACKGROUND, highlightthickness=0)
        scroll_bar = self.ttk.Scrollbar(scroll_host, orient="vertical", command=scroll_canvas.yview)
        scroll_canvas.configure(yscrollcommand=scroll_bar.set)
        scroll_canvas.pack(side="left", fill="both", expand=True)
        body = self.tk.Frame(scroll_canvas, bg=UI_BACKGROUND)
        body_window = scroll_canvas.create_window((0, 0), window=body, anchor="nw")
        body.bind("<Configure>", lambda _event: scroll_canvas.configure(scrollregion=scroll_canvas.bbox("all")))
        scroll_canvas.bind("<Configure>", lambda event: scroll_canvas.itemconfigure(body_window, width=event.width))

        controls = self.tk.Frame(body, bg=UI_BACKGROUND)
        controls.pack(anchor="center")

        def on_mousewheel(event: Any) -> str:
            delta = int(event.delta / 120) if event.delta else 0
            if not delta:
                delta = 1 if event.delta < 0 else -1
            scroll_canvas.yview_scroll(-delta, "units")
            return "break"

        surface.bind_all("<MouseWheel>", on_mousewheel)

        def back_to_play() -> None:
            surface.unbind_all("<MouseWheel>")
            self._build_play_home()

        back_area = self.tk.Frame(surface, bg=UI_BACKGROUND, cursor=self._app_cursor)
        back_area.place(x=0, y=0, width=160, height=185)
        back = self.tk.Label(back_area, image=self._ui_image("Elements/back-button.png"), bg=UI_BACKGROUND, cursor=self._app_cursor)
        back.place(x=25, y=22)
        back_area.bind("<Button-1>", lambda _event: back_to_play())
        back.bind("<Button-1>", lambda _event: back_to_play())
        back_area.lift()
        fields: dict[str, Any] = {}

        basic = self.tk.Frame(controls, bg=UI_BACKGROUND)
        basic.pack(anchor="center", pady=(0, 10))
        def entry_row(parent: Any, row: int, label: str, key: str, value: str, width: int = 10) -> Any:
            row_frame = self.tk.Frame(parent, bg=UI_BACKGROUND)
            row_frame.pack(anchor="center", pady=5)
            self.tk.Label(row_frame, text=label, width=24, anchor="e", bg=UI_BACKGROUND, fg=UI_TEXT, font=(self._ui_font_family, 11)).pack(side="left", padx=(0, 12))
            variable = self.tk.StringVar(value=value)
            fields[key] = variable
            self.tk.Entry(row_frame, textvariable=variable, width=width, bg=UI_PANEL_DARK, fg=UI_TEXT, insertbackground=UI_TEXT, relief="flat").pack(side="left")
            return variable
        entry_row(basic, 0, "No. of Songs", "count", str(self.app_settings.get("session_count", 20)))
        entry_row(basic, 1, "Guess Time (seconds)", "guess_time", str(self.app_settings.get("session_guess_time", 20)))
        entry_row(basic, 2, "Autoskip Time (seconds)", "autoskip_seconds", str(self.app_settings.get("session_autoskip_seconds", 1)))

        year_min = self.tk.IntVar(value=int(self.app_settings.get("session_year_min", 1924)))
        year_max = self.tk.IntVar(value=min(dt.datetime.now().year, int(self.app_settings.get("session_year_max", dt.datetime.now().year))))
        custom_percent = self.tk.IntVar(value=int(self.app_settings.get("session_custom_percent", 50)))
        difficulty_min = self.tk.IntVar(value=int(self.app_settings.get("session_difficulty_min", 0)))
        difficulty_max = self.tk.IntVar(value=int(self.app_settings.get("session_difficulty_max", 100)))
        fields.update({"year_min": year_min, "year_max": year_max, "custom_percent": custom_percent, "difficulty_min": difficulty_min, "difficulty_max": difficulty_max})
        self._make_ui_range_slider(controls, "Year Range", year_min, year_max, 1924, dt.datetime.now().year, center=True)
        self._make_ui_range_slider(controls, "Local Guess Rate", difficulty_min, difficulty_max, 0, 100, suffix="%", center=True)
        custom_sample_frame = self._make_ui_slider(controls, "Custom Sample", custom_percent, center=True)

        options = self.tk.Frame(controls, bg=UI_BACKGROUND)
        options.pack(fill="x", pady=(0, 12))
        self.tk.Label(options, text="Sample Point", bg=UI_BACKGROUND, fg=UI_TEXT, font=(self._ui_font_family, 12, "bold")).pack(fill="x", pady=(0, 2))
        fields["sample_point"] = self.tk.StringVar(value=self.app_settings.get("session_sample_point", "Random"))
        sample_menu = self.tk.OptionMenu(options, fields["sample_point"], "Start", "End", "Random", "Custom (%)")
        sample_menu.configure(bg=UI_PANEL, fg=UI_TEXT, activebackground=UI_PINK, activeforeground=UI_TEXT, highlightthickness=0, relief="flat", bd=0, width=14, font=(self._ui_font_family, 11))
        sample_menu["menu"].configure(bg=UI_PANEL_DARK, fg=UI_TEXT, activebackground=UI_PINK, activeforeground=UI_TEXT, font=(self._ui_font_family, 11))
        sample_menu.pack(anchor="center", pady=(3, 12))

        def refresh_custom_sample_state(*_args: Any) -> None:
            custom_sample_frame.set_enabled(fields["sample_point"].get() == "Custom (%)")

        fields["sample_point"].trace_add("write", refresh_custom_sample_state)
        refresh_custom_sample_state()

        self.tk.Label(options, text="Song Type", bg=UI_BACKGROUND, fg=UI_TEXT, font=(self._ui_font_family, 12, "bold")).pack(fill="x")
        type_frame = self.tk.Frame(options, bg=UI_BACKGROUND)
        type_frame.pack(anchor="center", pady=(3, 10))

        def add_toggle_button(parent: Any, label: str, variable: Any, width: int, padx: int) -> Any:
            button = self._make_kanon_button(
                parent,
                label,
                lambda: variable.set(not variable.get()),
                width=width,
                height=35,
                font_size=9,
            )
            button.pack(side="left", padx=(0, padx))
            variable.trace_add("write", lambda *_args: button._render_kanon_state(bool(variable.get())))
            button._render_kanon_state(bool(variable.get()))
            return button

        for label, key in (("OP", "opening"), ("ED", "ending"), ("IN", "insert")):
            variable = self.tk.BooleanVar(value=bool(self.app_settings.get(f"session_{key}", True)))
            fields[key] = variable
            add_toggle_button(type_frame, label, variable, 64, 12)
        self.tk.Label(options, text="Song Category", bg=UI_BACKGROUND, fg=UI_TEXT, font=(self._ui_font_family, 12, "bold")).pack(fill="x")
        category_frame = self.tk.Frame(options, bg=UI_BACKGROUND)
        category_frame.pack(anchor="center", pady=(3, 10))
        for label, key in (("Standard", "standard"), ("Character", "character"), ("Chanting", "chanting"), ("Instrumental", "instrumental"), ("Other", "other")):
            variable = self.tk.BooleanVar(value=bool(self.app_settings.get(f"session_{key}", True)))
            fields[key] = variable
            add_toggle_button(category_frame, label, variable, max(88, len(label) * 8 + 32), 8)
        for label, key, setting_key, default in (("Duplicate Shows", "duplicate", "session_duplicate", False), ("Rebroadcast Songs", "rebroadcast", "session_rebroadcast", True), ("Dub Songs", "dub", "session_dub", False), ("Autoskip", "autoskip", "session_autoskip", True)):
            fields[key] = self.tk.BooleanVar(value=bool(self.app_settings.get(setting_key, default)))
            add_toggle_button(options, label, fields[key], max(150, len(label) * 8 + 32), 8)
        if mode == "Random":
            fields["completely_random"] = self.tk.BooleanVar(value=bool(self.app_settings.get("session_completely_random", False)))
            add_toggle_button(options, "Completely Random Song Selection", fields["completely_random"], 270, 8)

        def restore_defaults() -> None:
            if not self.messagebox.askyesno(
                "Restore Defaults",
                "Restore all Session Settings to their default values?",
                parent=self.root,
            ):
                return
            fields["count"].set(str(DEFAULT_APP_SETTINGS["session_count"]))
            fields["guess_time"].set(str(DEFAULT_APP_SETTINGS["session_guess_time"]))
            fields["autoskip_seconds"].set(str(DEFAULT_APP_SETTINGS["session_autoskip_seconds"]))
            year_min.set(int(DEFAULT_APP_SETTINGS["session_year_min"]))
            year_max.set(min(dt.datetime.now().year, int(DEFAULT_APP_SETTINGS["session_year_max"])))
            custom_percent.set(int(DEFAULT_APP_SETTINGS["session_custom_percent"]))
            difficulty_min.set(int(DEFAULT_APP_SETTINGS["session_difficulty_min"]))
            difficulty_max.set(int(DEFAULT_APP_SETTINGS["session_difficulty_max"]))
            fields["sample_point"].set(str(DEFAULT_APP_SETTINGS["session_sample_point"]))
            for key in ("opening", "ending", "insert", "standard", "character", "chanting", "instrumental", "other", "duplicate", "rebroadcast", "dub", "autoskip"):
                fields[key].set(bool(DEFAULT_APP_SETTINGS[f"session_{key}"]))
            if "completely_random" in fields:
                fields["completely_random"].set(bool(DEFAULT_APP_SETTINGS["session_completely_random"]))

        def begin() -> None:
            try:
                settings = {
                    "count": max(1, int(fields["count"].get())),
                    "year_min": max(1924, int(fields["year_min"].get())),
                    "year_max": min(dt.datetime.now().year, int(fields["year_max"].get())),
                    "guess_time": max(1, int(fields["guess_time"].get())),
                    "custom_percent": max(0.0, min(100.0, float(fields["custom_percent"].get()))),
                    "sample_point": fields["sample_point"].get(),
                    "difficulty_min": max(0.0, min(100.0, float(fields["difficulty_min"].get()))),
                    "difficulty_max": max(0.0, min(100.0, float(fields["difficulty_max"].get()))),
                    "types": [key for key in ("opening", "ending", "insert") if fields[key].get()],
                    "categories": [key for key in ("standard", "character", "chanting", "instrumental", "other") if fields[key].get()],
                    "duplicate": fields["duplicate"].get(),
                    "rebroadcast": fields["rebroadcast"].get(),
                    "dub": fields["dub"].get(),
                    "autoskip": fields["autoskip"].get(),
                    "autoskip_seconds": max(0, int(fields["autoskip_seconds"].get())),
                    "completely_random": bool(fields["completely_random"].get()) if "completely_random" in fields else bool(self.app_settings.get("session_completely_random", False)),
                }
                if settings["year_min"] > settings["year_max"] or settings["difficulty_min"] > settings["difficulty_max"] or not settings["types"] or not settings["categories"]:
                    raise ValueError("Check the year, difficulty, song type, and category ranges.")
            except ValueError as exc:
                self.messagebox.showwarning("Invalid session settings", str(exc), parent=self.root)
                return
            self.app_settings.update({
                "session_count": settings["count"],
                "session_guess_time": settings["guess_time"],
                "session_autoskip_seconds": settings["autoskip_seconds"],
                "session_year_min": settings["year_min"],
                "session_year_max": settings["year_max"],
                "session_custom_percent": int(settings["custom_percent"]),
                "session_difficulty_min": int(settings["difficulty_min"]),
                "session_difficulty_max": int(settings["difficulty_max"]),
                "session_sample_point": settings["sample_point"],
                "session_opening": "opening" in settings["types"],
                "session_ending": "ending" in settings["types"],
                "session_insert": "insert" in settings["types"],
                "session_standard": "standard" in settings["categories"],
                "session_character": "character" in settings["categories"],
                "session_chanting": "chanting" in settings["categories"],
                "session_instrumental": "instrumental" in settings["categories"],
                "session_other": "other" in settings["categories"],
                "session_duplicate": settings["duplicate"],
                "session_rebroadcast": settings["rebroadcast"],
                "session_dub": settings["dub"],
                "session_autoskip": settings["autoskip"],
                "session_completely_random": bool(settings.get("completely_random", False)),
            })
            self._save_app_settings()
            surface.unbind_all("<MouseWheel>")
            self._build_play_home()
            self._begin_play_session(mode, settings)
        button_row = self.tk.Frame(surface, bg=UI_BACKGROUND)
        button_row.place(x=865, y=650, width=285, height=50)
        self._make_kanon_button(button_row, "Restore Defaults", restore_defaults, width=150, height=36, font_size=9, active_color=UI_PINK_DARK, hover_color=UI_PINK_DARK).pack(side="left", padx=(0, 8))
        self._make_kanon_button(button_row, "Start", begin, width=90, height=36, font_size=10, active_color=UI_PINK_DARK, hover_color=UI_PINK_DARK).pack(side="left")

    def _session_candidates(self, settings: dict[str, Any]) -> list[dict[str, Any]]:
        candidates: list[dict[str, Any]] = []
        for record in self._playable_records():
            if _record_key(record) in self.excluded_song_keys:
                continue
            song_type = _clean(record.get("songType")).casefold()
            type_key = next((key for key in ("opening", "ending", "insert") if song_type.startswith(key)), "other")
            if type_key not in settings["types"]:
                continue
            category = _clean(record.get("songCategory") or "standard").casefold()
            if category not in settings["categories"]:
                continue
            vintage = re.search(r"(?:Winter|Spring|Summer|Fall)\s+(\d{4})", _clean(record.get("animeVintage")), re.IGNORECASE)
            if vintage and not settings["year_min"] <= int(vintage.group(1)) <= settings["year_max"]:
                continue
            if not settings["rebroadcast"] and _record_flag(record, "rebroadcast"):
                continue
            if not settings["dub"] and _record_flag(record, "dub"):
                continue
            rate = _record_guess_rate(self.play_stats.get(_record_key(record), {}))
            if not settings["difficulty_min"] <= rate <= settings["difficulty_max"]:
                continue
            candidates.append(record)
        return candidates

    def _anime_key(self, record: dict[str, Any]) -> str:
        linked = record.get("linked_ids") or {}
        return _clean(linked.get("anilist") or linked.get("myanimelist") or record.get("annId") or record.get("animeENName") or record.get("animeJPName"))

    def _session_capacity(self, mode: str, candidates: list[dict[str, Any]], settings: dict[str, Any]) -> int:
        """Return the number of songs this mode can actually play.

        Duplicate Shows changes the capacity from one song per anime to one
        song per downloaded record. Flagged mode can be narrower still when
        its configured ratio is 100:0, because unflagged songs are then not
        eligible fallback choices.
        """
        eligible = candidates
        if mode == "Flagged" and float(self.app_settings.get("other_ratio", 0)) <= 0:
            eligible = [record for record in candidates if self.play_stats.get(_record_key(record), {}).get("flagged")]
        if mode == "Random" and settings.get("completely_random"):
            return len({_record_key(record) for record in eligible})
        if settings.get("duplicate"):
            return len({_record_key(record) for record in eligible})
        return len({self._anime_key(record) for record in eligible})

    def _select_play_songs(self, mode: str, candidates: list[dict[str, Any]], settings: dict[str, Any]) -> list[dict[str, Any]]:
        count = min(settings["count"], len(candidates))
        if not count:
            return []
        duplicate = settings["duplicate"]
        def choose(pool: list[dict[str, Any]], amount: int, already: Optional[set[str]] = None) -> list[dict[str, Any]]:
            already = already or set()
            available = [record for record in pool if _record_key(record) not in {_record_key(item) for item in result} and (duplicate or self._anime_key(record) not in {self._anime_key(item) for item in result}) and _record_key(record) not in already]
            random.shuffle(available)
            return available[:amount]
        result: list[dict[str, Any]] = []
        if mode == "Flagged":
            flagged = [record for record in candidates if self.play_stats.get(_record_key(record), {}).get("flagged")]
            other = [record for record in candidates if record not in flagged]
            flagged_count = round(count * float(self.app_settings.get("flagged_ratio", 100)) / 100.0)
            other_count = count - flagged_count
            result.extend(choose(flagged, flagged_count))
            if other_count and float(self.app_settings.get("other_ratio", 0)) > 0:
                result.extend(choose(other, other_count))
            # If a requested group does not contain enough songs, fill from
            # the other group only when that group is enabled by its ratio.
            if len(result) < count and float(self.app_settings.get("other_ratio", 0)) > 0:
                result.extend(choose(other, count - len(result)))
        elif mode == "Random":
            if settings.get("completely_random"):
                result = list(candidates)
                random.shuffle(result)
                return result[:count]
            by_anime: dict[str, list[dict[str, Any]]] = {}
            for record in candidates:
                by_anime.setdefault(self._anime_key(record), []).append(record)
            anime_keys = list(by_anime)
            while len(result) < count and anime_keys:
                anime = random.choice(anime_keys)
                type_groups: dict[str, list[dict[str, Any]]] = {}
                for record in by_anime[anime]:
                    type_groups.setdefault(_clean(record.get("songType")).split(" ")[0].casefold(), []).append(record)
                type_pool = random.choice(list(type_groups.values()))
                result.append(random.choice(type_pool))
                if not duplicate:
                    anime_keys.remove(anime)
                else:
                    by_anime[anime].remove(result[-1])
                    if not by_anime[anime]:
                        anime_keys.remove(anime)
        elif mode == "Learn":
            unencountered = [record for record in candidates if int(self.play_stats.get(_record_key(record), {}).get("encounters", 0) or 0) == 0]
            encountered = sorted([record for record in candidates if record not in unencountered], key=lambda record: int(self.play_stats.get(_record_key(record), {}).get("encounters", 0) or 0))
            new_count = round(count * float(self.app_settings.get("learn_new_ratio", 50)) / 100.0)
            result.extend(choose(unencountered, min(new_count, len(unencountered))))
            result.extend(choose(encountered, count - len(result)))
            if len(result) < count:
                result.extend(choose(candidates, count - len(result)))
        elif mode == "Review":
            boundary = float(self.app_settings.get("review_boundary", 50))
            low = [record for record in candidates if _record_guess_rate(self.play_stats.get(_record_key(record), {})) <= boundary]
            high = [record for record in candidates if _record_guess_rate(self.play_stats.get(_record_key(record), {})) >= boundary]
            random.shuffle(low)
            random.shuffle(high)
            hard_count = round(count * float(self.app_settings.get("review_hard_ratio", 80)) / 100.0)
            result.extend(choose(low, min(hard_count, len(low))))
            result.extend(choose(high, count - len(result)))
            if len(result) < count:
                result.extend(choose(candidates, count - len(result)))
        random.shuffle(result)
        return result[:count]

    def _begin_play_session(self, mode: str, settings: dict[str, Any]) -> None:
        candidates = self._session_candidates(settings)
        requested_count = max(1, int(settings.get("count", 1)))
        capacity = self._session_capacity(mode, candidates, settings)
        if not capacity:
            self.messagebox.showinfo("No matching songs", "No downloaded songs match these session settings.", parent=self.root)
            return
        # Keep the user's requested count in persistent settings, but cap this
        # session to what can actually be selected. This also prevents the
        # mode-specific duplicate/ratio rules from creating an overlong or
        # partially empty session.
        settings = dict(settings)
        settings["count"] = min(requested_count, capacity)
        songs = self._select_play_songs(mode, candidates, settings)
        # Some ratio-based modes can have a smaller practical pool than the
        # broad capacity calculation. Use the resulting list as the final
        # session size so the last song ends the game normally.
        if songs and len(songs) < settings["count"]:
            settings["count"] = len(songs)
        if not songs:
            self.messagebox.showinfo("No matching songs", "No downloaded songs match these session settings.", parent=self.root)
            return
        if settings["count"] < requested_count:
            self.status_var.set(f"Only {settings['count']:,} eligible songs found; session limited to that amount.")
        self._show_play_session(mode, settings, songs)

    def _show_play_session(self, mode: str, settings: dict[str, Any], songs: list[dict[str, Any]]) -> None:
        self._suspend_menu_player()
        self._clear_content()
        surface = self.tk.Frame(self.content, bg=UI_BACKGROUND)
        surface.pack(fill="both", expand=True)
        dialog = self.tk.Frame(surface, bg=UI_BACKGROUND, highlightthickness=2, highlightbackground=UI_PINK, highlightcolor=UI_PINK)
        dialog.place(x=25, y=34, width=1230, height=650)
        main = self.tk.Frame(dialog, bg=UI_BACKGROUND)
        main.place(x=18, y=18, width=870, height=610)
        history_frame = self.tk.Frame(dialog, bg=UI_PANEL_DARK, highlightthickness=1, highlightbackground=UI_MUTED)
        history_frame.place(x=900, y=18, width=310, height=610)
        history_header = self.tk.Frame(history_frame, bg=UI_PANEL_DARK)
        history_header.pack(fill="x", padx=10, pady=(8, 5))
        self.tk.Label(history_header, text="History", bg=UI_PANEL_DARK, fg=UI_TEXT, font=(self._ui_font_family, 13, "bold"), anchor="w").pack(side="left")
        history_canvas = self.tk.Canvas(history_frame, bg=UI_PANEL_DARK, highlightthickness=0)
        history_inner = self.tk.Frame(history_canvas, bg=UI_PANEL_DARK)
        history_window = history_canvas.create_window((0, 0), window=history_inner, anchor="nw")
        history_canvas.pack(side="top", fill="both", expand=True, padx=10, pady=(0, 0))
        title_pan_jobs: dict[Any, str] = {}
        title_pan_directions: dict[Any, int] = {}

        def cancel_title_pans() -> None:
            for title_canvas, job in list(title_pan_jobs.items()):
                try:
                    title_canvas.after_cancel(job)
                except self.tk.TclError:
                    pass
            title_pan_jobs.clear()
            title_pan_directions.clear()

        def title_pan_tick(title_canvas: Any, title_item: int) -> None:
            title_pan_jobs.pop(title_canvas, None)
            try:
                if not title_canvas.winfo_exists():
                    return
                bbox = title_canvas.bbox(title_item)
                visible_width = max(1, title_canvas.winfo_width())
                if not bbox or bbox[2] - bbox[0] <= visible_width:
                    return
                first, last = (float(value) for value in title_canvas.xview())
                direction = title_pan_directions.get(title_canvas, 1)
                if direction > 0 and last >= 0.999:
                    title_pan_directions[title_canvas] = -1
                    title_pan_jobs[title_canvas] = title_canvas.after(1000, title_pan_tick, title_canvas, title_item)
                    return
                if direction < 0 and first <= 0.001:
                    title_pan_directions[title_canvas] = 1
                    title_pan_jobs[title_canvas] = title_canvas.after(1000, title_pan_tick, title_canvas, title_item)
                    return
                title_canvas.xview_moveto(max(0.0, min(1.0, first + (0.003 * direction))))
                title_pan_jobs[title_canvas] = title_canvas.after(60, title_pan_tick, title_canvas, title_item)
            except self.tk.TclError:
                title_pan_jobs.pop(title_canvas, None)

        def start_title_pan(title_canvas: Any, title_item: int) -> None:
            try:
                bbox = title_canvas.bbox(title_item)
                if bbox and bbox[2] - bbox[0] > max(1, title_canvas.winfo_width()) and title_canvas not in title_pan_jobs:
                    title_pan_directions[title_canvas] = 1
                    title_pan_jobs[title_canvas] = title_canvas.after(1000, title_pan_tick, title_canvas, title_item)
            except self.tk.TclError:
                pass
        history_entries: list[dict[str, Any]] = []
        selected_history_index: list[Optional[int]] = [None]
        history_rows: list[Any] = []

        def update_history_scrollregion(_event: Any = None) -> None:
            history_canvas.configure(scrollregion=history_canvas.bbox("all"))
            history_canvas.update_idletasks()
            visible_width = max(1, history_canvas.winfo_width())
            history_canvas.itemconfigure(history_window, width=visible_width)

        history_inner.bind("<Configure>", update_history_scrollregion)
        history_canvas.bind("<Configure>", update_history_scrollregion)

        def history_path_is_inside(widget: Any, parent: Any) -> bool:
            widget_path = str(widget)
            parent_path = str(parent)
            return widget_path == parent_path or widget_path.startswith(parent_path + ".")

        def history_row_for_widget(widget: Any) -> Optional[int]:
            for row_index, row in enumerate(history_rows):
                if history_path_is_inside(widget, row):
                    return row_index
            return None

        def set_history_row_background(row: Any, background: str) -> None:
            try:
                if not row.winfo_exists():
                    return
                row.configure(bg=background)
            except self.tk.TclError:
                return
            for child in row.winfo_children():
                if isinstance(child, self.tk.Frame):
                    child.configure(bg=background)
                    for label in child.winfo_children():
                        if isinstance(label, self.tk.Label):
                            label.configure(bg=background)
                        elif isinstance(label, self.tk.Canvas):
                            label.configure(bg=background)
                elif isinstance(child, self.tk.Button):
                    child.configure(
                        bg=background,
                        fg=UI_TEXT if background == UI_PINK else UI_PINK,
                        activebackground=background,
                    )

        def set_history_row_foreground(row: Any, foreground: str) -> None:
            try:
                if not row.winfo_exists():
                    return
            except self.tk.TclError:
                return
            for child in row.winfo_children():
                if isinstance(child, self.tk.Frame):
                    for label in child.winfo_children():
                        if isinstance(label, self.tk.Label):
                            label.configure(fg=foreground)
                        elif isinstance(label, self.tk.Canvas):
                            for item in label.find_withtag("history-title"):
                                label.itemconfigure(item, fill=foreground)

        def clear_history_selection(_event: Any = None) -> None:
            selected_history_index[0] = None
            for row_index, row in enumerate(history_rows):
                set_history_row_background(row, UI_PANEL_DARK)
                result_color = "#48e39a" if history_entries[row_index].get("result") == "Correct" else "#ff6f86"
                set_history_row_foreground(row, result_color)

        def select_history_row(row_index: int) -> None:
            selected_history_index[0] = row_index
            for current_index, row in enumerate(history_rows):
                selected = current_index == row_index
                row_bg = UI_PINK if selected else UI_PANEL_DARK
                set_history_row_background(row, row_bg)
                result_color = "#48e39a" if history_entries[current_index].get("result") == "Correct" else "#ff6f86"
                set_history_row_foreground(row, UI_TEXT if selected else result_color)

        def toggle_history_flag(entry: dict[str, Any], row_index: int) -> None:
            key = str(entry.get("key") or "")
            stats = self.play_stats.setdefault(key, {"encounters": 0, "correct": 0, "wrong": 0, "flagged": False})
            stats["flagged"] = not bool(stats.get("flagged"))
            self._queue_profile_save()
            render_history()
            if 0 <= row_index < len(history_rows):
                select_history_row(row_index)

        def render_history() -> None:
            for child in history_inner.winfo_children():
                child.destroy()
            history_rows.clear()
            cancel_title_pans()
            title_font_spec = (self._ui_font_family, 10)
            title_font = self.tkfont.Font(root=self.root, family=self._ui_font_family, size=10)
            title_line_height = max(1, int(title_font.metrics("linespace")) + 2)
            for row_index, entry in enumerate(history_entries):
                result_color = "#48e39a" if entry.get("result") == "Correct" else "#ff6f86"
                row = self.tk.Frame(history_inner, bg=UI_PANEL_DARK, cursor=self._app_cursor, padx=4)
                row.pack(fill="x", anchor="w", pady=(0, 6))
                history_rows.append(row)
                key = str(entry.get("key") or "")
                flagged = bool(self.play_stats.get(key, {}).get("flagged"))
                flag_button = self.tk.Button(
                    row,
                    text="⚑" if flagged else "⚐",
                    command=lambda selected_entry=entry, selected_index=row_index: toggle_history_flag(selected_entry, selected_index),
                    bg=UI_PANEL_DARK,
                    fg=UI_PINK,
                    activebackground=UI_PANEL_DARK,
                    activeforeground=UI_TEXT,
                    relief="flat",
                    bd=0,
                    highlightthickness=1,
                    highlightbackground=UI_MUTED,
                    width=2,
                    height=1,
                    padx=0,
                    pady=0,
                    font=("Segoe UI Symbol", 11),
                    cursor=self._app_cursor,
                )
                flag_button.pack(side="right", padx=(6, 0))
                text_frame = self.tk.Frame(row, bg=UI_PANEL_DARK)
                text_frame.pack(side="left", fill="x", expand=True)
                # Keep the title viewport and metadata as separate packed rows.
                # A fixed font-metric height prevents the canvas from sharing
                # vertical space with the metadata when a title is scrolling.
                title_canvas = self.tk.Canvas(text_frame, bg=UI_PANEL_DARK, highlightthickness=0, height=title_line_height, cursor=self._app_cursor)
                title_canvas.pack(fill="x")
                title_item = title_canvas.create_text(0, 1, anchor="nw", text=str(entry.get("title") or ""), fill=result_color, font=title_font_spec, tags=("history-title",))
                meta_label = self.tk.Label(text_frame, text=str(entry.get("meta") or ""), bg=UI_PANEL_DARK, fg=result_color, anchor="w", justify="left", font=(self._ui_font_family, 8), cursor=self._app_cursor)
                meta_label.pack(fill="x")
                title_canvas.update_idletasks()
                title_bbox = title_canvas.bbox(title_item) or (0, 0, 1, 1)
                title_canvas.configure(scrollregion=(0, 0, max(1, title_bbox[2]), title_line_height))
                for widget in (row, text_frame, title_canvas, meta_label):
                    widget.bind("<Button-1>", lambda _event, selected_index=row_index: select_history_row(selected_index), add="+")
                title_canvas.bind(
                    "<Shift-MouseWheel>",
                    lambda event, canvas=title_canvas: (canvas.xview_scroll(-int(event.delta / 120) if event.delta else -1, "units"), "break")[1],
                    add="+",
                )
                history_canvas.after_idle(lambda canvas=title_canvas, item=title_item: start_title_pan(canvas, item))
            if selected_history_index[0] is not None and selected_history_index[0] < len(history_rows):
                select_history_row(selected_history_index[0])
            update_history_scrollregion()

        def handle_history_wheel(event: Any) -> Optional[str]:
            if history_path_is_inside(event.widget, history_frame):
                delta = int(getattr(event, "delta", 0) / 120) if getattr(event, "delta", 0) else 0
                history_canvas.yview_scroll(-delta if delta else 1, "units")
                return "break"
            return None

        def clear_history_when_clicking_elsewhere(event: Any) -> Optional[str]:
            if history_row_for_widget(event.widget) is not None:
                return None
            clear_history_selection()
            return None

        dialog.bind_all("<MouseWheel>", handle_history_wheel, add="+")
        dialog.bind_all("<Button-1>", clear_history_when_clicking_elsewhere, add="+")
        player = MCIPlayer()
        index = 0
        timer_job: Optional[str] = None
        autoskip_job: Optional[str] = None
        finished = False
        session_summary_shown = False
        session_totals = {"correct": 0, "incorrect": 0}
        guess_var = self.tk.StringVar()
        timer_var = self.tk.StringVar()
        result_var = self.tk.StringVar(value="")
        current_song_var = self.tk.StringVar(value="Preparing song…")
        current_detail_var = self.tk.StringVar(value="")
        current_record: list[Optional[dict[str, Any]]] = [None]
        details_visible = [False]
        song_card = self.tk.Frame(main, bg=UI_PANEL_DARK, highlightthickness=1, highlightbackground=UI_PINK)
        song_card.pack(fill="x", padx=12, pady=(0, 3))
        card_header = self.tk.Frame(song_card, bg=UI_PANEL_DARK)
        card_header.pack(fill="x", padx=10, pady=(2, 0))
        self.tk.Label(card_header, textvariable=current_song_var, bg=UI_PANEL_DARK, fg=UI_TEXT, font=(self._ui_font_family, 12, "bold"), anchor="w").pack(side="left", fill="x", expand=True)
        eye_image = self._ui_image("Elements/eye-crossed-svgrepo-com.png").subsample(16, 16)
        eye_button = self.tk.Button(
            card_header,
            image=eye_image,
            command=lambda: toggle_details(),
            bg=UI_PINK,
            activebackground=UI_PINK_LIGHT,
            relief="flat",
            bd=0,
            highlightthickness=0,
            cursor=self._app_cursor,
        )
        eye_button.image = eye_image
        eye_button.pack(side="right", padx=(8, 0))
        self.tk.Label(song_card, textvariable=current_detail_var, bg=UI_PANEL_DARK, fg=UI_MUTED, font=(self._ui_font_family, 10), anchor="w").pack(fill="x", padx=10, pady=(0, 1))
        count_label = self.ttk.Label(main, text=f"Song 1 of {len(songs)}", font=(self._ui_font_family, 15, "bold"))
        count_label.pack(pady=(1, 1))
        self.ttk.Label(main, text=f"{mode} Session").pack(pady=(0, 1))
        self.ttk.Label(main, textvariable=timer_var).pack()
        timer_progress = self.ttk.Progressbar(main, mode="determinate", maximum=max(1, int(settings.get("guess_time", 1))), style="Pink.Horizontal.TProgressbar")
        timer_progress.pack(fill="x", padx=30, pady=(2, 3))
        self.ttk.Label(main, textvariable=result_var, wraplength=820).pack(pady=3)
        answer_frame = self.ttk.Frame(main)
        answer_frame.pack(fill="x", padx=150, pady=5)
        entry_border = self.tk.Frame(answer_frame, bd=0, highlightthickness=0)
        entry_border.pack(fill="x")
        guess_entry = self.ttk.Entry(
            entry_border,
            textvariable=guess_var,
            font=(self._ui_font_family, 14),
            justify="center",
        )
        guess_entry.pack(fill="x", ipady=6)
        suggestion_frame = self.ttk.Frame(answer_frame)
        suggestion_list = self.tk.Listbox(suggestion_frame, height=6, exportselection=False)
        suggestion_list.pack(fill="x", expand=True)
        self.ttk.Label(main, text="Type or choose an anime title. The autocomplete prioritizes starts-with, contains, word-order, then fuzzy matches.").pack(pady=(0, 4))
        buttons = self.tk.Frame(main, bg=UI_BACKGROUND)
        buttons.pack(pady=4)
        def make_gameplay_button(label: str, command: Callable[[], None], state: str = "normal") -> Any:
            width, height = 112, 35
            button = self.tk.Canvas(buttons, width=width, height=height, bg=UI_BACKGROUND, highlightthickness=0, cursor=self._app_cursor, state=state)
            outer_items = (button.create_line(17, height / 2, 95, height / 2, width=height - 2, fill=UI_MUTED, capstyle="round"),)
            inner_items = (button.create_line(17, height / 2, 95, height / 2, width=height - 4, fill=UI_PANEL_DARK, capstyle="round"),)
            text_id = button.create_text(width / 2, height / 2, text=label, fill=UI_TEXT, font=(self._ui_font_family, 9, "bold"))
            button._kanon_active = False
            button._kanon_hover = False
            button._kanon_command = command

            def render(active: bool) -> None:
                button._kanon_active = active
                disabled = str(button.cget("state")) == "disabled"
                highlighted = not disabled and (active or button._kanon_hover)
                border_color = UI_PINK if highlighted else UI_MUTED
                fill_color = UI_PINK if highlighted else UI_PANEL_DARK
                text_color = UI_MUTED if disabled else UI_TEXT
                for item in outer_items:
                    button.itemconfigure(item, fill=border_color)
                for item in inner_items:
                    button.itemconfigure(item, fill=fill_color)
                button.itemconfigure(text_id, fill=text_color)

            button._render_kanon_state = render
            button.bind("<Button-1>", lambda _event: button._kanon_command() if str(button.cget("state")) != "disabled" else "break")
            button.bind("<Enter>", lambda _event: (setattr(button, "_kanon_hover", True), render(bool(button._kanon_active))))
            button.bind("<Leave>", lambda _event: (setattr(button, "_kanon_hover", False), render(bool(button._kanon_active))))
            button.pack(side="left", padx=7)
            render(False)
            return button

        submit_button = make_gameplay_button("Submit Guess", lambda: None)
        skip_button = make_gameplay_button("Skip Song", lambda: None)
        next_button = make_gameplay_button("Next Song", lambda: None, state="disabled")
        gameplay_volume_var = self.tk.IntVar(value=max(0, min(100, int(self.app_settings.get("volume", 50)))))
        volume_frame = self.tk.Frame(main, bg=UI_BACKGROUND)
        volume_frame.pack(pady=(3, 0))
        volume_label = self.tk.Label(volume_frame, text="", bg=UI_BACKGROUND, fg=UI_MUTED, font=(self._ui_font_family, 8))
        volume_label.pack()
        volume_canvas = self.tk.Canvas(volume_frame, width=250, height=24, bg=UI_BACKGROUND, highlightthickness=0, cursor=self._app_cursor)
        volume_canvas.pack()
        volume_start, volume_end, volume_y = 12.0, 238.0, 12.0
        volume_canvas.create_line(volume_start, volume_y, volume_end, volume_y, fill=UI_MUTED, width=5, capstyle="round")
        volume_fill = volume_canvas.create_line(volume_start, volume_y, volume_start, volume_y, fill=UI_PINK_LIGHT, width=5, capstyle="round")
        volume_knob = self._ui_images.setdefault("gameplay-volume-seek", self._ui_image("Elements/Settings/seek.png").subsample(5, 5))
        volume_knob_id = volume_canvas.create_image(volume_start, volume_y, anchor="center", image=volume_knob)
        volume_canvas.image = volume_knob

        def render_gameplay_volume(*_args: Any) -> None:
            try:
                value = max(0, min(100, int(gameplay_volume_var.get())))
            except (TypeError, ValueError):
                value = 50
            x = volume_start + (value / 100.0) * (volume_end - volume_start)
            volume_canvas.coords(volume_fill, volume_start, volume_y, x, volume_y)
            volume_canvas.coords(volume_knob_id, x, volume_y)
            volume_label.configure(text=f"Volume: {value}%")

        def set_gameplay_volume(event: Any) -> None:
            ratio = max(0.0, min(1.0, (float(event.x) - volume_start) / (volume_end - volume_start)))
            value = int(round(ratio * 100))
            gameplay_volume_var.set(value)
            self.app_settings["volume"] = value
            player.set_volume(value)
            render_gameplay_volume()

        def save_gameplay_volume(_event: Any = None) -> None:
            self.app_settings["volume"] = max(0, min(100, int(gameplay_volume_var.get())))
            self._save_app_settings()

        volume_canvas.bind("<Button-1>", set_gameplay_volume)
        volume_canvas.bind("<B1-Motion>", set_gameplay_volume)
        volume_canvas.bind("<ButtonRelease-1>", save_gameplay_volume)
        gameplay_volume_var.trace_add("write", render_gameplay_volume)
        render_gameplay_volume()
        def update_song_card(record: dict[str, Any]) -> None:
            current_record[0] = record
            song_type = _clean(record.get("songType")) or "Song"
            artist = _clean(record.get("songArtist")) or "Unknown artist"
            if details_visible[0]:
                current_song_var.set(f"{song_type} · {_clean(record.get('songName')) or 'Unknown song'}")
                current_detail_var.set(f"{_clean(record.get('animeVintage')) or 'Unknown season'} · {artist}")
            else:
                current_song_var.set("Song details hidden")
                current_detail_var.set("")

        def toggle_details() -> None:
            details_visible[0] = not details_visible[0]
            if current_record[0] is not None:
                update_song_card(current_record[0])

        def expand_history() -> None:
            popup = self.tk.Toplevel(self.root)
            popup.title("Session History")
            popup.configure(bg=UI_PINK)
            popup.overrideredirect(True)
            popup.transient(self.root)
            popup.grab_set()
            self._center_window(popup, 980, 520)
            popup_surface = self.tk.Frame(popup, bg=UI_BACKGROUND)
            popup_surface.pack(fill="both", expand=True, padx=4, pady=4)
            popup_header = self.tk.Frame(popup_surface, bg=UI_BACKGROUND)
            popup_header.pack(fill="x", padx=18, pady=(10, 8))
            self._make_kanon_button(popup_header, "Back", popup.destroy, width=80, height=32, font_size=9).pack(side="left")
            self.tk.Label(popup_header, text="Session History", bg=UI_BACKGROUND, fg=UI_TEXT, font=(self._ui_font_family, 19, "bold"), anchor="center").pack(side="left", fill="x", expand=True, padx=(12, 80))
            table_frame = self.tk.Frame(popup_surface, bg=UI_BACKGROUND)
            table_frame.pack(fill="both", expand=True, padx=18, pady=(0, 10))
            columns = ("number", "anime", "type", "answer", "guesses", "result")
            history_tree = self.ttk.Treeview(table_frame, columns=columns, show="headings")
            headings = {
                "number": "#",
                "anime": "Anime",
                "type": "Type",
                "answer": "Answer",
                "guesses": "Guesses",
                "result": "Result",
            }
            widths = {"number": 42, "anime": 260, "type": 110, "answer": 260, "guesses": 120, "result": 90}
            for column in columns:
                history_tree.heading(column, text=headings[column])
                history_tree.column(column, width=widths[column], minwidth=widths[column], stretch=column in {"anime", "answer"}, anchor="center" if column in {"number", "guesses", "result"} else "w")
            history_tree.tag_configure("correct", foreground="#48e39a")
            history_tree.tag_configure("incorrect", foreground="#ff6f86")
            for number, item in enumerate(history_entries, start=1):
                tag = "correct" if item.get("result") == "Correct" else "incorrect"
                history_tree.insert(
                    "",
                    "end",
                    values=(number, item.get("title", ""), item.get("type", ""), item.get("answer", ""), item.get("guesses", ""), item.get("result", "")),
                    tags=(tag,),
                )
            history_tree.pack(side="left", fill="both", expand=True)
            history_popup_scroll = self.ttk.Scrollbar(table_frame, orient="vertical", command=history_tree.yview)
            history_tree.configure(yscrollcommand=history_popup_scroll.set)
            history_popup_scroll.pack(side="right", fill="y")
            popup.protocol("WM_DELETE_WINDOW", popup.destroy)
            popup.bind("<Escape>", lambda _event: popup.destroy())
            self._activate_dialog(popup)

        expand_button = self._make_kanon_button(history_header, "Expand", expand_history, width=80, height=32, font_size=9)
        expand_button.pack(side="right")
        suggestion_job: Optional[str] = None
        suggestions_suppressed = False
        suggestions_query = [""]
        def focus_guess_entry() -> None:
            if guess_entry.winfo_exists() and str(guess_entry.cget("state")) != "disabled":
                guess_entry.focus_force()
                guess_entry.icursor("end")
        def update_suggestions() -> None:
            nonlocal suggestion_job
            suggestion_job = None
            if suggestions_suppressed:
                return
            query = guess_var.get()
            suggestions_query[0] = query
            values = self.library.index.search(query, 15)
            suggestion_list.delete(0, "end")
            for value in values:
                suggestion_list.insert("end", value)
            if values:
                if not suggestion_frame.winfo_ismapped():
                    suggestion_frame.pack(fill="x", pady=(4, 0))
                suggestion_list.selection_clear(0, "end")
                suggestion_list.selection_set(0)
                suggestion_list.activate(0)
            else:
                suggestion_frame.pack_forget()
        def schedule_suggestions(*_args: Any) -> None:
            nonlocal suggestion_job
            if suggestions_suppressed:
                return
            if suggestion_job:
                dialog.after_cancel(suggestion_job)
        # A short debounce keeps typing responsive while preserving
        # immediate dropdown feedback after the user pauses briefly.
            suggestion_job = dialog.after(60, update_suggestions)
        guess_var.trace_add("write", schedule_suggestions)
        guess_entry.bind("<FocusIn>", schedule_suggestions)
        def reclaim_guess_focus(_event: Any = None) -> None:
            # ttk widgets can retain focus on the last game control after a
            # click elsewhere.  Reclaim it after Tk processes the mouse event
            # so clicking back into the answer box always resumes typing.
            dialog.after_idle(focus_guess_entry)
        guess_entry.configure(takefocus=True)
        guess_entry.bind("<ButtonPress-1>", lambda _event: focus_guess_entry(), add="+")
        guess_entry.bind("<ButtonRelease-1>", reclaim_guess_focus, add="+")
        def choose_suggestion(_event: Any = None) -> str:
            nonlocal suggestions_suppressed
            suggestions_suppressed = True
            selection = suggestion_list.curselection()
            if selection:
                guess_var.set(suggestion_list.get(selection[0]))
                suggestion_list.delete(0, "end")
                suggestion_frame.pack_forget()
                guess_entry.focus_set()
                guess_entry.icursor("end")
            return "break"

        def move_suggestion(event: Any) -> str | None:
            """Move the dropdown highlight while keeping focus in the entry."""
            if not suggestion_list.size():
                return None
            selection = suggestion_list.curselection()
            current = int(selection[0]) if selection else int(suggestion_list.index("active"))
            offset = 1 if event.keysym == "Down" else -1
            next_index = max(0, min(suggestion_list.size() - 1, current + offset))
            suggestion_list.selection_clear(0, "end")
            suggestion_list.selection_set(next_index)
            suggestion_list.activate(next_index)
            suggestion_list.see(next_index)
            return "break"

        def choose_highlighted_suggestion(_event: Any = None) -> str:
            """First Enter accepts the highlighted item without submitting."""
            nonlocal suggestions_suppressed
            if not suggestion_list.size():
                return "break"
            selection = suggestion_list.curselection()
            selected_index = int(selection[0]) if selection else int(suggestion_list.index("active"))
            suggestions_suppressed = True
            guess_var.set(suggestion_list.get(selected_index))
            suggestion_list.delete(0, "end")
            suggestion_frame.pack_forget()
            suggestions_query[0] = guess_var.get()
            guess_entry.focus_set()
            guess_entry.icursor("end")
            return "break"

        def note_guess_typing(event: Any) -> None:
            nonlocal suggestions_suppressed
            if event.keysym not in {"Return", "Up", "Down"}:
                suggestions_suppressed = False
                schedule_suggestions()

        suggestion_list.bind("<ButtonRelease-1>", choose_suggestion)
        suggestion_list.bind("<Double-Button-1>", choose_suggestion)
        suggestion_list.bind("<Return>", choose_suggestion)
        guess_entry.bind("<Up>", move_suggestion, add="+")
        guess_entry.bind("<Down>", move_suggestion, add="+")
        guess_entry.bind("<KeyRelease>", note_guess_typing, add="+")
        def answer_aliases(record: dict[str, Any]) -> set[str]:
            aliases = {_search_clean(record.get("animeENName")), _search_clean(record.get("animeJPName"))}
            aliases.update(_search_clean(value) for value in _clean(record.get("animeAltName")).split(","))
            return {alias for alias in aliases if alias}
        def stop_timer() -> None:
            nonlocal timer_job
            if timer_job:
                self.root.after_cancel(timer_job)
                timer_job = None
        def stop_autoskip() -> None:
            nonlocal autoskip_job
            if autoskip_job:
                self.root.after_cancel(autoskip_job)
                autoskip_job = None

        def cleanup_session() -> None:
            nonlocal finished, suggestion_job
            finished = True
            try:
                stop_timer()
            except self.tk.TclError:
                pass
            try:
                stop_autoskip()
            except self.tk.TclError:
                pass
            try:
                player.stop()
            except Exception:
                pass
            if suggestion_job:
                try:
                    dialog.after_cancel(suggestion_job)
                except self.tk.TclError:
                    pass
                suggestion_job = None
            cancel_title_pans()
            try:
                surface.unbind_all("<MouseWheel>")
                surface.unbind_all("<Button-1>")
                surface.unbind_all("<Escape>")
            except self.tk.TclError:
                pass

        def show_session_finished() -> None:
            nonlocal session_summary_shown
            if session_summary_shown:
                return
            session_summary_shown = True
            cleanup_session()
            popup = self.tk.Toplevel(self.root)
            popup.title("Session Finished")
            popup.configure(bg=UI_PINK)
            popup.overrideredirect(True)
            popup.transient(self.root)
            popup.grab_set()
            self._center_window(popup, 440, 300)
            popup_surface = self.tk.Frame(popup, bg=UI_BACKGROUND)
            popup_surface.pack(fill="both", expand=True, padx=4, pady=4)
            self.tk.Label(
                popup_surface,
                text=f"Session Finished!\nCorrect: {session_totals['correct']}\nIncorrect: {session_totals['incorrect']}",
                bg=UI_BACKGROUND,
                fg=UI_TEXT,
                font=(self._ui_font_family, 17, "bold"),
                justify="center",
            ).pack(expand=True, pady=(26, 18))
            popup_buttons = self.tk.Frame(popup_surface, bg=UI_BACKGROUND)
            popup_buttons.pack(pady=(0, 24))

            def back_to_modes() -> None:
                popup.destroy()
                if surface.winfo_exists():
                    surface.destroy()
                self._build_play_home()

            def restart_session() -> None:
                popup.destroy()
                if surface.winfo_exists():
                    surface.destroy()
                self._begin_play_session(mode, settings)

            self._make_kanon_button(popup_buttons, "Back", back_to_modes, width=120, height=36, font_size=10).pack(side="left", padx=8)
            self._make_kanon_button(popup_buttons, "Restart", restart_session, width=120, height=36, font_size=10, active_color=UI_PINK_DARK, hover_color=UI_PINK_DARK).pack(side="left", padx=8)
            popup.protocol("WM_DELETE_WINDOW", back_to_modes)
            popup.bind("<Escape>", lambda _event: back_to_modes())
            self._activate_dialog(popup)

        def end_session() -> None:
            def leave_after_click() -> None:
                try:
                    cleanup_session()
                finally:
                    try:
                        if dialog.winfo_exists():
                            dialog.destroy()
                    except self.tk.TclError:
                        pass
                    try:
                        if surface.winfo_exists():
                            surface.destroy()
                    except self.tk.TclError:
                        pass
                    self._build_play_home()
            # Let Tk finish dispatching the Back button event before removing
            # the Canvas that is currently handling it.
            self.root.after_idle(leave_after_click)
        def schedule_autoskip() -> None:
            nonlocal autoskip_job
            if not settings.get("autoskip", True) or not dialog.winfo_exists():
                return
            delay = max(0, int(settings.get("autoskip_seconds", 1))) * 1000
            autoskip_job = dialog.after(delay, next_song)
        def finish_song(correct: bool, timed_out: bool = False) -> None:
            nonlocal finished
            if finished:
                return
            finished = True
            stop_timer()
            player.stop()
            session_totals["correct" if correct else "incorrect"] += 1
            record = songs[index]
            stats = self.play_stats.setdefault(_record_key(record), {"encounters": 0, "correct": 0, "wrong": 0, "flagged": False})
            stats["encounters"] = int(stats.get("encounters", 0) or 0) + 1
            stats["correct" if correct else "wrong"] = int(stats.get("correct" if correct else "wrong", 0) or 0) + 1
            # Defer the JSON write until Tk has returned to the event loop so
            # answer feedback/history can paint without a synchronous pause.
            self._queue_profile_save()
            rate_text = f"{_record_guess_rate(stats):.0f}%"
            history_entries.insert(0, {
                "key": _record_key(record),
                "title": self._display_title(record),
                "meta": f"{_clean(record.get('songType')) or 'Song'} · Guess rate: {rate_text}",
                "detail": f"{_clean(record.get('songName')) or 'Unknown song'} · {_clean(record.get('songArtist')) or 'Unknown artist'} · {_clean(record.get('animeVintage')) or 'Unknown season'}",
                "type": _clean(record.get("songType")) or "Song",
                "answer": f"{_clean(record.get('songName')) or 'Unknown song'} · {_clean(record.get('songArtist')) or 'Unknown artist'}",
                "guesses": f"{stats.get('correct', 0)}/{stats.get('encounters', 0)} ({rate_text})",
                "result": "Correct" if correct else "Incorrect",
            })
            selected_history_index[0] = None
            render_history()
            entry_border.configure(highlightthickness=3, highlightbackground="#28a745" if correct else "#dc3545", highlightcolor="#28a745" if correct else "#dc3545")
            answer = self._display_title(record)
            result_var.set(("Correct! " if correct else ("Time's up. " if timed_out else "Incorrect. ")) + f"Answer: {answer} · {record.get('songName', '')} · {record.get('songArtist', '')}")
            submit_button.configure(state="disabled")
            submit_button._render_kanon_state(False)
            next_button.configure(state="normal")
            next_button._render_kanon_state(False)
            schedule_autoskip()
        def tick(remaining: int) -> None:
            nonlocal timer_job
            if finished or not dialog.winfo_exists():
                return
            timer_var.set(f"Guess time remaining: {remaining} seconds")
            timer_progress["value"] = max(0, remaining)
            if remaining <= 0:
                finish_song(False, True)
            else:
                timer_job = self.root.after(1000, lambda: tick(remaining - 1))
        def load_song() -> None:
            nonlocal finished, suggestions_suppressed
            stop_timer()
            stop_autoskip()
            if index >= len(songs):
                self.status_var.set(f"{mode} session complete.")
                show_session_finished()
                return
            finished = False
            record = songs[index]
            update_song_card(record)
            suggestions_suppressed = False
            guess_var.set("")
            suggestion_list.delete(0, "end")
            suggestion_frame.pack_forget()
            suggestions_query[0] = ""
            entry_border.configure(highlightthickness=0)
            result_var.set("")
            count_label.configure(text=f"Song {index + 1} of {len(songs)}")
            submit_button.configure(state="normal")
            submit_button._render_kanon_state(False)
            next_button.configure(state="disabled")
            next_button._render_kanon_state(False)
            try:
                player.play(_clean(record.get("download_path")), settings["sample_point"], settings["custom_percent"], settings["guess_time"], self.app_settings.get("volume", 50))
            except Exception as exc:
                result_var.set(f"Could not play this song: {exc}")
                schedule_autoskip()
            tick(settings["guess_time"])
        def submit() -> None:
            record = songs[index]
            correct = _search_clean(guess_var.get()) in answer_aliases(record)
            finish_song(correct)
        def submit_or_choose_suggestion(_event: Any = None) -> str:
            nonlocal suggestion_job, suggestions_suppressed
            if suggestion_job:
                dialog.after_cancel(suggestion_job)
                suggestion_job = None
            # Preserve the highlighted item after Up/Down. Rebuilding the
            # dropdown here would always select its first entry again.
            if not suggestions_suppressed and suggestions_query[0] != guess_var.get():
                update_suggestions()
            if suggestion_list.size() and not suggestions_suppressed:
                return choose_highlighted_suggestion()
            suggestions_suppressed = True
            suggestion_list.delete(0, "end")
            suggestion_frame.pack_forget()
            submit()
            return "break"
        def next_song() -> None:
            nonlocal index
            stop_autoskip()
            index += 1
            load_song()
        submit_button._kanon_command = submit
        guess_entry.bind("<Return>", submit_or_choose_suggestion)
        skip_button._kanon_command = lambda: finish_song(False)
        next_button._kanon_command = next_song
        make_gameplay_button("Back", end_session)
        surface.bind_all("<Escape>", lambda _event: end_session())
        load_song()
        # The player and the first render can both run focus-affecting Tk
        # callbacks, so apply focus once after idle and once shortly after the
        # first song is visible.
        dialog.after_idle(focus_guess_entry)
        dialog.after(100, focus_guess_entry)

    def open_downloads(self) -> None:
        if not self.collection:
            self.new_profile()
            return
        self.new_profile_mode = False
        self.profile_name_var.set(self.profile_var.get())
        self._build_import_screen()

    def select_profile(self) -> None:
        names = _profile_names()
        if not names:
            return
        dialog = self.tk.Toplevel(self.root)
        dialog.title("Select Profile")
        dialog.configure(bg=UI_PINK)
        dialog.overrideredirect(True)
        dialog.transient(self.root)
        dialog.grab_set()
        self._center_window(dialog, POPUP_WIDTH, POPUP_HEIGHT)
        surface = self.tk.Frame(dialog, bg=UI_BACKGROUND)
        surface.pack(fill="both", expand=True, padx=4, pady=4)
        canvas = self.tk.Canvas(surface, width=POPUP_WIDTH - 8, height=POPUP_HEIGHT - 8, bg=UI_BACKGROUND, highlightthickness=0)
        canvas.pack(fill="both", expand=True)
        # Keep the heading on the arrow's horizontal tip line, matching the
        # Profile menu, and leave the upper-left area clear for the arrow hitbox.
        canvas.create_text(273, 65, text="Select Profile", fill=UI_TEXT, font=(self._ui_font_family, 24, "bold"))
        box = self.tk.Listbox(
            surface,
            exportselection=False,
            bg=UI_PANEL_DARK,
            fg=UI_TEXT,
            selectbackground=UI_PINK,
            selectforeground=UI_TEXT,
            relief="flat",
            bd=0,
            highlightthickness=0,
            font=(self._ui_font_family, 12),
        )
        box.place(x=70, y=130, width=405, height=220)
        for name in names:
            box.insert("end", name)
        if self.profile_var.get() in names:
            box.selection_set(names.index(self.profile_var.get()))

        def scroll_profile_list(event: Any) -> str:
            delta = int(event.delta / 120) if event.delta else 0
            if not delta:
                delta = 1 if getattr(event, "num", 0) == 5 else -1
            box.yview_scroll(-delta, "units")
            return "break"

        # The list remains scrollable without showing a native scrollbar, as
        # requested for the other full-screen settings surfaces.
        box.bind("<MouseWheel>", scroll_profile_list)
        box.bind("<Button-4>", scroll_profile_list)
        box.bind("<Button-5>", scroll_profile_list)
        def choose() -> None:
            selection = box.curselection()
            if not selection:
                return
            self.load_profile(box.get(selection[0]))
            dialog.destroy()
        def delete_selected() -> None:
            selection = box.curselection()
            if not selection:
                self.messagebox.showinfo("Choose a profile", "Select a profile to delete first.", parent=dialog)
                return
            name = box.get(selection[0])
            if not self.messagebox.askyesno("Delete profile", "Delete this profile? This action cannot be undone", parent=dialog):
                return
            profile_dir = self._profile_path(name).parent
            try:
                if profile_dir.exists():
                    shutil.rmtree(profile_dir)
            except OSError as exc:
                self.messagebox.showerror("Could not delete profile", str(exc), parent=dialog)
                return
            remaining = _profile_names()
            dialog.destroy()
            if name == self.profile_var.get():
                if remaining:
                    self.load_profile(remaining[0])
                else:
                    self.profile_var.set("Default")
                    self.profile_name_var.set("Default")
                    self.collection = None
                    self.import_paths = []
                    self.enabled_lists = set()
                    self.excluded_song_keys = set()
                    self.download_records = []
                    self.play_stats = {}
                    self.current_manifest_path = ""
                    self.new_profile_mode = False
                    self._build_profile_home()
                    self.root.after(80, self._show_no_profiles_prompt)
            else:
                self.status_var.set(f"Deleted profile: {name}")

        def leave_popup(_event: Any = None) -> str:
            dialog.destroy()
            self.show_profile_menu()
            return "break"

        def dispatch_back(event: Any) -> str:
            if 0 <= event.x <= 150 and 0 <= event.y <= 125:
                return leave_popup(event)
            return None

        canvas.bind("<Button-1>", dispatch_back)
        # Use the same compact animated buttons as the Profile menu.  This
        # keeps the popup actions visually consistent and leaves a little
        # breathing room between the two controls.
        self._popup_button(canvas, 37, 400, "Use Profile", choose, hover_options=True)
        self._popup_button(canvas, 295, 400, "Delete Profile", delete_selected, hover_options=True)
        back_arrow = self._ui_images.setdefault("select-profile-back-arrow", self._ui_image("Elements/back-button.png").zoom(3, 3).subsample(4, 4))
        canvas.create_image(75, 65, image=back_arrow, tags=("select-profile-back",))
        canvas.tag_bind("select-profile-back", "<Button-1>", leave_popup)
        dialog.protocol("WM_DELETE_WINDOW", dialog.destroy)
        dialog.bind("<Escape>", lambda _event: dialog.destroy())
        box.bind("<Double-1>", lambda _event: choose())
        self._activate_dialog(dialog)

    def _build_import_screen(self) -> None:
        self._clear_content()
        ttk = self.ttk
        surface = self.tk.Frame(self.content, bg=UI_BACKGROUND)
        surface.pack(fill="both", expand=True)
        self.tk.Label(surface, text="New Profile" if self.new_profile_mode else "Download", bg=UI_BACKGROUND, fg=UI_TEXT, font=(self._ui_font_family, 24, "bold")).place(relx=0.5, y=78, anchor="center")
        back_area = self.tk.Frame(surface, bg=UI_BACKGROUND, cursor=self._app_cursor)
        back_area.place(x=0, y=0, width=160, height=185)
        back = self.tk.Label(back_area, image=self._ui_image("Elements/back-button.png"), bg=UI_BACKGROUND, cursor=self._app_cursor)
        back.place(x=25, y=22)
        def leave_import_screen() -> None:
            if self.new_profile_mode:
                self._cancel_new_profile()
            else:
                self._build_profile_home()

        back_area.bind("<Button-1>", lambda _event: leave_import_screen())
        back.bind("<Button-1>", lambda _event: leave_import_screen())
        profile_frame = ttk.LabelFrame(surface, text="Profile Name")
        profile_frame.place(x=140, y=125, width=300, height=70)
        name_entry = ttk.Entry(profile_frame, textvariable=self.profile_name_var)
        name_entry.pack(fill="x", padx=8, pady=8)
        name_entry.bind("<ButtonPress-1>", lambda _event: name_entry.focus_force(), add="+")
        name_entry.bind("<ButtonRelease-1>", lambda _event: name_entry.focus_force(), add="+")
        if not self.new_profile_mode:
            name_entry.configure(state="readonly")

        file_frame = ttk.LabelFrame(surface, text="AniList/MAL/AMQ/AnisongDB Export File")
        file_frame.place(x=450, y=125, width=690, height=70)
        ttk.Entry(file_frame, textvariable=self.path_var).pack(side="left", fill="x", expand=True, padx=6, pady=6)
        ttk.Button(file_frame, text="Browse…", command=self.browse_input).pack(side="left", padx=3)
        ttk.Button(file_frame, text="Load list", command=self.load_list).pack(side="left", padx=(3, 6))

        filter_frame = ttk.LabelFrame(surface, text="Download Filters")
        # Keep the filter container close to its actual three rows of controls
        # instead of reserving a large unused area underneath them.
        filter_frame.place(x=140, y=205, width=1000, height=135)
        self.filter_body = ttk.Frame(filter_frame)
        # Filters are always visible; removing the toggle gives the form back
        # the vertical space that the collapsed/expanded control consumed.
        self.filter_body.pack(fill="x", padx=5, pady=3)
        ttk.Label(self.filter_body, text="Song types:").grid(row=0, column=0, sticky="w", padx=5, pady=3)
        for col, (label, variable) in enumerate((("Opening", self.opening_var), ("Ending", self.ending_var), ("Insert", self.insert_var)), start=1):
            ttk.Checkbutton(self.filter_body, text=label, variable=variable).grid(row=0, column=col, sticky="w")
        ttk.Label(self.filter_body, text="Categories:").grid(row=1, column=0, sticky="w", padx=5, pady=3)
        for col, (label, variable) in enumerate((("Standard", self.standard_var), ("Character", self.character_var), ("Chanting", self.chanting_var), ("Instrumental", self.instrumental_var), ("Other", self.other_var)), start=1):
            ttk.Checkbutton(self.filter_body, text=label, variable=variable).grid(row=1, column=col, sticky="w")
        ttk.Label(self.filter_body, text="Year range:").grid(row=2, column=0, sticky="w", padx=5, pady=3)
        ttk.Entry(self.filter_body, textvariable=self.year_min_var, width=7).grid(row=2, column=1, sticky="w")
        ttk.Label(self.filter_body, text="to").grid(row=2, column=2)
        ttk.Entry(self.filter_body, textvariable=self.year_max_var, width=7).grid(row=2, column=3, sticky="w")
        ttk.Label(self.filter_body, text="Season:").grid(row=2, column=4, padx=(14, 3), sticky="e")
        ttk.Combobox(self.filter_body, textvariable=self.season_var, values=("All", "Winter", "Spring", "Summer", "Fall"), state="readonly", width=9).grid(row=2, column=5, sticky="w")
        ttk.Label(self.filter_body, text="Media:").grid(row=2, column=6, padx=(14, 3), sticky="e")
        ttk.Combobox(self.filter_body, textvariable=self.media_var, values=("audio", "HQ", "MQ"), state="readonly", width=7).grid(row=2, column=7, sticky="w")

        output = ttk.Frame(surface)
        output.place(x=140, y=350, width=1000, height=42)
        ttk.Label(output, text="Output folder:").pack(side="left")
        ttk.Entry(output, textvariable=self.output_var).pack(side="left", fill="x", expand=True, padx=6)
        ttk.Button(output, text="Browse…", command=self.browse_output).pack(side="left")

        list_frame = ttk.LabelFrame(surface, text="Detected Lists")
        list_frame.place(x=140, y=400, width=1000, height=200)
        columns = ("list", "kind", "entries", "songs")
        self.list_tree = ttk.Treeview(list_frame, columns=columns, show="headings", selectmode="browse")
        for column, heading, width in (("list", "List", 360), ("kind", "Type", 130), ("entries", "# of Entries", 110), ("songs", "# of Songs", 110)):
            self.list_tree.heading(column, text=heading)
            self.list_tree.column(column, width=width, anchor="w" if column == "list" else "center")
        scroll = ttk.Scrollbar(list_frame, orient="vertical", command=self.list_tree.yview)
        self.list_tree.configure(yscrollcommand=scroll.set)
        self.list_tree.pack(side="left", fill="both", expand=True)
        scroll.pack(side="right", fill="y")
        actions = ttk.Frame(surface)
        actions.place(x=140, y=620, width=1000, height=50)
        ttk.Button(actions, text="Custom Download", command=self.custom_download).pack(side="left")
        ttk.Button(actions, text="Download selected list", command=self.download_selected).pack(side="left", padx=7)
        ttk.Button(actions, text="Save Profile", command=lambda: self.save_profile(force=True)).pack(side="right")
        self._populate_lists()

    def _initialize_profiles(self) -> None:
        try:
            self._set_startup_progress("Checking local profiles…", 16)
            PROFILE_ROOT.mkdir(parents=True, exist_ok=True)
            names = _profile_names()
            self._set_startup_progress("Selecting the last used profile…", 32)
            if not names:
                self._no_profiles_detected = True
                self.profile_var.set("Default")
                self.profile_name_var.set("Default")
                self.collection = None
                self.import_paths = []
                self.enabled_lists = set()
                self.excluded_song_keys = set()
                self.download_records = []
                self.play_stats = {}
                self.current_manifest_path = ""
                self._set_startup_progress("No profiles found.", 86)
                return
            last_profile = _clean(self.app_settings.get("last_profile"))
            selected = last_profile if last_profile in names else (self.profile_var.get() if self.profile_var.get() in names else names[0])
            self.profile_var.set(selected)
            self._set_startup_progress(f"Restoring {selected}…", 48)
            self.load_profile(selected)
            self._set_startup_progress("Restoring saved downloads and play history…", 86)
        except OSError as exc:
            self.status_var.set(f"Profile storage unavailable: {exc}")
        except Exception as exc:
            self.status_var.set(f"Profile startup failed: {exc}")
            self._report_callback_exception(type(exc), exc, exc.__traceback__)
        finally:
            self.root.after(40, self._finish_startup_loading)

    def _profile_path(self, name: str) -> Path:
        return PROFILE_ROOT / _profile_slug(name) / "profile.json"

    def _queue_profile_save(self, delay_ms: int = 20) -> None:
        """Persist small gameplay changes after the current UI event paints."""
        if self._profile_save_job:
            try:
                self.root.after_cancel(self._profile_save_job)
            except self.tk.TclError:
                pass
        self._profile_save_job = self.root.after(delay_ms, self._flush_profile_save)

    def _flush_profile_save(self) -> None:
        self._profile_save_job = None
        self.save_profile()

    def save_profile(self, force: bool = False) -> bool:
        # New Profile is a draft until the explicit Save Profile button is
        # pressed. Background operations may still call save_profile(), but
        # they must never create a profile directory behind the user's back.
        if self.new_profile_mode and not force:
            return False
        was_new_profile = self.new_profile_mode
        name = (self.profile_name_var.get() if was_new_profile else self.profile_var.get()).strip() or "Default"
        if was_new_profile and name in _profile_names():
            self.messagebox.showerror("Profile name already exists", "Choose a different profile name before saving.", parent=self.root)
            return False
        self.profile_var.set(name)
        self.profile_name_var.set(name)
        try:
            profile_path = self._profile_path(name)
            profile_path.parent.mkdir(parents=True, exist_ok=True)
            payload = {
                "profile_name": name,
                "source_path": self.path_var.get(),
                "source_paths": list(self.import_paths),
                "enabled_lists": sorted(self.enabled_lists),
                "excluded_song_keys": sorted(self.excluded_song_keys),
                "output_dir": self.output_var.get(),
                "preferred_media": self.media_var.get(),
                "filters": {
                    "opening": self.opening_var.get(),
                    "ending": self.ending_var.get(),
                    "insert": self.insert_var.get(),
                    "standard": self.standard_var.get(),
                    "character": self.character_var.get(),
                    "chanting": self.chanting_var.get(),
                    "instrumental": self.instrumental_var.get(),
                    "other": self.other_var.get(),
                    "year_min": self.year_min_var.get(),
                    "year_max": self.year_max_var.get(),
                    "season": self.season_var.get(),
                },
                "manifest_path": self.current_manifest_path,
                "downloads": self.download_records,
                "play_stats": self.play_stats,
                "collection": _collection_to_dict(self.collection),
            }
            with open(profile_path, "w", encoding="utf-8") as handle:
                json.dump(payload, handle, ensure_ascii=False, indent=2)
            self.app_settings["last_profile"] = name
            self._save_app_settings()
            if was_new_profile:
                self.new_profile_mode = False
                self._profile_before_new_name = ""
            self.status_var.set(f"Saved profile: {name}")
            if was_new_profile:
                self._build_profile_home()
            return True
        except OSError as exc:
            self.messagebox.showerror("Could not save profile", str(exc), parent=self.root)
            return False

    def load_profile(self, name: str) -> None:
        profile_path = self._profile_path(name)
        if not profile_path.exists():
            self.profile_var.set(name)
            self.profile_name_var.set(name)
            self.collection = None
            self.import_paths = []
            self.enabled_lists = set()
            self.excluded_song_keys = set()
            self.download_records = []
            self.play_stats = {}
            self.current_manifest_path = ""
            self._profile_before_new_name = ""
            self._build_profile_home()
            return
        try:
            with open(profile_path, "r", encoding="utf-8") as handle:
                payload = json.load(handle)
            self.profile_var.set(_clean(payload.get("profile_name")) or name)
            self.profile_name_var.set(self.profile_var.get())
            self.app_settings["last_profile"] = self.profile_var.get()
            self._save_app_settings()
            self.new_profile_mode = False
            self._profile_before_new_name = ""
            collection_data = payload.get("collection")
            self.collection = _collection_from_dict(collection_data)
            raw_paths = payload.get("source_paths")
            if isinstance(raw_paths, list):
                self.import_paths = [_clean(path) for path in raw_paths if _clean(path)]
            else:
                source_path = _clean(payload.get("source_path"))
                self.import_paths = [source_path] if source_path else []
            if self.collection:
                if not self.import_paths and self.collection.path:
                    self.import_paths = [part for part in self.collection.path.split(";") if _clean(part)]
                self.path_var.set("; ".join(self.import_paths) or self.collection.path)
                saved_enabled = payload.get("enabled_lists")
                if isinstance(saved_enabled, list):
                    self.enabled_lists = {name for name in saved_enabled if name in self.collection.buckets}
                else:
                    # Profiles created before list toggles existed default to
                    # every imported list being enabled.
                    self.enabled_lists = set(self.collection.buckets)
                saved_excluded = payload.get("excluded_song_keys")
                self.excluded_song_keys = {str(key) for key in saved_excluded} if isinstance(saved_excluded, list) else set()
            else:
                self.path_var.set(_clean(payload.get("source_path")))
                self.enabled_lists = set()
                self.excluded_song_keys = set()
            self.output_var.set(_clean(payload.get("output_dir")) or str(Path.cwd() / "downloads"))
            self.media_var.set(_clean(payload.get("preferred_media")) or "audio")
            filters = payload.get("filters") or {}
            for key, variable in (
                ("opening", self.opening_var), ("ending", self.ending_var), ("insert", self.insert_var),
                ("standard", self.standard_var), ("character", self.character_var), ("chanting", self.chanting_var),
                ("instrumental", self.instrumental_var), ("other", self.other_var),
            ):
                if key in filters:
                    variable.set(bool(filters[key]))
            self.year_min_var.set(_clean(filters.get("year_min")) or "1924")
            self.year_max_var.set(_clean(filters.get("year_max")) or str(dt.datetime.now().year))
            self.season_var.set(_clean(filters.get("season")) or "All")
            self.current_manifest_path = _clean(payload.get("manifest_path"))
            self.download_records = payload.get("downloads") or []
            self.play_stats = payload.get("play_stats") or {}
            if not self.download_records and self.current_manifest_path:
                try:
                    with open(self.current_manifest_path, "r", encoding="utf-8") as handle:
                        self.download_records = json.load(handle)
                except (OSError, ValueError):
                    pass
            self._populate_lists()
            if self.collection:
                self.status_var.set(f"Loaded {self.collection.source} profile '{self.profile_var.get()}': {self.collection.total_entries:,} entries and {len(self.download_records):,} saved downloads.")
            else:
                self.status_var.set(f"Profile '{self.profile_var.get()}' is ready. Import an export to begin.")
            self._build_profile_home()
        except (OSError, ValueError, TypeError, KeyError) as exc:
            self.messagebox.showerror("Could not load profile", str(exc), parent=self.root)

    def switch_profile(self) -> None:
        if self.busy:
            self.messagebox.showinfo("Operation in progress", "Wait for the current operation to finish before switching profiles.", parent=self.root)
            return
        self.load_profile(self.profile_var.get())

    def _cancel_new_profile(self) -> None:
        """Leave an unfinished New Profile screen without unloading the active profile."""
        if self.count_refresh_job:
            try:
                self.root.after_cancel(self.count_refresh_job)
            except self.tk.TclError:
                pass
            self.count_refresh_job = None
        previous_name = self._profile_before_new_name
        self._profile_before_new_name = ""
        self.new_profile_mode = False
        if previous_name and previous_name in _profile_names():
            self.load_profile(previous_name)
        else:
            self.profile_var.set("Default")
            self.profile_name_var.set("Default")
            self.collection = None
            self.import_paths = []
            self.enabled_lists = set()
            self.excluded_song_keys = set()
            self.download_records = []
            self.play_stats = {}
            self.current_manifest_path = ""
            self.path_var.set("")
            self._build_profile_home()

    def new_profile(self) -> None:
        self._suspend_menu_player()
        if not self.new_profile_mode:
            self._profile_before_new_name = self.profile_var.get()
        self.new_profile_mode = True
        self.profile_name_var.set("")
        self.collection = None
        self.import_paths = []
        self.enabled_lists = set()
        self.excluded_song_keys = set()
        self.path_var.set("")
        self.download_records = []
        self.play_stats = {}
        self.current_manifest_path = ""
        self.output_var.set(str(Path.cwd() / "downloads"))
        self.status_var.set("Enter a profile name and choose an AniList, MAL, AMQ, or AnisongDB export.")
        self._build_import_screen()

    def _populate_lists(self) -> None:
        if not hasattr(self, "list_tree") or not self.list_tree.winfo_exists():
            return
        for row in self.list_tree.get_children():
            self.list_tree.delete(row)
        self.list_rows.clear()
        if not self.collection:
            return
        for name, bucket in self.collection.buckets.items():
            row = self.list_tree.insert("", "end", values=(name, display_bucket_type(self.collection, bucket), len(bucket.entries), _fmt_count(bucket.song_count)))
            self.list_rows[name] = row

    def browse_input(self) -> None:
        selected = list(self.filedialog.askopenfilenames(filetypes=[("AniList / MAL / AMQ / AnisongDB exports", "*.json *.xml"), ("All files", "*.*")]))
        if not selected:
            return
        if len(selected) > 1 and any(Path(path).suffix.lower() != ".json" for path in selected):
            self.messagebox.showwarning("JSON files required", "Select one XML file by itself, or select multiple JSON files for a named group.", parent=self.root)
            return
        self.import_paths = selected
        self.path_var.set("; ".join(selected))

    def browse_output(self) -> None:
        selected = self.filedialog.askdirectory()
        if selected:
            self.output_var.set(selected)
            self.save_profile()

    def load_list(self) -> None:
        profile_name = self.profile_name_var.get().strip()
        if not profile_name:
            self.messagebox.showwarning("Profile name required", "Enter a profile name before importing a list.", parent=self.root)
            return
        if self.new_profile_mode and profile_name in _profile_names():
            self.messagebox.showerror("Profile name already exists", "Choose a different profile name before importing this list.", parent=self.root)
            return
        paths = self.import_paths or ([self.path_var.get().strip()] if self.path_var.get().strip() else [])
        if not paths:
            self.messagebox.showwarning("Export required", "Choose one or more JSON files, or one XML file, before loading.", parent=self.root)
            return
        if len(paths) > 1 and any(Path(path).suffix.lower() != ".json" for path in paths):
            self.messagebox.showwarning("JSON files required", "Multiple-file imports must contain JSON files only.", parent=self.root)
            return
        previous_path = self.collection.path if self.collection else ""
        try:
            if len(paths) > 1:
                group_name = self.simpledialog.askstring("JSON list name", "Enter a list name for this JSON file group:", parent=self.root)
                if not _clean(group_name):
                    return
                self.collection = parse_export_group(paths, group_name)
            else:
                self.collection = parse_export(paths[0])
        except Exception as exc:
            self.messagebox.showerror("Could not load list", str(exc), parent=self.root)
            return
        self.import_paths = [str(path) for path in paths]
        self.path_var.set("; ".join(self.import_paths))
        self.enabled_lists.update(self.collection.buckets.keys())
        if previous_path and os.path.normcase(os.path.abspath(previous_path)) != os.path.normcase(os.path.abspath(self.collection.path)):
            self.download_records = []
            self.current_manifest_path = ""
        self._populate_lists()
        self.profile_var.set(profile_name)
        self.save_profile()
        self.status_var.set(f"Loaded {self.collection.source}: {self.collection.total_entries:,} unique entries across {len(self.collection.buckets)} lists. Counts will be loaded automatically.")
        self._schedule_count_refresh()

    def _schedule_count_refresh(self) -> None:
        if not self.collection or not any(bucket.song_count is None for bucket in self.collection.buckets.values()):
            return
        types, categories = self._filters()
        if types and categories:
            self.status_var.set("Loaded list. Fetching song counts from AnisongDB…")
            if self.count_refresh_job:
                try:
                    self.root.after_cancel(self.count_refresh_job)
                except self.tk.TclError:
                    pass
            self.count_refresh_job = self.root.after(200, self.refresh_counts)

    def _selected_bucket(self) -> Optional[ListBucket]:
        if not self.collection:
            return None
        selected = self.list_tree.selection()
        if not selected:
            return None
        name = self.list_tree.item(selected[0], "values")[0]
        return self.collection.buckets.get(name)

    def _filters(self) -> tuple[list[str], list[str]]:
        types = [name for name, variable in (("opening", self.opening_var), ("ending", self.ending_var), ("insert", self.insert_var)) if variable.get()]
        categories = [name for name, variable in (("standard", self.standard_var), ("character", self.character_var), ("chanting", self.chanting_var), ("instrumental", self.instrumental_var), ("other", self.other_var)) if variable.get()]
        return types, categories

    def _filter_snapshot(self) -> tuple[int, int, str]:
        try:
            minimum = max(1924, int(self.year_min_var.get()))
            maximum = min(dt.datetime.now().year, int(self.year_max_var.get()))
        except (TypeError, ValueError):
            minimum, maximum = 1924, dt.datetime.now().year
        return minimum, maximum, self.season_var.get()

    def _date_filter(self, song: dict[str, Any], snapshot: Optional[tuple[int, int, str]] = None) -> bool:
        vintage = _clean(song.get("animeVintage"))
        match = re.search(r"(Winter|Spring|Summer|Fall)\s+(\d{4})", vintage, re.IGNORECASE)
        if not match:
            return True
        minimum, maximum, season_filter = snapshot or self._filter_snapshot()
        year = int(match.group(2))
        season = match.group(1).title()
        return minimum <= year <= maximum and (season_filter == "All" or season_filter == season)

    def _matching_songs(self, entries: list[AnimeEntry], types: list[str], categories: list[str], snapshot: Optional[tuple[int, int, str]] = None) -> list[dict[str, Any]]:
        if _collection_has_embedded_songs(self.collection):
            keys = {entry.key for entry in entries}
            matching: list[dict[str, Any]] = []
            for song in self.collection.songs:
                linked = song.get("linked_ids") or {}
                song_keys = {f"anilist:{linked.get('anilist')}", f"mal:{linked.get('myanimelist')}", f"source:AMQ:{linked.get('ann')}"}
                song_type = _clean(song.get("songType")).casefold()
                type_ok = ((song_type.startswith("opening") and "opening" in types)
                           or (song_type.startswith("ending") and "ending" in types)
                           or (song_type.startswith("insert") and "insert" in types)
                           or (not song_type.startswith(("opening", "ending", "insert")) and "insert" in types))
                category_ok = _clean(song.get("songCategory") or "standard").casefold() in categories
                if keys.intersection(song_keys) and type_ok and category_ok and self._date_filter(song, snapshot):
                    matching.append(song)
            return matching
        snapshot = snapshot or self._filter_snapshot()
        entry_keys = tuple(entry.key for entry in entries)
        filter_key = (id(self.collection), entry_keys, tuple(types), tuple(categories), snapshot)
        cached = self._song_query_cache.get(filter_key)
        if cached is not None:
            return list(cached)

        # A completed all-lists count refresh already fetched this same song
        # data. Reuse that superset for an individual list instead of making a
        # second network request when Custom Download is opened.
        all_entries = self.collection.all_entries() if self.collection else entries
        all_key = tuple(entry.key for entry in all_entries)
        all_filter_key = (id(self.collection), all_key, tuple(types), tuple(categories), snapshot)
        songs = self._song_query_cache.get(all_filter_key)
        if songs is None:
            songs = self.client.songs_for_entries(entries, types, categories)
            songs = [song for song in songs if self._date_filter(song, snapshot)]
            self._song_query_cache[filter_key] = list(songs)
            return list(songs)

        wanted_keys = set(entry_keys)
        matching = []
        for song in songs:
            linked = song.get("linked_ids") or {}
            song_keys = {
                f"anilist:{linked.get('anilist')}",
                f"mal:{linked.get('myanimelist')}",
                f"source:AMQ:{linked.get('ann')}",
            }
            if wanted_keys.intersection(song_keys):
                matching.append(song)
        self._song_query_cache[filter_key] = list(matching)
        return matching

    def _run_thread(self, target: Callable[[], None]) -> None:
        if self.busy:
            return
        self.busy = True
        threading.Thread(target=target, daemon=True).start()

    def _finish(self) -> None:
        self.busy = False

    def refresh_counts(self) -> None:
        self.count_refresh_job = None
        if not self.collection:
            self.messagebox.showinfo("Load a list first", "Choose an export and click Load list.", parent=self.root)
            return
        types, categories = self._filters()
        if not types or not categories:
            self.messagebox.showwarning("No song filters selected", "Select at least one song type and one category.", parent=self.root)
            return
        snapshot = self._filter_snapshot()
        if _collection_has_embedded_songs(self.collection):
            for bucket in self.collection.buckets.values():
                bucket.song_count = len(self._matching_songs(bucket.entries, types, categories, snapshot))
            self._update_rows("AMQ song counts loaded without AnisongDB requests.")
            return
        self.status_var.set("Fetching songs for all entries…")
        target_collection = self.collection

        def work() -> None:
            try:
                if self.collection is not target_collection:
                    return
                all_songs = self._matching_songs(target_collection.all_entries(), types, categories, snapshot)
                if self.collection is not target_collection:
                    return
                totals = count_songs_by_bucket(target_collection, all_songs)
                for name, bucket in target_collection.buckets.items():
                    bucket.song_count = totals.get(name, 0)
                self.root.after(
                    0,
                    lambda: self._update_rows(f"Song counts refreshed for {len(all_songs):,} matching songs.")
                    if self.collection is target_collection else None,
                )
            except Exception as exc:
                self.root.after(0, lambda: self._show_worker_error(str(exc)) if self.collection is target_collection else None)
            finally:
                self.root.after(0, self._finish)
        self._run_thread(work)

    def _update_rows(self, status: str) -> None:
        if not self.collection:
            return
        if not hasattr(self, "list_tree") or not self.list_tree.winfo_exists():
            return
        for name, bucket in self.collection.buckets.items():
            row = self.list_rows.get(name)
            if row:
                self.list_tree.item(row, values=(name, display_bucket_type(self.collection, bucket), len(bucket.entries), _fmt_count(bucket.song_count)))
        self.save_profile()
        self.status_var.set(status)

    def _show_worker_error(self, message: str) -> None:
        self.status_var.set("Operation failed.")
        self.messagebox.showerror("AnisongDB operation failed", message, parent=self.root)

    def _confirm_download(self, bucket_name: str, entries: list[AnimeEntry], songs: list[dict[str, Any]]) -> bool:
        if not songs:
            self.messagebox.showinfo("No songs found", f"No matching songs were found for {bucket_name} with the current filters.", parent=self.root)
            return False
        return self.messagebox.askyesno(
            "Confirm download",
            f"List: {bucket_name}\nEntries: {len(entries):,}\nSongs: {len(songs):,}\n\nExisting files will be skipped.\nDownload these songs to:\n{self.output_var.get()}?",
            parent=self.root,
        )

    def download_selected(self) -> None:
        bucket = self._selected_bucket()
        if not bucket:
            self.messagebox.showinfo("Choose a list", "Select a list row first.", parent=self.root)
            return
        self._start_download(bucket.name, bucket.entries)

    def custom_download(self, selected_bucket: Optional[ListBucket] = None) -> None:
        bucket = selected_bucket or self._selected_bucket()
        if not bucket:
            self.messagebox.showinfo("Choose a list", "Select a list row first.", parent=self.root)
            return
        types, categories = self._filters()
        if not types or not categories:
            self.messagebox.showwarning("No song filters selected", "Select at least one song type and one category.", parent=self.root)
            return
        if self.busy:
            self.status_var.set("Still preparing song counts. Try Custom Download again when that finishes.")
            self.messagebox.showinfo(
                "Song data is still loading",
                "The profile is still fetching song data. Custom Download will be ready as soon as that finishes.",
                parent=self.root,
            )
            return
        snapshot = self._filter_snapshot()
        self.status_var.set("Preparing custom song selection…")

        # Show feedback immediately.  Matching a large list may take a moment,
        # but the old flow kept the List Actions popup open until that work
        # completed, which looked like the first click had been ignored.
        preparing = self.tk.Toplevel(self.root)
        preparing.title(f"Custom Download — {bucket.name}")
        preparing.configure(bg=UI_PINK)
        preparing.overrideredirect(True)
        preparing.transient(self.root)
        preparing.grab_set()
        self._center_window(preparing, 620, 220)
        preparing_surface = self.tk.Frame(preparing, bg=UI_BACKGROUND)
        preparing_surface.pack(fill="both", expand=True, padx=4, pady=4)
        self.tk.Label(
            preparing_surface,
            text=f"Custom Download — {bucket.name}",
            bg=UI_BACKGROUND,
            fg=UI_TEXT,
            font=(self._ui_font_family, 18, "bold"),
        ).pack(pady=(30, 12))
        self.tk.Label(
            preparing_surface,
            text="Preparing the song list…",
            bg=UI_BACKGROUND,
            fg=UI_TEXT,
            font=(self._ui_font_family, 12),
        ).pack(pady=4)
        preparing_bar = self.ttk.Progressbar(preparing_surface, mode="indeterminate", length=360, style="Pink.Horizontal.TProgressbar")
        preparing_bar.pack(pady=(8, 20))
        preparing_bar.start(12)
        preparing.protocol("WM_DELETE_WINDOW", lambda: None)
        preparing.bind("<Escape>", lambda _event: None)
        self._activate_dialog(preparing)

        def show_ready(songs: list[dict[str, Any]]) -> None:
            if not preparing.winfo_exists():
                self._finish()
                return
            preparing_bar.stop()
            preparing.destroy()
            self._show_custom_dialog(bucket, songs)

        def show_failure(message: str) -> None:
            if preparing.winfo_exists():
                preparing_bar.stop()
                preparing.destroy()
            self._finish()
            self._show_worker_error(message)

        def work() -> None:
            try:
                songs = self._matching_songs(bucket.entries, types, categories, snapshot)
                self.root.after(0, lambda: show_ready(songs))
            except Exception as exc:
                self.root.after(0, lambda: show_failure(str(exc)))
        self._run_thread(work)

    def _show_custom_dialog(self, bucket: ListBucket, songs: list[dict[str, Any]]) -> None:
        self._finish()
        if not songs:
            self.messagebox.showinfo("No songs found", "No songs match the current filters.", parent=self.root)
            return
        dialog = self.tk.Toplevel(self.root)
        dialog.title(f"Custom Download — {bucket.name}")
        dialog.geometry("900x650")
        self._center_window(dialog, 900, 650)
        dialog.configure(bg=UI_PINK)
        dialog.overrideredirect(True)
        dialog.transient(self.root)
        dialog.grab_set()
        surface = self.tk.Frame(dialog, bg=UI_BACKGROUND)
        surface.pack(fill="both", expand=True, padx=4, pady=4)
        self.tk.Label(surface, text=f"Custom Download — {bucket.name}", bg=UI_BACKGROUND, fg=UI_TEXT, font=(self._ui_font_family, 20, "bold")).pack(pady=(12, 8))
        self.ttk.Label(surface, text="Search anime, song, artist, type, category, or any other displayed metadata:").pack(anchor="w", padx=10, pady=(2, 2))
        search_var = self.tk.StringVar()
        self.ttk.Entry(surface, textvariable=search_var).pack(fill="x", padx=10, pady=(0, 9))
        container = self.ttk.Frame(surface)
        container.pack(fill="both", expand=True, padx=10)
        tree = self.ttk.Treeview(container, columns=("selected", "song", "artist"), show="headings", selectmode="none", style="Download.Treeview")
        tree.heading("selected", text="")
        tree.heading("song", text="Song")
        tree.heading("artist", text="Artist")
        tree.column("selected", width=55, anchor="center", stretch=False)
        tree.column("song", width=560, anchor="w")
        tree.column("artist", width=230, anchor="w")
        scrollbar = self.ttk.Scrollbar(container, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=scrollbar.set)
        tree.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        tree.tag_configure("anime_header", background=UI_PANEL, foreground=UI_TEXT, font=(self._ui_font_family, 10, "bold"))
        tree.tag_configure("song_row", background=UI_PANEL_DARK, foreground=UI_TEXT)

        type_order = {"opening": 0, "ending": 1, "insert": 2}
        def song_sort_key(song: dict[str, Any]) -> tuple[Any, ...]:
            raw_type = _clean(song.get("songType")).casefold()
            order = next((value for name, value in type_order.items() if raw_type.startswith(name)), 3)
            number_match = re.search(r"(\d+)", raw_type)
            number = int(number_match.group(1)) if number_match else 0
            return order, number, _clean(song.get("songName")).casefold(), _clean(song.get("songArtist")).casefold()

        # Store each key once so rendering/searching never calls songs.index()
        # repeatedly. The old widget-per-song dialog became very slow for large
        # lists; a Treeview keeps the UI to one native row per visible item.
        groups: dict[str, list[tuple[str, dict[str, Any]]]] = {}
        used_keys: set[str] = set()
        for index, song in enumerate(songs):
            base_key = _clean(song.get("annSongId") or song.get("amqSongId") or song.get("_amq_song_number")) or f"song-{index}"
            key = base_key
            suffix = 2
            while key in used_keys:
                key = f"{base_key}-{suffix}"
                suffix += 1
            used_keys.add(key)
            anime = self._display_title(song)
            groups.setdefault(anime, []).append((key, song))
        selected: dict[str, bool] = {key: True for entries in groups.values() for key, _song in entries}
        item_to_key: dict[str, str] = {}
        item_to_anime: dict[str, str] = {}
        anime_to_item: dict[str, str] = {}
        render_job: Optional[str] = None

        def marker(value: bool) -> str:
            return "☑" if value else "☐"

        def update_anime_marker(anime: str) -> None:
            item = anime_to_item.get(anime)
            if not item:
                return
            values = [selected[key] for key, _song in groups[anime]]
            tree.set(item, "selected", marker(all(values)))

        def render() -> None:
            nonlocal render_job
            render_job = None
            for item in tree.get_children(""):
                tree.delete(item)
            item_to_key.clear()
            item_to_anime.clear()
            anime_to_item.clear()
            query = search_var.get().casefold().strip()
            for anime in sorted(groups, key=str.casefold):
                all_songs = groups[anime]
                anime_matches = bool(query and query in anime.casefold())
                visible_songs = [
                    (key, song) for key, song in all_songs
                    if not query or anime_matches or query in " ".join(str(value) for value in song.values()).casefold()
                ]
                if not visible_songs:
                    continue
                anime_iid = f"anime:{len(anime_to_item)}"
                anime_to_item[anime] = anime_iid
                tree.insert("", "end", iid=anime_iid, values=(marker(all(selected[key] for key, _song in all_songs)), anime, ""), tags=("anime_header",))
                for key, song in sorted(visible_songs, key=lambda pair: song_sort_key(pair[1])):
                    song_iid = f"song:{key}"
                    item_to_key[song_iid] = key
                    item_to_anime[song_iid] = anime
                    tree.insert("", "end", iid=song_iid, values=(marker(selected[key]), f"    {song.get('songType', 'Song')} — {song.get('songName', 'Untitled')}", song.get("songArtist", "")), tags=("song_row",))

        def on_click(event: Any) -> str:
            item = tree.identify_row(event.y)
            if not item:
                return "break"
            if item in item_to_key:
                key = item_to_key[item]
                selected[key] = not selected[key]
                tree.set(item, "selected", marker(selected[key]))
                update_anime_marker(item_to_anime[item])
            elif item.startswith("anime:"):
                anime = next((name for name, iid in anime_to_item.items() if iid == item), "")
                if anime:
                    value = not all(selected[key] for key, _song in groups[anime])
                    for key, _song in groups[anime]:
                        selected[key] = value
                    tree.set(item, "selected", marker(value))
                    for song_iid, key in item_to_key.items():
                        if item_to_anime.get(song_iid) == anime:
                            tree.set(song_iid, "selected", marker(value))
            return "break"

        def on_mousewheel(event: Any) -> str:
            delta = int(event.delta / 120) if event.delta else 0
            tree.yview_scroll(-delta if delta else (-1 if event.delta > 0 else 1), "units")
            return "break"

        tree.bind("<Button-1>", on_click)
        tree.bind("<MouseWheel>", on_mousewheel)
        tree.bind("<Button-4>", lambda _event: tree.yview_scroll(-1, "units"))
        tree.bind("<Button-5>", lambda _event: tree.yview_scroll(1, "units"))

        def schedule_render(*_args: Any) -> None:
            nonlocal render_job
            if render_job:
                dialog.after_cancel(render_job)
            render_job = dialog.after(120, render)

        search_var.trace_add("write", schedule_render)
        render()
        buttons = self.ttk.Frame(surface)
        buttons.pack(fill="x", padx=10, pady=10)
        def select_all() -> None:
            for key in selected:
                selected[key] = True
            render()
        def deselect_all() -> None:
            for key in selected:
                selected[key] = False
            render()
        self.ttk.Button(buttons, text="Select all", command=select_all).pack(side="left")
        self.ttk.Button(buttons, text="Deselect all", command=deselect_all).pack(side="left", padx=6)
        def accept() -> None:
            selected_songs = [song for entries in groups.values() for key, song in entries if selected[key]]
            if not selected_songs:
                self.messagebox.showinfo("No songs selected", "Select at least one song.", parent=self.root)
                return
            dialog.destroy()
            self._ask_and_download(bucket.name + " (custom selection)", bucket.entries, selected_songs)
        self.ttk.Button(buttons, text="Continue", command=accept).pack(side="right")
        self.ttk.Button(buttons, text="Cancel", command=dialog.destroy).pack(side="right", padx=6)
        self._activate_dialog(dialog)

    def _start_download(self, bucket_name: str, entries: list[AnimeEntry]) -> None:
        types, categories = self._filters()
        if not types or not categories:
            self.messagebox.showwarning("No song filters selected", "Select at least one song type and one category.", parent=self.root)
            return
        snapshot = self._filter_snapshot()
        self.status_var.set("Looking up matching songs…")

        def work() -> None:
            try:
                songs = self._matching_songs(entries, types, categories, snapshot)
                self.root.after(0, lambda: self._ask_and_download(bucket_name, entries, songs))
            except Exception as exc:
                self.root.after(0, lambda: self._show_worker_error(str(exc)))
                self.root.after(0, self._finish)
        self._run_thread(work)

    def _ask_and_download(self, bucket_name: str, entries: list[AnimeEntry], songs: list[dict[str, Any]]) -> None:
        if not self._confirm_download(bucket_name, entries, songs):
            self._finish()
            return
        self.status_var.set(f"Downloading {len(songs):,} songs…")
        output_dir = self.output_var.get()
        existing = SongDownloader(output_dir, self.media_var.get()).existing_count(songs)
        cancel_event = threading.Event()
        progress_window = self._progress_window(bucket_name, len(songs), existing, cancel_event)

        def work() -> None:
            try:
                downloader = SongDownloader(output_dir, self.media_var.get())

                def progress(done: int, total: int, record: dict[str, Any], status: str) -> None:
                    self.root.after(0, lambda: self._update_progress(progress_window, done, total, record, status))

                records = downloader.download(songs, progress, cancel_event)
                merged_by_id: dict[str, dict[str, Any]] = {}
                for record in [*self.download_records, *records]:
                    record_id = _clean(record.get("annSongId") or record.get("amqSongId") or record.get("download_path"))
                    if record_id:
                        merged_by_id[record_id] = record
                merged_records = list(merged_by_id.values())
                json_path, csv_path = write_manifest(merged_records, output_dir)
                self.root.after(0, lambda: self._finish_download(merged_records, json_path, csv_path, cancelled=cancel_event.is_set()))
                self.root.after(0, lambda: self._close_progress(progress_window))
            except Exception as exc:
                self.root.after(0, lambda: self._show_worker_error(str(exc)))
                self.root.after(0, lambda: self._close_progress(progress_window))
            finally:
                self.root.after(0, self._finish)
        threading.Thread(target=work, daemon=True).start()

    def _progress_window(self, name: str, total: int, existing: int = 0, cancel_event: Optional[threading.Event] = None) -> Any:
        dialog = self.tk.Toplevel(self.root)
        dialog.title("Downloading songs")
        dialog.configure(bg=UI_PINK)
        dialog.overrideredirect(True)
        dialog.transient(self.root)
        dialog.grab_set()
        self._center_window(dialog, 700, 260)
        surface = self.tk.Frame(dialog, bg=UI_BACKGROUND)
        surface.pack(fill="both", expand=True, padx=4, pady=4)
        self.tk.Label(surface, text=f"Downloading — {name}", bg=UI_BACKGROUND, fg=UI_TEXT, font=(self._ui_font_family, 17, "bold")).pack(pady=(25, 12))
        progress = self.ttk.Progressbar(surface, maximum=max(total, 1), length=600, style="Pink.Horizontal.TProgressbar")
        progress.pack(fill="x", padx=30, pady=8)
        status = self.tk.StringVar(value=f"Scanning files… {existing:,} already present; they will be skipped.")
        self.ttk.Label(surface, textvariable=status).pack(anchor="center", padx=15, pady=(2, 10))

        def request_cancel() -> None:
            if cancel_event is None or cancel_event.is_set():
                return
            if self.messagebox.askyesno(
                "Cancel download",
                "Cancel this download? The current file may finish first, and completed files will be kept.",
                parent=dialog,
            ):
                cancel_event.set()
                cancel_button._set_kanon_enabled(False)
                status.set("Cancelling… finishing the current file.")

        cancel_button = self._make_kanon_button(surface, "Cancel", request_cancel, width=95, height=34, font_size=9)
        cancel_button.pack(pady=(0, 18))
        dialog.progress_bar, dialog.progress_status, dialog.cancel_event = progress, status, cancel_event
        dialog.protocol("WM_DELETE_WINDOW", lambda: None)
        dialog.bind("<Escape>", lambda _event: request_cancel())
        self._activate_dialog(dialog)
        return dialog

    def _update_progress(self, dialog: Any, done: int, total: int, record: dict[str, Any], status: str) -> None:
        if dialog.winfo_exists():
            dialog.progress_bar["value"] = done
            dialog.progress_status.set(f"{done:,}/{total:,} · {status} · {song_label(record)}")
        self.status_var.set(f"Downloading {done:,}/{total:,}: {status}")

    def _close_progress(self, dialog: Any) -> None:
        if dialog.winfo_exists():
            try:
                dialog.grab_release()
            except self.tk.TclError:
                pass
            dialog.destroy()

    def _finish_download(self, records: list[dict[str, Any]], json_path: Path, csv_path: Path, cancelled: bool = False) -> None:
        self.download_records = records
        self.current_manifest_path = str(json_path)
        self.save_profile()
        if cancelled:
            self.status_var.set(f"Download cancelled. Completed files were kept; metadata saved to {json_path.name}.")
        else:
            self.status_var.set(f"Finished. Metadata: {json_path.name} and {csv_path.name}; profile history updated.")

    def _profile_song_records(self) -> list[dict[str, Any]]:
        records: list[dict[str, Any]] = []
        seen: set[str] = set()
        for song in [*(self.collection.songs if self.collection else []), *self.download_records]:
            key = _clean(song.get("annSongId") or song.get("amqSongId") or song.get("_amq_song_number") or song.get("download_path"))
            if key and key not in seen:
                seen.add(key)
                records.append(song)
        return records

    def _merge_imported_collection(self, incoming: AnimeCollection) -> None:
        if not self.collection:
            self.collection = incoming
        else:
            for name, incoming_bucket in incoming.buckets.items():
                bucket = self.collection.buckets.get(name)
                if bucket is None:
                    self.collection.buckets[name] = incoming_bucket
                else:
                    for entry in incoming_bucket.entries:
                        bucket.add(entry)
                    if incoming_bucket.song_count is not None:
                        bucket.song_count = (bucket.song_count or 0) + incoming_bucket.song_count
            seen = {_clean(song.get("annSongId") or song.get("amqSongId") or song.get("_amq_song_number") or song.get("download_path")) for song in self.collection.songs}
            for index, song in enumerate(incoming.songs):
                key = _clean(song.get("annSongId") or song.get("amqSongId") or song.get("_amq_song_number") or song.get("download_path")) or f"song-{len(seen)}-{index}"
                if key not in seen:
                    seen.add(key)
                    self.collection.songs.append(song)
            if self.collection.source != incoming.source:
                self.collection.source = "Mixed"
            self.collection.path = ";".join(part for part in (self.collection.path, incoming.path) if part)
        self.enabled_lists.update(incoming.buckets.keys())

    def _show_add_list_dialog(self) -> None:
        dialog = self.tk.Toplevel(self.root)
        dialog.title("Add List")
        dialog.configure(bg=UI_PINK)
        dialog.overrideredirect(True)
        dialog.transient(self.root)
        dialog.grab_set()
        self._center_window(dialog, 900, 350)
        surface = self.tk.Frame(dialog, bg=UI_BACKGROUND)
        surface.pack(fill="both", expand=True, padx=4, pady=4)
        self.tk.Label(surface, text="Add List", bg=UI_BACKGROUND, fg=UI_TEXT, font=(self._ui_font_family, 24, "bold")).pack(pady=(21, 18))
        selected_paths: list[str] = []
        display_var = self.tk.StringVar()
        file_frame = self.ttk.LabelFrame(surface, text="AniList/MAL/AMQ/AnisongDB Export File")
        file_frame.pack(fill="x", padx=40, pady=6)
        self.ttk.Entry(file_frame, textvariable=display_var).pack(side="left", fill="x", expand=True, padx=7, pady=8)
        def browse() -> None:
            paths = list(self.filedialog.askopenfilenames(filetypes=[("AniList / MAL / AMQ / AnisongDB exports", "*.json *.xml"), ("All files", "*.*")]))
            if not paths:
                return
            if len(paths) > 1 and any(Path(path).suffix.lower() != ".json" for path in paths):
                self.messagebox.showwarning("JSON files required", "Select one XML file by itself, or multiple JSON files for a named group.", parent=dialog)
                return
            selected_paths[:] = paths
            display_var.set("; ".join(paths))
        self.ttk.Button(file_frame, text="Browse…", command=browse).pack(side="left", padx=3, pady=5)
        self.tk.Label(surface, text="Multiple JSON files are merged into one named list.", bg=UI_BACKGROUND, fg=UI_MUTED, font=(self._ui_font_family, 11)).pack(anchor="w", padx=42, pady=(8, 18))
        actions = self.ttk.Frame(surface)
        actions.pack(fill="x", padx=40, pady=8)
        def add() -> None:
            paths = selected_paths or [part.strip() for part in display_var.get().split(";") if part.strip()]
            if not paths:
                self.messagebox.showwarning("Export required", "Choose an export file first.", parent=dialog)
                return
            try:
                if len(paths) > 1:
                    list_name = self.simpledialog.askstring("JSON list name", "Enter a list name for this JSON file group:", parent=dialog)
                    if not _clean(list_name):
                        return
                    incoming = parse_export_group(paths, list_name)
                else:
                    incoming = parse_export(paths[0])
            except Exception as exc:
                self.messagebox.showerror("Could not add list", str(exc), parent=dialog)
                return
            self._merge_imported_collection(incoming)
            self.import_paths = list(dict.fromkeys([*self.import_paths, *paths]))
            self.path_var.set("; ".join(self.import_paths))
            self.save_profile()
            dialog.destroy()
            self.edit_profile()
        self.ttk.Button(actions, text="Cancel", command=dialog.destroy).pack(side="right", padx=(8, 0))
        self.ttk.Button(actions, text="Add List", command=add).pack(side="right")
        dialog.protocol("WM_DELETE_WINDOW", dialog.destroy)
        dialog.bind("<Escape>", lambda _event: dialog.destroy())
        self._activate_dialog(dialog)

    def _profile_export_payload(self, active_only: bool) -> Optional[dict[str, Any]]:
        if not self.collection:
            return None
        if active_only:
            buckets = [bucket for name, bucket in self.collection.buckets.items() if name in self.enabled_lists]
            if not buckets:
                return None
        else:
            buckets = list(self.collection.buckets.values())

        records = self._profile_song_records()
        if active_only:
            records = [
                song for song in records
                if _record_key(song) not in self.excluded_song_keys
                and any(self._record_matches_bucket(song, bucket) for bucket in buckets)
            ]
        return {
            "format": "AMQ Trainer Profile Export",
            "version": 1,
            "profile_name": self.profile_var.get(),
            "scope": "active" if active_only else "all",
            "lists": [
                {
                    "name": bucket.name,
                    "kind": bucket.kind,
                    "song_count": bucket.song_count,
                    "entries": [asdict(entry) for entry in bucket.entries],
                }
                for bucket in buckets
            ],
            "songs": records,
        }

    def _export_profile(self, active_only: bool) -> None:
        payload = self._profile_export_payload(active_only)
        if payload is None:
            self.messagebox.showinfo("Nothing to export", "This profile has no active lists to export.", parent=self.root)
            return
        scope = "active lists and their songs" if active_only else "all lists and songs"
        if not self.messagebox.askyesno(
            "Export Profile",
            f"Export {scope} for profile '{self.profile_var.get()}'?",
            parent=self.root,
        ):
            return
        initial = _safe_filename(f"{self.profile_var.get()} - AMQ Trainer Profile.json")
        target = self.filedialog.asksaveasfilename(
            title="Export Profile",
            defaultextension=".json",
            initialfile=initial,
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")],
        )
        if not target:
            return
        try:
            with open(target, "w", encoding="utf-8") as handle:
                json.dump(payload, handle, ensure_ascii=False, indent=2)
        except OSError as exc:
            self.messagebox.showerror("Could not export profile", str(exc), parent=self.root)
            return
        self.status_var.set(f"Exported profile to {Path(target).name}.")
        self.messagebox.showinfo("Profile exported", f"Profile exported to {Path(target).name}.", parent=self.root)

    def _show_export_profile_popup(self) -> None:
        self._open_choice_popup(
            "Export Profile",
            [
                ("Active Lists & Songs", lambda: self._export_profile(True)),
                ("All Lists & Songs", lambda: self._export_profile(False)),
            ],
            hover_options=True,
            show_back_button=True,
            back_command=self.edit_profile,
        )

    def edit_profile(self) -> None:
        if not self.collection:
            self.messagebox.showinfo("No imported list", "Import a list before editing the profile.", parent=self.root)
            return
        self._suspend_menu_player()
        self._clear_content()
        dialog = self.tk.Frame(self.content, bg=UI_BACKGROUND)
        dialog.pack(fill="both", expand=True)
        self.tk.Label(dialog, text=f"Edit Profile — {self.profile_var.get()}", bg=UI_BACKGROUND, fg=UI_TEXT, font=(self._ui_font_family, 24, "bold")).place(relx=0.5, y=78, anchor="center")
        main = self.tk.Frame(dialog, bg=UI_BACKGROUND)
        main.place(x=180, y=150, width=1000, height=480)
        left = self.ttk.LabelFrame(main, text="Lists", width=250)
        left.pack(side="left", fill="y", padx=(0, 8))
        left.pack_propagate(False)
        right = self.ttk.LabelFrame(main, text="Songs")
        right.pack(side="left", fill="both", expand=True, padx=(8, 0))

        list_host = self.tk.Canvas(left, bg=UI_PANEL, highlightthickness=0)
        list_inner = self.ttk.Frame(list_host)
        list_window = list_host.create_window((0, 0), window=list_inner, anchor="nw")
        list_inner.bind("<Configure>", lambda _event: list_host.configure(scrollregion=list_host.bbox("all")))
        list_host.bind("<Configure>", lambda event: list_host.itemconfigure(list_window, width=event.width))
        list_host.pack(fill="both", expand=True, padx=8, pady=8)
        def scroll_lists(event: Any) -> str:
            delta = int(event.delta / 120) if getattr(event, "delta", 0) else 0
            list_host.yview_scroll(-delta if delta else (-1 if getattr(event, "delta", 0) > 0 else 1), "units")
            return "break"
        list_host.bind("<MouseWheel>", scroll_lists)
        list_inner.bind("<MouseWheel>", scroll_lists)
        list_host.bind("<Button-4>", lambda _event: list_host.yview_scroll(-1, "units"))
        list_host.bind("<Button-5>", lambda _event: list_host.yview_scroll(1, "units"))
        selected_list_name = [next(iter(self.collection.buckets), "")]
        list_vars: dict[str, Any] = {}
        list_button_widgets: dict[str, Any] = {}

        container = self.ttk.Frame(right)
        container.pack(fill="both", expand=True, padx=8, pady=8)
        song_tree = self.ttk.Treeview(
            container,
            columns=("selected", "song"),
            show="headings",
            selectmode="none",
            style="Download.Treeview",
        )
        song_tree.heading("selected", text="")
        song_tree.heading("song", text="Songs")
        song_tree.column("selected", width=34, minwidth=34, anchor="center", stretch=False)
        song_tree.column("song", width=680, anchor="w", stretch=True)
        song_scrollbar = self.ttk.Scrollbar(container, orient="vertical", command=song_tree.yview)
        song_tree.configure(yscrollcommand=song_scrollbar.set)
        song_tree.pack(side="left", fill="both", expand=True)
        song_scrollbar.pack(side="right", fill="y")
        song_tree.tag_configure("anime_header", background=UI_PANEL, foreground=UI_TEXT, font=(self._ui_font_family, 10, "bold"))
        song_tree.tag_configure("song_row", background=UI_PANEL_DARK, foreground=UI_TEXT)
        song_vars: dict[str, Any] = {}
        current_songs: list[dict[str, Any]] = []
        current_song_keys: set[str] = set()
        current_song_records: dict[str, dict[str, Any]] = {}
        item_to_song_key: dict[str, str] = {}
        item_to_group_keys: dict[str, set[str]] = {}
        bucket_index_cache: dict[str, tuple[set[str], set[str]]] = {}
        record_index_cache: dict[str, tuple[set[str], set[str]]] = {}

        def title_key(value: Any) -> str:
            return re.sub(r"[^a-z0-9]+", "", _clean(value).casefold())

        def bucket_match_index(bucket: ListBucket) -> tuple[set[str], set[str]]:
            cached = bucket_index_cache.get(bucket.name)
            if cached is not None:
                return cached
            entry_keys = {entry.key for entry in bucket.entries}
            entry_titles: set[str] = set()
            for entry in bucket.entries:
                entry_titles.update(
                    key for key in (
                        title_key(entry.title),
                        title_key(entry.extra.get("title_english")),
                        title_key(entry.extra.get("title_romaji")),
                        title_key(entry.extra.get("title_native")),
                    ) if key
                )
            cached = (entry_keys, entry_titles)
            bucket_index_cache[bucket.name] = cached
            return cached

        def record_match_index(song: dict[str, Any]) -> tuple[set[str], set[str]]:
            cache_key = _record_key(song)
            cached = record_index_cache.get(cache_key)
            if cached is not None:
                return cached
            linked = song.get("linked_ids") or {}
            record_keys = {
                f"anilist:{linked.get('anilist')}",
                f"mal:{linked.get('myanimelist')}",
                f"source:AMQ:{linked.get('ann')}",
            }
            record_titles = {
                key for key in (
                    title_key(song.get("animeENName")),
                    title_key(song.get("animeJPName")),
                    *(title_key(value) for value in _clean(song.get("animeAltName")).split(",")),
                ) if key
            }
            cached = (record_keys, record_titles)
            record_index_cache[cache_key] = cached
            return cached

        def matches_bucket(song: dict[str, Any], bucket: ListBucket) -> bool:
            record_keys, record_titles = record_match_index(song)
            entry_keys, entry_titles = bucket_match_index(bucket)
            return bool(record_keys.intersection(entry_keys) or record_titles.intersection(entry_titles))

        def record_id(song: dict[str, Any], index: int = 0) -> str:
            return _record_key(song, index)

        def refresh_list_button_colors() -> None:
            for name, button in list_button_widgets.items():
                button.configure(style="Accent.TButton" if name == selected_list_name[0] else "TButton")

        def render(*_args: Any) -> None:
            nonlocal current_songs
            current_song_keys.clear()
            current_song_records.clear()
            item_to_song_key.clear()
            item_to_group_keys.clear()
            for item in song_tree.get_children(""):
                song_tree.delete(item)
            bucket = self.collection.buckets.get(selected_list_name[0])
            if not bucket:
                current_songs = []
                return
            current_songs = []
            for song in self._profile_song_records():
                if matches_bucket(song, bucket):
                    current_songs.append(song)
            groups: dict[str, list[dict[str, Any]]] = {}
            for song in current_songs:
                groups.setdefault(self._display_title(song), []).append(song)
            if not current_songs:
                song_tree.insert("", "end", values=("", "No downloaded/imported song records are stored for this list yet."), tags=("song_row",))
            for anime in sorted(groups, key=str.casefold):
                group_keys: list[str] = []
                for index, song in enumerate(groups[anime]):
                    key = record_id(song, index)
                    current_song_keys.add(key)
                    current_song_records[key] = song
                    song_vars.setdefault(key, self.tk.BooleanVar(value=key not in self.excluded_song_keys))
                    group_keys.append(key)
                group_selected = bool(group_keys) and all(bool(song_vars[key].get()) for key in group_keys)
                group_item = song_tree.insert(
                    "", "end",
                    values=("☑" if group_selected else "☐", anime),
                    tags=("anime_header",),
                )
                item_to_group_keys[group_item] = set(group_keys)
                for index, song in enumerate(groups[anime]):
                    key = record_id(song, index)
                    item = song_tree.insert(
                        "", "end",
                        values=("☑" if song_vars[key].get() else "☐", self._display_song_label(song)),
                        tags=("song_row",),
                    )
                    item_to_song_key[item] = key
            if song_tree.get_children(""):
                song_tree.yview_moveto(0)

        def refresh_group_checkbox(key: str) -> None:
            for item, group_keys in item_to_group_keys.items():
                if key not in group_keys:
                    continue
                selected = bool(group_keys) and all(bool(song_vars[group_key].get()) for group_key in group_keys)
                song_tree.set(item, "selected", "☑" if selected else "☐")
                break

        def toggle_group_item(item: str) -> None:
            group_keys = item_to_group_keys.get(item)
            if not group_keys:
                return
            select_group = not all(bool(song_vars[key].get()) for key in group_keys)
            for key in group_keys:
                song_vars[key].set(select_group)
                if select_group:
                    self.excluded_song_keys.discard(key)
                else:
                    self.excluded_song_keys.add(key)
            song_tree.set(item, "selected", "☑" if select_group else "☐")
            for song_item, key in item_to_song_key.items():
                if key in group_keys:
                    song_tree.set(song_item, "selected", "☑" if select_group else "☐")
            self.save_profile()

        def toggle_song_item(item: str) -> None:
            key = item_to_song_key.get(item)
            if not key or key not in song_vars:
                return
            value = not bool(song_vars[key].get())
            song_vars[key].set(value)
            if value:
                self.excluded_song_keys.discard(key)
            else:
                self.excluded_song_keys.add(key)
            song_tree.set(item, "selected", "☑" if value else "☐")
            refresh_group_checkbox(key)
            self.save_profile()

        def click_song(event: Any) -> str:
            item = song_tree.identify_row(event.y)
            if item in item_to_group_keys:
                toggle_group_item(item)
            elif item in item_to_song_key:
                toggle_song_item(item)
            return "break"

        def scroll_songs(event: Any) -> str:
            delta = int(event.delta / 120) if getattr(event, "delta", 0) else 0
            song_tree.yview_scroll(-delta if delta else (-1 if getattr(event, "delta", 0) > 0 else 1), "units")
            return "break"

        song_tree.bind("<Button-1>", click_song)
        song_tree.bind("<MouseWheel>", scroll_songs)
        song_tree.bind("<Button-4>", lambda _event: song_tree.yview_scroll(-1, "units"))
        song_tree.bind("<Button-5>", lambda _event: song_tree.yview_scroll(1, "units"))
        def toggle_focused_song_row(_event: Any = None) -> str:
            item = song_tree.focus()
            if item in item_to_group_keys:
                toggle_group_item(item)
            elif item in item_to_song_key:
                toggle_song_item(item)
            return "break"

        song_tree.bind("<space>", toggle_focused_song_row)

        def select_list(name: str) -> None:
            selected_list_name[0] = name
            refresh_list_button_colors()
            render()

        def toggle_list(name: str) -> None:
            if list_vars[name].get():
                self.enabled_lists.add(name)
            else:
                self.enabled_lists.discard(name)
            self.save_profile()

        # Build the downloaded-membership index once.  The previous code
        # rescanned every profile record for every list while the editor was
        # being constructed, which was very noticeable on large profiles.
        downloaded_entry_keys: set[str] = set()
        for record in self._profile_song_records():
            path_text = _clean(record.get("download_path"))
            if not path_text:
                continue
            try:
                if not Path(path_text).is_file() or Path(path_text).stat().st_size <= 0:
                    continue
            except OSError:
                continue
            linked = record.get("linked_ids") or {}
            downloaded_entry_keys.update({
                f"anilist:{linked.get('anilist')}",
                f"mal:{linked.get('myanimelist')}",
                f"source:AMQ:{linked.get('ann')}",
            })

        for name in self.collection.buckets:
            row = self.ttk.Frame(list_inner)
            row.pack(fill="x", pady=3)
            bucket_keys = {entry.key for entry in self.collection.buckets[name].entries}
            variable = self.tk.BooleanVar(value=name in self.enabled_lists and bool(bucket_keys.intersection(downloaded_entry_keys)))
            list_vars[name] = variable
            check = self.ttk.Checkbutton(row, variable=variable, command=lambda list_name=name: toggle_list(list_name))
            check.pack(side="left", padx=(2, 3))
            button = self.ttk.Button(row, text=name, command=lambda list_name=name: select_list(list_name))
            button.pack(side="left", fill="x", expand=True)
            list_button_widgets[name] = button
            # Bind the row and button explicitly as well as using the ttk
            # command. This keeps list selection reliable when the embedded
            # frame is hosted inside a Canvas window.
            button.bind("<Button-1>", lambda _event, list_name=name: select_list(list_name), add="+")
            row.bind("<MouseWheel>", scroll_lists, add="+")
            check.bind("<MouseWheel>", scroll_lists, add="+")
            button.bind("<MouseWheel>", scroll_lists, add="+")
            row.bind("<Button-4>", lambda _event: list_host.yview_scroll(-1, "units"), add="+")
            row.bind("<Button-5>", lambda _event: list_host.yview_scroll(1, "units"), add="+")
            check.bind("<Button-4>", lambda _event: list_host.yview_scroll(-1, "units"), add="+")
            check.bind("<Button-5>", lambda _event: list_host.yview_scroll(1, "units"), add="+")
            button.bind("<Button-4>", lambda _event: list_host.yview_scroll(-1, "units"), add="+")
            button.bind("<Button-5>", lambda _event: list_host.yview_scroll(1, "units"), add="+")
        refresh_list_button_colors()

        def current_bucket() -> Optional[ListBucket]:
            return self.collection.buckets.get(selected_list_name[0]) if self.collection else None

        def delete_current_list() -> None:
            bucket = current_bucket()
            if not bucket:
                return
            if not self.messagebox.askyesno("Delete list", f"Delete '{bucket.name}' from this profile? This cannot be undone.", parent=self.root):
                return
            delete_songs = self.messagebox.askyesno("Delete downloaded songs?", "Also delete downloaded songs associated with this list? Choose No to keep the downloaded files.", parent=self.root)
            if delete_songs:
                def belongs(song: dict[str, Any]) -> bool:
                    return matches_bucket(song, bucket)
                removed = [song for song in [*self.download_records, *(self.collection.songs if self.collection else [])] if belongs(song)]
                for song in removed:
                    path = Path(_clean(song.get("download_path"))) if _clean(song.get("download_path")) else None
                    if path:
                        try:
                            if path.is_file():
                                path.unlink()
                        except OSError:
                            pass
                self.download_records = [song for song in self.download_records if not belongs(song)]
                self.collection.songs = [song for song in self.collection.songs if not belongs(song)]
            self.collection.buckets.pop(bucket.name, None)
            self.enabled_lists.discard(bucket.name)
            self.save_profile()
            self.edit_profile()

        def open_list_actions() -> None:
            self._open_choice_popup("List Actions", [
                ("Add List", self._show_add_list_dialog),
                ("Download List", lambda: self.custom_download(current_bucket())),
                ("Delete List", delete_current_list),
            ], hover_options=True, show_back_button=True)

        list_action_frame = self.ttk.Frame(dialog)
        list_action_frame.place(x=180, y=650, width=250, height=50)
        song_buttons = self.ttk.Frame(dialog)
        song_buttons.place(x=446, y=650, width=500, height=50)
        self.ttk.Button(list_action_frame, text="List Actions", command=open_list_actions).pack(side="left")
        def set_selected(value: bool) -> None:
            for key in current_song_keys:
                if key in song_vars:
                    song_vars[key].set(value)
                    if value:
                        self.excluded_song_keys.discard(key)
                    else:
                        self.excluded_song_keys.add(key)
            for item, key in item_to_song_key.items():
                song_tree.set(item, "selected", "☑" if value else "☐")
            for item in item_to_group_keys:
                song_tree.set(item, "selected", "☑" if value else "☐")
            self.save_profile()
        self.ttk.Button(song_buttons, text="Select All", command=lambda: set_selected(True)).pack(side="left", padx=6)
        self.ttk.Button(song_buttons, text="Deselect All", command=lambda: set_selected(False)).pack(side="left", padx=6)
        def delete_selected() -> None:
            selected = {key for key in current_song_keys if key in song_vars and song_vars[key].get()}
            if not selected:
                self.messagebox.showinfo("No entries selected", "Select entries to delete first.", parent=self.root)
                return
            if not self.messagebox.askyesno("Confirm deletion", f"Confirm deleting {len(selected)} entries from the profile? This action cannot be undone.", parent=self.root):
                return
            selected_record_ids = {_record_key(current_song_records[key]) for key in selected if key in current_song_records}
            self.download_records = [song for song in self.download_records if _record_key(song) not in selected_record_ids]
            self.collection.songs = [song for song in self.collection.songs if _record_key(song) not in selected_record_ids]
            self.save_profile()
            song_vars.clear()
            render()
        self.ttk.Button(song_buttons, text="Delete", command=delete_selected).pack(side="left", padx=6)
        self.ttk.Button(dialog, text="Export Profile", command=self._show_export_profile_popup).place(x=1020, y=650, width=160, height=50)
        back_area = self.tk.Frame(dialog, bg=UI_BACKGROUND, cursor=self._app_cursor)
        back_area.place(x=0, y=0, width=160, height=145)
        back = self.tk.Label(back_area, image=self._ui_image("Elements/back-button.png"), bg=UI_BACKGROUND, cursor=self._app_cursor)
        back.place(x=25, y=22)
        back_area.bind("<Button-1>", lambda _event: self._build_profile_home())
        back.bind("<Button-1>", lambda _event: self._build_profile_home())
        render()


def cli_main(args: argparse.Namespace) -> int:
    collection = parse_export(args.file)
    print(f"Source: {collection.source}")
    print(f"Unique entries: {collection.total_entries}")
    for bucket in collection.buckets.values():
        print(f"{bucket.name}\t{display_bucket_type(collection, bucket)}\t{len(bucket.entries)} entries")
    if args.summary:
        client = AnisongDBClient()
        types = list(SONG_TYPES)
        categories = list(SONG_CATEGORIES)
        songs = collection.songs if _collection_has_embedded_songs(collection) else client.songs_for_entries(collection.all_entries(), types, categories)
        totals = count_songs_by_bucket(collection, songs)
        print("\nSong totals:")
        for bucket in collection.buckets.values():
            print(f"{bucket.name}\t{totals.get(bucket.name, 0)} songs")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("file", nargs="?", help="AniList .json or MAL .xml export")
    parser.add_argument("--summary", action="store_true", help="Print AnisongDB song totals as well as entry totals")
    args = parser.parse_args()
    if args.file:
        return cli_main(args)
    try:
        import tkinter as tk
    except ImportError:
        print("Tkinter is not available. Pass an export path to use the summary CLI.", file=sys.stderr)
        return 2
    root = tk.Tk()
    App(root)
    root.mainloop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
