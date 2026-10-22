# AMQ Trainer

This is a Windows-friendly standalone Python/Tkinter tool for importing AniList JSON, MyAnimeList XML, or AMQ song exports, looking up matching entries in AnisongDB when needed, downloading selected songs, and saving metadata manifests for the later training-data pipeline.

The desktop UI uses a fixed 1280×720 design surface so the Kanon layout and its popups remain predictable while being refined.

It follows the same general workflow as the [AMQSongBrowser v1.1.1 release](https://github.com/nyamu-amq/AMQSongBrowser/releases/tag/v1.1.1) supplied as the foundation: import a list, query AnisongDB, choose songs, and download media. The implementation uses AnisongDB’s current batch API rather than scraping the website.

## Features

- Reads AniList `MediaListCollection` JSON exports.
- Reads MAL XML exports, including the old export format in the example file.
- Reads AMQ JSON song exports and uses their existing media URLs/metadata without querying AnisongDB.
- Normalizes status names to Watching, Completed, On Hold, Dropped, Planning, and Rewatching.
- Exposes AniList custom lists and MAL `my_tags` as selectable custom lists.
- Uses a Profile home with Select Profile, New Profile, Edit Profile, and Delete Profile actions.
- Provides a Play tab with Random, Learn, Review, and Flagged training modes.
- Shows Play mode selection and session settings inside the main 1280×720 page; active guessing sessions include Back to end the session and return to the mode screen.
- Provides a fixed Kanon-style Settings screen for English/Romaji titles, range-based play-mode controls, review difficulty, and profile-wide data management.
- Opens Settings as a full 1280×720 application page; global and session controls are persisted between launches.
- Provides configurable playback volume and per-session autoskip timing; Play sessions default to 20 songs.
- Stores local encounters, correct/incorrect guesses, and song flags per profile.
- Refreshes and caches AMQ's `libraryMasterList` once per day for title autocomplete.
- Shows entry and song totals for every detected list with the exact columns List, Type, # of Entries, and # of Songs.
- Collapses Download Filters by default; all song types/categories are initially enabled, with dynamic year range and season filters.
- Requires confirmation before a download begins.
- Offers a grouped Custom Download dialog with anime-level and individual-song selection plus metadata search.
- Filters Opening, Ending, and Insert songs, plus AnisongDB song categories.
- Uses Audio, HQ, or MQ as the preferred download link with fallback.
- Saves `download_manifest.json` and `download_manifest.csv` beside the downloaded audio.
- Keeps local profiles under `%LOCALAPPDATA%\\AniSongListDownloader\\profiles`, restoring the imported list, counts, settings, and download history when reopened.
- Remembers and automatically reopens the last-used profile at startup.
- Shows a startup loading overlay with progress while the saved profile is restored, and blocks navigation until startup is ready.
- Settings are stored under `%LOCALAPPDATA%\\AniSongListDownloader\\settings.json`; destructive operations ask for confirmation before affecting all profiles.
- Scans the output folder before downloading and reports/skips existing non-empty files.
- Provides an Edit Profile view with list navigation, grouped song records, and irreversible metadata-entry deletion confirmation.
- Uses AMQ-style title autocomplete: starts-with, contains, word-order, and fuzzy matching.
- Can print a read-only summary from the command line.

## Run on Windows

Install Python 3.10+ and run:

```powershell
python .\anisong_list_downloader.py
```

Or double-click `run_anisong_downloader.bat`.

## Build a standalone `.exe`

The program itself uses only Python’s standard library. To produce a Windows executable that can run without a browser or a Python install, install PyInstaller once:

```powershell
python -m pip install pyinstaller
```

Then double-click `build_standalone.bat`, or run:

```powershell
python -m PyInstaller --noconfirm --clean --onefile --windowed --add-data "dist\\Kanon-UI;Kanon-UI" --name AMQTrainer anisong_list_downloader.py
```

The executable will be created at `dist\AMQTrainer.exe`. A profile-enabled built copy is included in this workspace.

Choose **New Profile**, enter a unique profile name, choose an AniList/MAL/AMQ export, and click **Load list**. Select a detected list, then use **Download selected list** or **Custom Download**. Existing profiles can be reopened from **Select Profile**, with their lists/download metadata restored.

For a quick list-only summary:

```powershell
python .\anisong_list_downloader.py "C:\path\to\AnilistAnimeList.json"
```

For a network-backed song summary:

```powershell
python .\anisong_list_downloader.py "C:\path\to\AnilistAnimeList.json" --summary
```

The script has no third-party Python dependencies. It uses the standard library, including Tkinter, XML parsing, HTTP, CSV, and JSON support.

## API and download note

The app uses `https://anisongdb.com/api/mal_ids_request` for MAL IDs in both MAL and AniList exports, with a title-search fallback for AniList entries that have no MAL cross-link. The batch endpoint accepts up to 500 IDs per request. The API response is the source of the metadata manifest, including anime IDs, song IDs, song type, title, artist, composer, links, difficulty, and length.

AnisongDB may return media links as AMQ filenames rather than full URLs. The downloader resolves those filenames against `https://naedist.animemusicquiz.com/` and still accepts full URLs when present.

Use the downloader only for media you are permitted to save, and respect AnisongDB/AMQ service limits.
