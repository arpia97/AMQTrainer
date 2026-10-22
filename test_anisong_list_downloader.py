import json
import tempfile
import unittest
import xml.etree.ElementTree as ET
from pathlib import Path

from anisong_list_downloader import AnimeCollection, AnimeEntry, LibraryIndex, ListBucket, SongDownloader, _collection_from_dict, _collection_to_dict, count_songs_by_bucket, display_bucket_type, parse_anilist, parse_mal, parse_export, parse_export_group, write_manifest


class ParserTests(unittest.TestCase):
    def temp_dir(self):
        return tempfile.TemporaryDirectory(dir=Path.cwd())

    def test_anilist_status_and_custom_membership_are_deduplicated(self):
        payload = {
            "MediaListCollection": {
                "lists": [
                    {"name": "Watching", "isCustomList": False, "entries": [{"mediaId": 1, "status": "CURRENT", "customLists": {"Favorites": True}, "media": {"id": 1, "idMal": 101, "title": {"romaji": "Example"}}}]},
                    {"name": "Favorites", "isCustomList": True, "entries": [{"mediaId": 1, "status": "CURRENT", "customLists": {"Favorites": True}, "media": {"id": 1, "idMal": 101, "title": {"romaji": "Example"}}}]},
                ]
            }
        }
        with self.temp_dir() as directory:
            path = Path(directory) / "list.json"
            with open(path, "w", encoding="utf-8") as handle:
                json.dump(payload, handle)
            collection = parse_anilist(path)
        self.assertEqual(collection.buckets["Watching"].entries[0].title, "Example")
        self.assertEqual(len(collection.buckets["Favorites"].entries), 1)
        self.assertEqual(collection.total_entries, 1)

    def test_mal_status_and_tags(self):
        root = ET.Element("myanimelist")
        anime = ET.SubElement(root, "anime")
        ET.SubElement(anime, "series_animedb_id").text = "42"
        ET.SubElement(anime, "series_title").text = "Example"
        ET.SubElement(anime, "my_status").text = "Completed"
        ET.SubElement(anime, "my_tags").text = "Favorites, 2026"
        with self.temp_dir() as directory:
            path = Path(directory) / "list.xml"
            with open(path, "wb") as handle:
                ET.ElementTree(root).write(handle, encoding="utf-8", xml_declaration=True)
            collection = parse_mal(path)
        self.assertEqual(len(collection.buckets["Completed"].entries), 1)
        self.assertEqual(collection.buckets["Tag: Favorites"].entries[0].mal_id, 42)
        self.assertEqual(collection.total_entries, 1)

    def test_manifest_writes_json_and_csv(self):
        with self.temp_dir() as directory:
            json_path, csv_path = write_manifest([{"annId": 1, "songName": "Example", "download_status": "downloaded"}], directory)
            self.assertTrue(json_path.exists())
            self.assertTrue(csv_path.exists())

    def test_relative_media_filename_is_normalized(self):
        downloader = SongDownloader(Path.cwd())
        url, key = downloader._media_url({"audio": "qi299l.mp3"})
        self.assertEqual(url, "https://naedist.animemusicquiz.com/qi299l.mp3")
        self.assertEqual(key, "audio")

    def test_amq_song_export_is_detected_and_normalized(self):
        payload = {"songs": [{"songNumber": 1, "songInfo": {"annId": 7, "annSongId": 8, "animeNames": {"english": "Example"}, "siteIds": {"malId": 42, "aniListId": 99}, "type": 2, "typeNumber": 1, "songName": "Ending", "artist": "Artist", "vintage": "Winter 2024"}, "videoUrl": "https://naedist.animemusicquiz.com/example.mp3"}]}
        with self.temp_dir() as directory:
            path = Path(directory) / "amq.json"
            path.write_text(json.dumps(payload), encoding="utf-8")
            collection = parse_export(path)
        self.assertEqual(collection.source, "AMQ")
        self.assertEqual(collection.songs[0]["songType"], "Ending 1")
        self.assertEqual(collection.songs[0]["linked_ids"]["myanimelist"], 42)

    def test_anisongdb_song_list_export_is_detected_and_normalized(self):
        payload = [{
            "annId": 7,
            "annSongId": 8,
            "animeENName": "Example",
            "animeJPName": "Example Romaji",
            "animeAltName": ["Example Alt"],
            "linked_ids": {"myanimelist": 42, "anilist": 99},
            "songType": "Ending 1",
            "songCategory": "Standard",
            "songName": "Ending",
            "songArtist": "Artist",
            "audio": "example.mp3",
        }]
        with self.temp_dir() as directory:
            path = Path(directory) / "anisongdb.json"
            path.write_text(json.dumps(payload), encoding="utf-8")
            collection = parse_export(path)
        self.assertEqual(collection.source, "AniSongDB")
        self.assertEqual(collection.songs[0]["animeAltName"], "Example Alt")
        self.assertEqual(collection.songs[0]["audio"], "example.mp3")
        self.assertEqual(collection.buckets["AniSongDB Export"].song_count, 1)

    def test_multiple_json_exports_are_merged_into_named_group(self):
        def payload(identifier, title):
            return {"MediaListCollection": {"lists": [{"name": "Watching", "isCustomList": False, "entries": [{"mediaId": identifier, "status": "CURRENT", "media": {"id": identifier, "title": {"romaji": title}}}]}]}}
        with self.temp_dir() as directory:
            first = Path(directory) / "one.json"
            second = Path(directory) / "two.json"
            first.write_text(json.dumps(payload(1, "One")), encoding="utf-8")
            second.write_text(json.dumps(payload(2, "Two")), encoding="utf-8")
            collection = parse_export_group([first, second], "Grouped JSONs")
        self.assertEqual(list(collection.buckets), ["Grouped JSONs"])
        self.assertEqual(len(collection.buckets["Grouped JSONs"].entries), 2)

    def test_collection_song_records_round_trip(self):
        collection = AnimeCollection(source="AMQ", buckets={}, songs=[{"annSongId": 1, "songName": "Example"}])
        restored = _collection_from_dict(_collection_to_dict(collection))
        self.assertEqual(restored.songs[0]["songName"], "Example")

    def test_amq_trainer_profile_export_is_importable(self):
        payload = {
            "format": "AMQ Trainer Profile Export",
            "version": 1,
            "lists": [{
                "name": "Favorites",
                "kind": "custom",
                "entries": [{"source_id": "42", "title": "Example", "mal_id": 42, "source": "AniList"}],
            }],
            "songs": [{"annSongId": 7, "animeENName": "Example", "download_path": "example.mp3"}],
        }
        with self.temp_dir() as directory:
            path = Path(directory) / "profile.json"
            path.write_text(json.dumps(payload), encoding="utf-8")
            collection = parse_export(path)
        self.assertEqual(collection.source, "AMQ")
        self.assertEqual(list(collection.buckets), ["Favorites"])
        self.assertEqual(collection.songs[0]["annSongId"], 7)

    def test_anilist_song_counts_accept_mal_cross_links(self):
        entry = AnimeEntry(source_id="99", title="Example", anilist_id=99, mal_id=42, source="AniList")
        collection = AnimeCollection(source="AniList", buckets={"Watching": ListBucket("Watching", "status", [entry])})
        songs = [{"annSongId": 1, "linked_ids": {"myanimelist": 42}, "songName": "Opening"}]
        self.assertEqual(count_songs_by_bucket(collection, songs)["Watching"], 1)

    def test_displayed_bucket_types_are_user_facing(self):
        anilist = AnimeCollection(source="AniList", buckets={})
        mal = AnimeCollection(source="MAL", buckets={})
        self.assertEqual(display_bucket_type(anilist, ListBucket("Watching", "status")), "AniList")
        self.assertEqual(display_bucket_type(mal, ListBucket("Completed", "status")), "MAL")
        self.assertEqual(display_bucket_type(anilist, ListBucket("Favorites", "custom")), "Custom List")

    def test_autocomplete_prioritizes_prefix_contains_and_word_order(self):
        index = LibraryIndex([
            {"title": "My Hero Academia", "aliases": []},
            {"title": "Boku no Hero Academia", "aliases": []},
            {"title": "Kokoro", "aliases": []},
        ])
        self.assertEqual(index.search("my hero", 1), ["My Hero Academia"])
        self.assertIn("Boku no Hero Academia", index.search("hero boku"))
        self.assertIn("Kokoro", index.search("kororo"))

    def test_autocomplete_returns_matching_variant_and_english_variant(self):
        index = LibraryIndex([{"title": "English Anime Title", "aliases": ["Romaji Anime Title"]}])
        results = index.search("romaji")
        self.assertEqual(results[0], "Romaji Anime Title")
        self.assertIn("English Anime Title", results)

    def test_autocomplete_prefers_exact_and_shorter_shared_prefix(self):
        index = LibraryIndex([
            {"title": "Aikatsu Friends!", "aliases": []},
            {"title": "Aikatsu!", "aliases": []},
        ])
        self.assertEqual(index.search("Aikatsu!", 1), ["Aikatsu!"])
        self.assertEqual(index.search("Aikatsu", 1), ["Aikatsu!"])


if __name__ == "__main__":
    unittest.main()
