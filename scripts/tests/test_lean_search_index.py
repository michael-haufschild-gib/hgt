from __future__ import annotations

import sqlite3
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

from lean_search_index import (  # noqa: E402
    DeclRow,
    LeanSearchIndex,
    MarkerRow,
    SourceFile,
    build_match_expression,
    split_identifier,
)


def _extract(source: SourceFile) -> tuple[list[DeclRow], list[MarkerRow]]:
    """Toy extractor: `kind name -- doc` per line, `TODO ...` lines are markers."""
    path = Path(source.abspath)
    decls: list[DeclRow] = []
    markers: list[MarkerRow] = []
    for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if line.startswith("TODO"):
            markers.append(MarkerRow(line=i, text=line))
            continue
        if not line.strip():
            continue
        head, _, doc = line.partition("--")
        kind, _, name = head.strip().partition(" ")
        decls.append(
            DeclRow(name=name.strip(), kind=kind, module=path.stem, line=i, doc=doc.strip())
        )
    return decls, markers


class SplitIdentifierTests(unittest.TestCase):
    def test_splits_namespace_snake_and_camel_components(self) -> None:
        self.assertEqual(
            split_identifier("Foo.evalJet_measuredClockInverseOperator_difference"),
            "Foo eval Jet measured Clock Inverse Operator difference",
        )

    def test_keeps_primes_and_digits_attached(self) -> None:
        self.assertEqual(split_identifier("q62_phiMero_norm_gap'"), "q62 phi Mero norm gap'")

    def test_keeps_acronym_runs_whole(self) -> None:
        self.assertEqual(split_identifier("ccmGNSSocket"), "ccm GNS Socket")


class MatchExpressionTests(unittest.TestCase):
    def test_emits_exact_and_prefix_clause_per_term(self) -> None:
        self.assertEqual(build_match_expression("clock jet"), '"clock" OR "clock"* OR "jet" OR "jet"*')

    def test_preserves_quoted_phrases(self) -> None:
        self.assertEqual(
            build_match_expression('"critical line" zero'),
            '"critical line" OR "zero" OR "zero"*',
        )

    def test_strips_fts5_operators_from_free_text(self) -> None:
        # `-`, `(`, `^` and `*` are FTS5 syntax; leaking them raises a query error.
        expression = build_match_expression("de-Branges (space) ^rank a*b")
        self.assertNotIn("-", expression)
        self.assertNotIn("(", expression)
        self.assertNotIn("^", expression)
        # Single letters stay exact: `a*` would match the whole corpus.
        self.assertEqual(
            expression,
            '"de" OR "de"* OR "Branges" OR "Branges"* OR "space" OR "space"*'
            ' OR "rank" OR "rank"* OR "a" OR "b"',
        )

    def test_keeps_non_ascii_terms(self) -> None:
        # Names and docstrings here are full of Greek; dropping it would make
        # `research "ξ zero"` silently return nothing for the ξ half.
        self.assertEqual(
            build_match_expression("ξ Λ_pos"),
            '"\u03be" OR "\u039b" OR "pos" OR "pos"*',
        )

    def test_keeps_subscripted_identifiers_whole(self) -> None:
        # unicode61 folds a subscript into the surrounding token, so `deckMap\u2081`
        # has to reach the index intact rather than split at the subscript.
        self.assertEqual(
            build_match_expression("deckMap\u2081_leftInverse"),
            '"deckMap\u2081" OR "deckMap\u2081"* OR "leftInverse" OR "leftInverse"*',
        )

    def test_empty_query_yields_no_expression(self) -> None:
        self.assertEqual(build_match_expression("   "), "")


class IndexLifecycleTests(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.tree = Path(self._tmp.name) / "tree"
        self.tree.mkdir()
        self.index = LeanSearchIndex(Path(self._tmp.name) / "search.db")
        self.addCleanup(self.index.close)
        self.addCleanup(self._tmp.cleanup)

    def _write(self, name: str, body: str) -> None:
        (self.tree / name).write_text(body, encoding="utf-8")

    def _sources(self) -> list[SourceFile]:
        out = []
        for p in sorted(self.tree.glob("*.txt")):
            stat = p.stat()
            out.append(SourceFile(p.name, str(p), stat.st_size, stat.st_mtime_ns))
        return out

    def _refresh(self):
        return self.index.refresh(self._sources(), _extract)

    def _names(self, query: str) -> list[str]:
        return [hit.name for hit in self.index.search_declarations(query, limit=10)]

    def _db_size(self) -> int:
        """Total on-disk footprint; in WAL mode most of it sits in the -wal file."""
        return sum(
            Path(str(self.index.db_path) + suffix).stat().st_size
            for suffix in ("", "-wal", "-shm")
            if Path(str(self.index.db_path) + suffix).exists()
        )

    def test_indexes_and_finds_a_declaration(self) -> None:
        self._write("a.txt", "theorem coerciveOperatorInverse -- a coercive operator inverse\n")
        stats = self._refresh()
        self.assertEqual((stats.changed, stats.removed, stats.wrote), (1, 0, True))
        self.assertEqual(self._names("coercive"), ["coerciveOperatorInverse"])
        self.assertEqual(self.index.counts()["declarations"], 1)

    def test_camel_components_are_searchable_as_words(self) -> None:
        self._write("a.txt", "theorem measuredClockInverseOperator_difference\n")
        self._refresh()
        self.assertEqual(self._names("clock inverse"), ["measuredClockInverseOperator_difference"])

    def test_exact_identifier_query_outranks_partial_matches(self) -> None:
        self._write(
            "a.txt",
            "theorem ladder_pin\n"
            "theorem ladder_pin_hermiteSide\n"
            "theorem pin_of_ladder\n",
        )
        self._refresh()
        self.assertEqual(self._names("ladder_pin")[0], "ladder_pin")

    def test_exact_term_outranks_prefix_only_match(self) -> None:
        self._write("a.txt", "theorem sumOfSquares -- sum of squares\ntheorem squareSummable\n")
        self._refresh()
        self.assertEqual(self._names("sum of squares")[0], "sumOfSquares")

    def test_second_refresh_is_a_no_op(self) -> None:
        self._write("a.txt", "theorem alpha\n")
        self._refresh()
        stats = self._refresh()
        self.assertEqual((stats.changed, stats.removed, stats.wrote), (0, 0, False))

    def test_edited_file_replaces_its_rows(self) -> None:
        self._write("a.txt", "theorem alpha\n")
        self._refresh()
        self._write("a.txt", "theorem beta\ntheorem gamma\n")
        stats = self._refresh()
        self.assertEqual(stats.changed, 1)
        self.assertEqual(self._names("alpha"), [])
        self.assertEqual(sorted(self._names("beta gamma")), ["beta", "gamma"])
        self.assertEqual(self.index.counts()["declarations"], 2)

    def test_deleted_file_drops_out_of_the_index(self) -> None:
        self._write("a.txt", "theorem alpha\n")
        self._write("b.txt", "theorem beta\n")
        self._refresh()
        (self.tree / "a.txt").unlink()
        stats = self._refresh()
        self.assertEqual((stats.changed, stats.removed), (0, 1))
        self.assertEqual(self._names("alpha"), [])
        self.assertEqual(self._names("beta"), ["beta"])
        self.assertEqual(self.index.counts()["files"], 1)

    def test_new_file_is_picked_up_without_touching_the_others(self) -> None:
        self._write("a.txt", "theorem alpha\n")
        self._refresh()
        self._write("b.txt", "theorem beta\n")
        stats = self._refresh()
        self.assertEqual(stats.changed, 1)
        self.assertEqual(self._names("beta"), ["beta"])

    def test_markers_are_indexed_and_ranked(self) -> None:
        self._write("a.txt", "theorem alpha\nTODO the prolate ladder rung is missing\n")
        self._refresh()
        hits = self.index.search_markers("prolate ladder", limit=5)
        self.assertEqual([(h.relpath, h.line) for h in hits], [("a.txt", 2)])

    def test_batching_commits_every_file_across_batches(self) -> None:
        self.index.batch_size = 2
        for i in range(5):
            self._write(f"f{i}.txt", f"theorem decl{i}\n")
        stats = self._refresh()
        self.assertEqual(stats.changed, 5)
        self.assertEqual(self.index.counts()["declarations"], 5)
        self.assertEqual(self._names("decl3"), ["decl3"])

    def test_schema_change_rebuilds_rather_than_erroring(self) -> None:
        self._write("a.txt", "theorem alpha\n")
        self._refresh()
        self.index.close()
        con = sqlite3.connect(self.index.db_path)
        con.execute("UPDATE meta SET value='stale' WHERE key='schema_fingerprint'")
        con.commit()
        con.close()
        self.assertEqual(self._names("alpha"), [])  # rebuilt empty
        self._refresh()
        self.assertEqual(self._names("alpha"), ["alpha"])

    def test_corrupt_database_is_replaced(self) -> None:
        self.index.db_path.write_bytes(b"this is not a database")
        self._write("a.txt", "theorem alpha\n")
        self._refresh()
        self.assertEqual(self._names("alpha"), ["alpha"])

    def test_unreadable_source_file_does_not_abort_the_refresh(self) -> None:
        self._write("a.txt", "theorem alpha\n")
        sources = self._sources()
        sources.append(SourceFile("ghost.txt", str(self.tree / "ghost.txt"), 1, 1))
        with self.assertRaises(OSError):
            self.index.refresh(sources, _extract)
        # The batch that failed rolled back; the tree is still searchable.
        self.assertEqual(self._refresh().changed, 1)
        self.assertEqual(self._names("alpha"), ["alpha"])

    def test_rebuild_reclaims_space_left_by_deleted_files(self) -> None:
        doc = "lorem ipsum dolor sit amet " * 8
        for i in range(200):
            self._write(
                f"f{i}.txt",
                "".join(f"theorem decl{i}_{j} -- {doc}\n" for j in range(20)),
            )
        self._refresh()
        for i in range(200):
            (self.tree / f"f{i}.txt").unlink()
        self._write("only.txt", "theorem alpha\n")
        self._refresh()
        fat = self._db_size()
        self.index.rebuild(self._sources(), _extract)
        # Dropping rows only moves pages to the freelist; only a rebuild
        # returns the space to the filesystem.
        self.assertLess(self._db_size(), fat)
        self.assertEqual(self._names("alpha"), ["alpha"])
        self.assertEqual(self.index.counts()["declarations"], 1)

    def test_concurrent_writer_leaves_the_index_searchable(self) -> None:
        self._write("a.txt", "theorem alpha\n")
        self._refresh()
        blocker = sqlite3.connect(self.index.db_path)
        blocker.execute("PRAGMA busy_timeout=0")
        blocker.execute("BEGIN EXCLUSIVE")
        self.addCleanup(blocker.close)

        self.index.busy_timeout_ms = 50
        self.index.close()
        self._write("b.txt", "theorem beta\n")
        stats = self._refresh()
        self.assertTrue(stats.stale, "a lost write lock must be reported, not raised")
        self.assertEqual(self._names("alpha"), ["alpha"], "stale index still answers queries")

        blocker.rollback()
        self.assertEqual(self._refresh().changed, 1)
        self.assertEqual(self._names("beta"), ["beta"])


if __name__ == "__main__":
    unittest.main()
