#!/usr/bin/env python3
"""Incremental full-text search index for the Lean corpus.

The formal tree is far too large to re-scan on every query: ~18.7k own-tree
files, ~4.5M lines, ~214k declarations.  Loading the per-file extraction cache
and linearly scoring every declaration costs well over a second per query, and
the substring scoring it used gave no useful ranking — a three-word query
matches ten thousand declarations and the top twenty came out in alphabetical
order.

This module keeps a SQLite FTS5 index next to the tree instead.  It is chosen
over an external search library for three reasons that matter here:

* `sqlite3` is in the standard library, so there is no dependency to install in
  every agent worktree and nothing that can rot;
* FTS5 is a C implementation with BM25 ranking built in, so a full rebuild of
  the declaration corpus takes ~2s and a query ~10ms;
* WAL mode allows many concurrent readers with a single short-lived writer,
  which is the access pattern of a fleet of agents that mostly search and
  occasionally add files.  A refresh that loses the write lock degrades to
  searching the slightly stale index rather than blocking or failing.

Nothing in here imports the rest of the formal tooling: the caller supplies the
file list and an extraction callback, so the index can be exercised in
isolation.
"""

from __future__ import annotations

import dataclasses
import hashlib
import re
import sqlite3
from pathlib import Path
from typing import Callable, Iterable, Sequence

# Lean identifiers are namespaced, snake_cased and camelCased all at once
# (`evalJet_measuredClockInverseOperator_difference`).  The FTS tokenizer only
# splits on non-alphanumerics, so the camel humps are exploded into a separate
# indexed column at write time; that is what makes "measured clock inverse"
# find the declaration above.
_CAMEL_RE = re.compile(r"[A-Z]+(?![a-z])|[A-Z][a-z0-9']*|[a-z0-9']+")
_SPLIT_RE = re.compile(r"[._\s]+")
# `[^\W_]` is "word character except underscore", so the query side keeps the
# Greek and script letters that fill this corpus's names and docstrings (`ξ`,
# `Λ`, `θ`) instead of silently dropping them, while `_` still separates.
_TERM_RE = re.compile(r"[^\W_]+(?:['’][^\W_]*)*")
_PHRASE_RE = re.compile(r'"([^"]+)"')


def split_identifier(name: str) -> str:
    """Explode a Lean identifier into its namespace, snake and camel components."""
    parts: list[str] = []
    for chunk in _SPLIT_RE.split(name):
        parts.extend(_CAMEL_RE.findall(chunk))
    return " ".join(parts)


@dataclasses.dataclass(frozen=True)
class SourceFile:
    """One indexable file, already stamped by the caller's directory walk.

    The walk has to stat every file anyway to decide what changed, so the stamp
    travels with the entry rather than being taken a second time here.  Paths
    stay strings: only the handful of changed files are ever turned into
    `Path` objects, and at this scale that alone is tens of milliseconds.
    """

    relpath: str
    abspath: str
    size: int
    mtime_ns: int


@dataclasses.dataclass(frozen=True)
class DeclRow:
    name: str
    kind: str
    module: str
    line: int
    doc: str


@dataclasses.dataclass(frozen=True)
class MarkerRow:
    line: int
    text: str


@dataclasses.dataclass(frozen=True)
class DeclHit:
    name: str
    kind: str
    module: str
    relpath: str
    line: int
    doc: str
    score: float


@dataclasses.dataclass(frozen=True)
class MarkerHit:
    relpath: str
    line: int
    text: str
    score: float


@dataclasses.dataclass(frozen=True)
class RefreshStats:
    changed: int
    removed: int
    indexed_files: int
    wrote: bool
    stale: bool = False
    reason: str = ""


class SearchIndexUnavailable(RuntimeError):
    """Raised when this SQLite build cannot host the index."""


# No `prefix=` option: prefix terms are answered from the ordinary term index
# by range scan, and on this corpus that measured identical query latency
# (including two- and three-letter prefixes) while a `prefix='2 3 4'` index
# added ~110 MB and half again the build time.
_SCHEMA = """
CREATE TABLE meta(key TEXT PRIMARY KEY, value TEXT NOT NULL);

CREATE TABLE file(
  relpath  TEXT PRIMARY KEY,
  size     INTEGER NOT NULL,
  mtime_ns INTEGER NOT NULL
);

CREATE TABLE decl(
  id      INTEGER PRIMARY KEY,
  relpath TEXT NOT NULL,
  name    TEXT NOT NULL,
  tokens  TEXT NOT NULL,
  doc     TEXT NOT NULL,
  module  TEXT NOT NULL,
  kind    TEXT NOT NULL,
  line    INTEGER NOT NULL
);
CREATE INDEX decl_by_file ON decl(relpath);

CREATE VIRTUAL TABLE decl_fts USING fts5(
  name, tokens, doc, module, kind,
  content='decl', content_rowid='id',
  tokenize="unicode61 remove_diacritics 0"
);

CREATE TRIGGER decl_ai AFTER INSERT ON decl BEGIN
  INSERT INTO decl_fts(rowid, name, tokens, doc, module, kind)
  VALUES (new.id, new.name, new.tokens, new.doc, new.module, new.kind);
END;
CREATE TRIGGER decl_ad AFTER DELETE ON decl BEGIN
  INSERT INTO decl_fts(decl_fts, rowid, name, tokens, doc, module, kind)
  VALUES ('delete', old.id, old.name, old.tokens, old.doc, old.module, old.kind);
END;

CREATE TABLE marker(
  id      INTEGER PRIMARY KEY,
  relpath TEXT NOT NULL,
  path    TEXT NOT NULL,
  line    INTEGER NOT NULL,
  text    TEXT NOT NULL
);
CREATE INDEX marker_by_file ON marker(relpath);

CREATE VIRTUAL TABLE marker_fts USING fts5(
  text, path,
  content='marker', content_rowid='id',
  tokenize="unicode61 remove_diacritics 0"
);

CREATE TRIGGER marker_ai AFTER INSERT ON marker BEGIN
  INSERT INTO marker_fts(rowid, text, path) VALUES (new.id, new.text, new.path);
END;
CREATE TRIGGER marker_ad AFTER DELETE ON marker BEGIN
  INSERT INTO marker_fts(marker_fts, rowid, text, path)
  VALUES ('delete', old.id, old.text, old.path);
END;
"""

# Column order matches decl_fts: name, tokens, doc, module, kind.  A hit on the
# declaration name outweighs one in its docstring, and the exploded-identifier
# column sits just under the raw name so a multi-word query still lands on the
# declaration it describes rather than on some file that merely mentions it.
_DECL_WEIGHTS = (12.0, 8.0, 1.0, 0.6, 0.2)
_MARKER_WEIGHTS = (4.0, 1.0)

# The stored fingerprint is derived from the schema text rather than a
# hand-bumped integer, so editing `_SCHEMA` cannot leave agents querying an
# index built to the previous layout.
SCHEMA_FINGERPRINT = hashlib.sha256(_SCHEMA.encode("utf-8")).hexdigest()[:16]


def _fts5_available(con: sqlite3.Connection) -> bool:
    try:
        con.execute("CREATE VIRTUAL TABLE temp.fts5_probe USING fts5(x)")
    except sqlite3.OperationalError:
        return False
    con.execute("DROP TABLE temp.fts5_probe")
    return True


def build_match_expression(query: str) -> str:
    """Translate a plain user query into an FTS5 MATCH expression.

    Quoted runs stay phrases.  Every other term is emitted twice, once exact
    and once as a prefix, so `ladder` still finds `ladderLattice` and a
    half-typed identifier still resolves — while a document matching the exact
    term matches two clauses instead of one and therefore outranks documents
    that only satisfy the prefix.  Without that, `sum` would rank `summable`
    alongside `sum`.  Terms are OR-ed: a Lean search is usually "these
    concepts, best match first", not a conjunctive filter.
    """
    phrases = [p.strip() for p in _PHRASE_RE.findall(query)]
    rest = _PHRASE_RE.sub(" ", query)
    clauses = [f'"{p.replace(chr(34), "")}"' for p in phrases if p.strip()]
    for term in _TERM_RE.findall(rest):
        token = term.replace('"', "")
        if not token:
            continue
        clauses.append(f'"{token}"')
        if len(token) >= 2:
            clauses.append(f'"{token}"*')
    return " OR ".join(clauses)


class LeanSearchIndex:
    """An incrementally maintained FTS5 index over declarations and gap markers."""

    def __init__(
        self, db_path: Path, *, busy_timeout_ms: int = 30_000, batch_size: int = 512
    ) -> None:
        self.db_path = db_path
        self.busy_timeout_ms = busy_timeout_ms
        self.batch_size = batch_size
        self._con: sqlite3.Connection | None = None

    # -- connection handling -------------------------------------------------

    def _open(self) -> sqlite3.Connection:
        con = sqlite3.connect(self.db_path)
        con.execute(f"PRAGMA busy_timeout={self.busy_timeout_ms}")
        if not _fts5_available(con):
            con.close()
            raise SearchIndexUnavailable("this SQLite build has no FTS5 module")
        con.execute("PRAGMA journal_mode=WAL")
        con.execute("PRAGMA synchronous=NORMAL")
        return con

    def _connect(self) -> sqlite3.Connection:
        if self._con is not None:
            return self._con
        try:
            con = self._open()
            current = self._schema_current(con)
        except SearchIndexUnavailable:
            raise
        except sqlite3.DatabaseError:
            # Not a database at all — a truncated or half-written file from an
            # interrupted run.  The index is derivable, so discard it.
            self._unlink()
            con = self._open()
            current = False
        if not current:
            con = self._create_schema(con)
        self._con = con
        return con

    def _unlink(self) -> None:
        for suffix in ("", "-wal", "-shm"):
            Path(str(self.db_path) + suffix).unlink(missing_ok=True)

    def close(self) -> None:
        if self._con is not None:
            self._con.close()
            self._con = None

    def _schema_current(self, con: sqlite3.Connection) -> bool:
        try:
            row = con.execute("SELECT value FROM meta WHERE key='schema_fingerprint'").fetchone()
        except sqlite3.DatabaseError:
            return False
        return bool(row) and row[0] == SCHEMA_FINGERPRINT

    # Order matters: triggers reference the FTS tables, and dropping an FTS5
    # virtual table is what cleans up its shadow tables.
    _DROP_ORDER = (
        ("TRIGGER", "decl_ai"),
        ("TRIGGER", "decl_ad"),
        ("TRIGGER", "marker_ai"),
        ("TRIGGER", "marker_ad"),
        ("TABLE", "decl_fts"),
        ("TABLE", "marker_fts"),
        ("TABLE", "decl"),
        ("TABLE", "marker"),
        ("TABLE", "file"),
        ("TABLE", "meta"),
    )

    def _create_schema(self, con: sqlite3.Connection) -> sqlite3.Connection:
        """(Re)create the schema, discarding any older layout.

        Dropping in dependency order keeps other processes' open handles valid.
        Only if the existing file is too damaged for that does it get replaced
        outright.
        """
        try:
            for kind, name in self._DROP_ORDER:
                con.execute(f"DROP {kind} IF EXISTS {name}")
            con.executescript(_SCHEMA)
        except sqlite3.DatabaseError:
            con.close()
            self._unlink()
            con = self._open()
            con.executescript(_SCHEMA)
        con.execute(
            "INSERT OR REPLACE INTO meta(key, value) VALUES('schema_fingerprint', ?)",
            (SCHEMA_FINGERPRINT,),
        )
        con.commit()
        self._con = con
        return con

    # -- writing -------------------------------------------------------------

    def refresh(
        self,
        sources: Sequence[SourceFile],
        extract: Callable[[SourceFile], tuple[Iterable[DeclRow], Iterable[MarkerRow]]],
    ) -> RefreshStats:
        """Bring the index in line with the tree, re-reading only changed files.

        `sources` is the full stamped set of files that should be indexed;
        anything recorded but absent from it is dropped.  Change detection uses
        (size, mtime_ns), matching the per-file extraction cache the rest of the
        tooling already trusts.
        """
        con = self._connect()
        known = {
            row[0]: (row[1], row[2]) for row in con.execute("SELECT relpath, size, mtime_ns FROM file")
        }

        changed = [
            source
            for source in sources
            if known.get(source.relpath) != (source.size, source.mtime_ns)
        ]
        removed = sorted(set(known) - {source.relpath for source in sources})

        if not changed and not removed:
            return RefreshStats(0, 0, len(known), wrote=False)

        # Write in batches rather than one transaction: a cold build parses
        # thousands of files, and holding the write lock for all of it would
        # stall every other agent's refresh.  Each batch is self-consistent, so
        # an interrupted run simply resumes at the first unrecorded file.
        done = 0
        try:
            for start in range(0, len(changed) or 1, self.batch_size):
                batch = changed[start : start + self.batch_size]
                with con:
                    if start == 0:
                        for relpath in removed:
                            self._drop_file(con, relpath)
                    for source in batch:
                        relpath = source.relpath
                        # Re-check inside the write lock.  With a fleet of
                        # agents refreshing at once they all queue up holding
                        # the same work list, and without this every one of
                        # them would re-parse and rewrite what the first
                        # already indexed.
                        current = con.execute(
                            "SELECT size, mtime_ns FROM file WHERE relpath = ?", (relpath,)
                        ).fetchone()
                        if current and tuple(current) == (source.size, source.mtime_ns):
                            continue
                        self._drop_file(con, relpath)
                        decls, markers = extract(source)
                        con.executemany(
                            "INSERT INTO decl(relpath, name, tokens, doc, module, kind, line)"
                            " VALUES (?,?,?,?,?,?,?)",
                            [
                                (
                                    relpath,
                                    d.name,
                                    split_identifier(d.name),
                                    d.doc,
                                    d.module,
                                    d.kind,
                                    d.line,
                                )
                                for d in decls
                            ],
                        )
                        con.executemany(
                            "INSERT INTO marker(relpath, path, line, text) VALUES (?,?,?,?)",
                            [(relpath, split_identifier(relpath), m.line, m.text) for m in markers],
                        )
                        con.execute(
                            "INSERT OR REPLACE INTO file(relpath, size, mtime_ns) VALUES (?,?,?)",
                            (relpath, source.size, source.mtime_ns),
                        )
                        done += 1
        except sqlite3.OperationalError as error:
            # Another agent holds the write lock.  A slightly stale index still
            # answers the query, which beats blocking the caller.
            return RefreshStats(
                done, len(removed), len(known), wrote=done > 0, stale=True, reason=str(error)
            )
        return RefreshStats(done, len(removed), len(sources), wrote=True)

    @staticmethod
    def _drop_file(con: sqlite3.Connection, relpath: str) -> None:
        con.execute("DELETE FROM decl WHERE relpath = ?", (relpath,))
        con.execute("DELETE FROM marker WHERE relpath = ?", (relpath,))
        con.execute("DELETE FROM file WHERE relpath = ?", (relpath,))

    def optimize(self) -> None:
        con = self._connect()
        with con:
            con.execute("INSERT INTO decl_fts(decl_fts) VALUES('optimize')")
            con.execute("INSERT INTO marker_fts(marker_fts) VALUES('optimize')")

    def rebuild(
        self,
        sources: Sequence[SourceFile],
        extract: Callable[[SourceFile], tuple[Iterable[DeclRow], Iterable[MarkerRow]]],
    ) -> RefreshStats:
        # Replace the file rather than dropping tables inside it: dropped pages
        # go to the freelist, so an in-place rebuild would keep the old size
        # forever.  Readers holding the previous file keep working on it until
        # they reconnect.
        self.close()
        self._unlink()
        self._connect()
        stats = self.refresh(sources, extract)
        self.optimize()
        return stats

    # -- reading -------------------------------------------------------------

    def search_declarations(self, query: str, limit: int = 20) -> list[DeclHit]:
        match = build_match_expression(query)
        if not match:
            return []
        con = self._connect()
        exact = query.strip().lower()
        weights = ", ".join(str(w) for w in _DECL_WEIGHTS)
        rows = con.execute(
            f"""
            SELECT d.name, d.kind, d.module, d.relpath, d.line, d.doc,
                   bm25(decl_fts, {weights})
                     - (CASE WHEN lower(d.name) = :exact THEN 400.0 ELSE 0.0 END)
                     - (CASE WHEN instr(lower(d.name), :exact) > 0 THEN 120.0 ELSE 0.0 END)
                     AS score
            FROM decl_fts JOIN decl d ON d.id = decl_fts.rowid
            WHERE decl_fts MATCH :match
            ORDER BY score
            LIMIT :limit
            """,
            {"match": match, "exact": exact, "limit": limit},
        ).fetchall()
        return [DeclHit(r[0], r[1], r[2], r[3], r[4], r[5], r[6]) for r in rows]

    def search_markers(self, query: str, limit: int = 20) -> list[MarkerHit]:
        match = build_match_expression(query)
        if not match:
            return []
        con = self._connect()
        weights = ", ".join(str(w) for w in _MARKER_WEIGHTS)
        rows = con.execute(
            f"""
            SELECT m.relpath, m.line, m.text, bm25(marker_fts, {weights}) AS score
            FROM marker_fts JOIN marker m ON m.id = marker_fts.rowid
            WHERE marker_fts MATCH :match
            ORDER BY score
            LIMIT :limit
            """,
            {"match": match, "limit": limit},
        ).fetchall()
        return [MarkerHit(r[0], r[1], r[2], r[3]) for r in rows]

    def counts(self) -> dict[str, int]:
        con = self._connect()
        return {
            "files": con.execute("SELECT count(*) FROM file").fetchone()[0],
            "declarations": con.execute("SELECT count(*) FROM decl").fetchone()[0],
            "markers": con.execute("SELECT count(*) FROM marker").fetchone()[0],
        }
