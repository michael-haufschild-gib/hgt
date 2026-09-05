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
from collections import Counter
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


def query_parts(query: str) -> list[tuple[tuple[str, ...], bool]]:
    """One shared, literal query grammar for FTS and the scan fallback."""
    if query.count('"') % 2:
        raise ValueError('unclosed phrase: use matching double quotes inside shell quotes')
    rest = _PHRASE_RE.sub(" ", query)
    if any(t in {"AND", "OR", "NOT", "NEAR"} for t in _TERM_RE.findall(rest)):
        raise ValueError('Boolean syntax is not supported: spaces mean AND; use --any for OR')
    parts = []
    for phrase in _PHRASE_RE.findall(query):
        terms = tuple(t.casefold() for t in _TERM_RE.findall(phrase))
        if terms:
            parts.append((terms, True))
    parts.extend(((t.casefold(),), False) for t in _TERM_RE.findall(rest))
    return list(dict.fromkeys(parts))


def matches_fields(parts: list[tuple[tuple[str, ...], bool]], fields: Sequence[str],
                   *, any_terms: bool = False, exact: bool = False) -> bool:
    """Token/phrase matching for machines without FTS5; phrases cannot cross fields."""
    columns = [tuple(t.casefold() for t in _TERM_RE.findall(f)) for f in fields]
    matches = []
    for terms, phrase in parts:
        if phrase:
            found = any(column[i:i + len(terms)] == terms
                        for column in columns for i in range(len(column) - len(terms) + 1))
        else:
            term = terms[0]
            found = any(token == term or (not exact and len(term) >= 2 and token.startswith(term))
                        for column in columns for token in column)
        matches.append(found)
    return bool(matches) and (any(matches) if any_terms else all(matches))


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
class SearchResults:
    declarations: list[DeclHit]
    exploration: list[DeclHit]
    total: int
    modules: int
    eligible: int


def module_family(module: str) -> str:
    """Directory plus two leading filename words: a cheap, explicit topic proxy."""
    parent, _, leaf = module.rpartition(".")
    return parent + "." + " ".join(split_identifier(leaf).casefold().split()[:2])


def select_results(hits: Sequence[DeclHit], *, limit: int, per_module: int,
                   offset: int, explore: int, total: int | None = None) -> SearchResults:
    """Cap modules before paging; discover across ALL matching module representatives."""
    ordered = sorted(hits, key=lambda h: (h.score, h.module, h.line, h.name))
    counts: Counter[str] = Counter()
    eligible = []
    representatives: dict[str, DeclHit] = {}
    for hit in ordered:
        representatives.setdefault(hit.module, hit)
        counts[hit.module] += 1
        if not per_module or counts[hit.module] <= per_module:
            eligible.append(hit)
    direct = eligible[offset:offset + limit]
    shown = {h.module for h in direct}
    families = Counter(module_family(m) for m in representatives)
    used = Counter(module_family(m) for m in shown)
    candidates = [h for m, h in representatives.items() if m not in shown]
    discovery = []
    for _ in range(explore):
        if not candidates:
            break
        # Scores are negative (better is smaller). Dampen families with many
        # matching modules; prefer families not already displayed. No random
        # unrelated modules and no top-N candidate cutoff that buries the tail.
        hit = min(candidates, key=lambda h: (
            used[module_family(h.module)],
            h.score / families[module_family(h.module)] ** 0.5,
            h.module, h.line, h.name,
        ))
        discovery.append(hit)
        used[module_family(hit.module)] += 1
        candidates.remove(hit)
    return SearchResults(direct, discovery, len(hits) if total is None else total,
                         len(representatives), len(eligible))


def module_matches(module: str, include: str = "", exclude: Sequence[str] = ()) -> bool:
    folded = module.casefold()
    return include.casefold() in folded and not any(s.casefold() in folded for s in exclude)


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
  module_tokens TEXT NOT NULL,
  kind    TEXT NOT NULL,
  line    INTEGER NOT NULL
);
CREATE INDEX decl_by_file ON decl(relpath);

CREATE VIRTUAL TABLE decl_fts USING fts5(
  name, tokens, doc, module, kind, module_tokens,
  content='decl', content_rowid='id',
  tokenize="unicode61 remove_diacritics 0"
);

CREATE TRIGGER decl_ai AFTER INSERT ON decl BEGIN
  INSERT INTO decl_fts(rowid, name, tokens, doc, module, kind, module_tokens)
  VALUES (new.id, new.name, new.tokens, new.doc, new.module, new.kind, new.module_tokens);
END;
CREATE TRIGGER decl_ad AFTER DELETE ON decl BEGIN
  INSERT INTO decl_fts(decl_fts, rowid, name, tokens, doc, module, kind, module_tokens)
  VALUES ('delete', old.id, old.name, old.tokens, old.doc, old.module, old.kind, old.module_tokens);
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
_DECL_WEIGHTS = (12.0, 8.0, 1.0, 0.6, 0.2, 0.6)
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


def build_match_expression(query: str, *, any_terms: bool = False, exact: bool = False) -> str:
    """Require every term/phrase by default; prefix alternatives stay grouped."""
    clauses = []
    for terms, phrase in query_parts(query):
        text = " ".join(terms)
        clause = f'"{text}"'
        if not phrase and not exact and len(text) >= 2:
            clause = f'({clause} OR "{text}"*)'
        clauses.append(clause)
    return (" OR " if any_terms else " AND ").join(clauses)


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
        try:
            con.execute(f"PRAGMA busy_timeout={self.busy_timeout_ms}")
            if not _fts5_available(con):
                raise SearchIndexUnavailable("this SQLite build has no FTS5 module")
            con.execute("PRAGMA journal_mode=WAL")
            con.execute("PRAGMA synchronous=NORMAL")
        except (sqlite3.DatabaseError, SearchIndexUnavailable):
            con.close()
            raise
        return con

    def _connect(self) -> sqlite3.Connection:
        if self._con is not None:
            return self._con
        con = None
        try:
            con = self._open()
            current = self._schema_current(con)
        except sqlite3.DatabaseError as error:
            if con is not None:
                con.close()
            # Python <3.11 does not expose sqlite_errorcode or result constants.
            corrupt = getattr(error, "sqlite_errorcode", None) in (11, 26) or str(error) in (
                "file is not a database", "database disk image is malformed"
            )
            if not corrupt:
                raise
            self._unlink()
            con = self._open()
            current = False
        try:
            if not current:
                con = self._create_schema(con)
        except sqlite3.DatabaseError:
            con.close()
            raise
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
        if not con.execute("SELECT 1 FROM sqlite_master WHERE name='meta'").fetchone():
            return False
        row = con.execute("SELECT value FROM meta WHERE key='schema_fingerprint'").fetchone()
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
        """Migrate atomically; lock contention must never unlink a live index."""
        try:
            con.execute("BEGIN IMMEDIATE")
            # Another process may have completed migration while we waited.
            if not self._schema_current(con):
                for kind, name in self._DROP_ORDER:
                    con.execute(f"DROP {kind} IF EXISTS {name}")
                # executescript implicitly commits, so execute complete SQL
                # statements individually to keep DDL and fingerprint atomic.
                statement = ""
                for line in _SCHEMA.splitlines(keepends=True):
                    statement += line
                    if sqlite3.complete_statement(statement):
                        con.execute(statement)
                        statement = ""
                con.execute(
                    "INSERT INTO meta(key, value) VALUES('schema_fingerprint', ?)",
                    (SCHEMA_FINGERPRINT,),
                )
            con.commit()
        except sqlite3.DatabaseError:
            con.rollback()
            raise
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
                            "INSERT INTO decl(relpath, name, tokens, doc, module, kind, line, module_tokens)"
                            " VALUES (?,?,?,?,?,?,?,?)",
                            [
                                (
                                    relpath,
                                    d.name,
                                    split_identifier(d.name),
                                    d.doc,
                                    d.module,
                                    d.kind,
                                    d.line,
                                    split_identifier(d.module),
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

    def search_declarations(self, query: str, limit: int = 20, **options) -> list[DeclHit]:
        return self.search(query, limit=limit, explore=0, **options).declarations

    def search(self, query: str, *, limit: int = 20, any_terms: bool = False,
               exact: bool = False, per_module: int = 0, offset: int = 0,
               explore: int = 5, module: str = "",
               exclude_modules: Sequence[str] = ()) -> SearchResults:
        if min(limit, per_module, offset, explore) < 0:
            raise ValueError("search limits and offset must be nonnegative")
        match = build_match_expression(query, any_terms=any_terms, exact=exact)
        if not match:
            return SearchResults([], [], 0, 0, 0)
        con = self._connect()
        weights = ", ".join(str(w) for w in _DECL_WEIGHTS)
        filters, params = self._module_filter("d.module", module, exclude_modules)
        params.update(match=match, identifier=query.strip().lower(), cap=per_module)
        rows = con.execute(
            f"""
            WITH scored AS MATERIALIZED (
              SELECT d.id, d.module, d.line, d.name,
                     bm25(decl_fts, {weights})
                       - CASE WHEN lower(d.name) = :identifier THEN 400.0 ELSE 0.0 END
                       - CASE WHEN instr(lower(d.name), :identifier) > 0 THEN 120.0 ELSE 0.0 END
                       AS score
              FROM decl_fts JOIN decl d ON d.id = decl_fts.rowid
              WHERE decl_fts MATCH :match {filters}
            ), ranked AS (
              SELECT *, row_number() OVER (
                PARTITION BY module ORDER BY score, line, name, id
              ) AS module_rank, count(*) OVER () AS total
              FROM scored
            )
            SELECT d.name, d.kind, d.module, d.relpath, d.line, d.doc, r.score, r.total
            FROM ranked r JOIN decl d ON d.id = r.id
            WHERE :cap = 0 OR r.module_rank <= :cap
            """, params,
        ).fetchall()
        hits = [DeclHit(*row[:7]) for row in rows]
        return select_results(hits, limit=limit, per_module=per_module,
                              offset=offset, explore=explore,
                              total=rows[0][7] if rows else 0)

    @staticmethod
    def _module_filter(column: str, module: str, excludes: Sequence[str]) -> tuple[str, dict]:
        # Literal substrings, not LIKE patterns: underscores and % stay literal.
        sql = f" AND instr(lower({column}), :module) > 0"
        params = {"module": module.lower()}
        for i, value in enumerate(excludes):
            sql += f" AND instr(lower({column}), :exclude{i}) = 0"
            params[f"exclude{i}"] = value.lower()
        return sql, params

    def search_markers(self, query: str, limit: int = 20, *, any_terms: bool = False,
                       exact: bool = False, module: str = "",
                       exclude_modules: Sequence[str] = ()) -> list[MarkerHit]:
        if limit < 0:
            raise ValueError("marker limit must be nonnegative")
        match = build_match_expression(query, any_terms=any_terms, exact=exact)
        if not match:
            return []
        con = self._connect()
        weights = ", ".join(str(w) for w in _MARKER_WEIGHTS)
        # Markers have a path, not a module. Normalize separators for the same
        # dotted module filters used on declarations (also covers prose files).
        filters, params = self._module_filter("replace(m.relpath, '/', '.')", module, exclude_modules)
        params.update(match=match, limit=limit)
        rows = con.execute(
            f"""
            SELECT m.relpath, m.line, m.text, bm25(marker_fts, {weights}) AS score
            FROM marker_fts JOIN marker m ON m.id = marker_fts.rowid
            WHERE marker_fts MATCH :match {filters}
            ORDER BY score, m.relpath, m.line
            LIMIT :limit
            """, params,
        ).fetchall()
        return [MarkerHit(*r) for r in rows]

    def counts(self) -> dict[str, int]:
        con = self._connect()
        return {
            "files": con.execute("SELECT count(*) FROM file").fetchone()[0],
            "declarations": con.execute("SELECT count(*) FROM decl").fetchone()[0],
            "markers": con.execute("SELECT count(*) FROM marker").fetchone()[0],
        }
