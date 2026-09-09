#!/usr/bin/env python3
"""Versioned, incremental corpus for statement and proof-method discovery.

The legacy name/doc index remains independent: its query and JSON contracts do
not change. This database records every source's outcome and every searchable
chunk's provenance. Source extraction is explicitly provisional; only the Lean
exporter supplies elaborated types, binders, proof references and axioms.
"""
from __future__ import annotations

import contextlib
import fcntl
import hashlib
import json
import os
import re
import sqlite3
import time
from pathlib import Path
from typing import Iterable

from lean_search_index import build_match_expression, module_matches, split_identifier

VERSION = "discovery-1"
EXTRACTION_VERSION = 'source-2'
CHUNK_CHARS = 5000
CHUNK_OVERLAP = 300
PRIORITY_VERSION = 'rhtower-htgeometry-1'
PATH_PRIORITY_SQL = "CASE WHEN instr(lower(path),'/rhtower/')>0 THEN 0 WHEN instr(lower(path),'/htgeometry/')>0 THEN 100 ELSE 200 END"
SCHEMA = """
CREATE TABLE IF NOT EXISTS meta(key TEXT PRIMARY KEY,value TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS files(
 path TEXT PRIMARY KEY,module TEXT NOT NULL,package TEXT NOT NULL,collection TEXT NOT NULL,
 size INTEGER,mtime_ns INTEGER,source_hash TEXT,status TEXT NOT NULL,error TEXT NOT NULL DEFAULT '',
 compile_status TEXT NOT NULL DEFAULT 'pending',imports TEXT NOT NULL DEFAULT '[]',
 toolchain TEXT NOT NULL DEFAULT '',updated REAL NOT NULL);
CREATE TABLE IF NOT EXISTS declarations(
 id TEXT PRIMARY KEY,path TEXT NOT NULL REFERENCES files(path) ON DELETE CASCADE,
 name TEXT NOT NULL,module TEXT NOT NULL,kind TEXT NOT NULL,line INTEGER NOT NULL,end_line INTEGER NOT NULL,
 statement TEXT NOT NULL,proof TEXT NOT NULL,doc TEXT NOT NULL,source_hash TEXT NOT NULL,
 type_text TEXT NOT NULL DEFAULT '',type_shape TEXT NOT NULL DEFAULT '',
 binders TEXT NOT NULL DEFAULT '[]',axioms TEXT,compiler_status TEXT NOT NULL DEFAULT 'source_only');
CREATE INDEX IF NOT EXISTS declaration_name ON declarations(name);
CREATE INDEX IF NOT EXISTS declaration_path ON declarations(path);
CREATE TABLE IF NOT EXISTS compiler_metadata(
 decl_id TEXT PRIMARY KEY REFERENCES declarations(id) ON DELETE CASCADE,payload TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS documents(
 id INTEGER PRIMARY KEY,decl_id TEXT REFERENCES declarations(id) ON DELETE CASCADE,
 path TEXT NOT NULL REFERENCES files(path) ON DELETE CASCADE,module TEXT NOT NULL,
 view TEXT NOT NULL,line INTEGER NOT NULL,end_line INTEGER NOT NULL,text TEXT NOT NULL,
 content_hash TEXT NOT NULL,provenance TEXT NOT NULL);
CREATE INDEX IF NOT EXISTS document_decl ON documents(decl_id,view);
CREATE INDEX IF NOT EXISTS document_path ON documents(path);
CREATE TABLE IF NOT EXISTS embedding_queue(
 doc_id INTEGER PRIMARY KEY REFERENCES documents(id) ON DELETE CASCADE,
 content_hash TEXT NOT NULL,priority INTEGER NOT NULL);
CREATE INDEX IF NOT EXISTS embedding_priority ON embedding_queue(priority,doc_id);
CREATE TRIGGER IF NOT EXISTS embedding_insert_priority AFTER INSERT ON documents WHEN new.view<>'lean' BEGIN
 INSERT OR REPLACE INTO embedding_queue VALUES(new.id,new.content_hash,
 (CASE WHEN instr(lower(new.path),'/rhtower/')>0 THEN 0 WHEN instr(lower(new.path),'/htgeometry/')>0 THEN 100 ELSE 200 END) +
 CASE new.view WHEN 'method' THEN 0 WHEN 'type' THEN 1 WHEN 'statement' THEN 2 WHEN 'proof' THEN 3 WHEN 'shape' THEN 4 ELSE 5 END); END;
CREATE TRIGGER IF NOT EXISTS embedding_update_priority AFTER UPDATE ON documents WHEN new.view<>'lean' AND new.content_hash<>old.content_hash BEGIN
 INSERT OR REPLACE INTO embedding_queue VALUES(new.id,new.content_hash,
 (CASE WHEN instr(lower(new.path),'/rhtower/')>0 THEN 0 WHEN instr(lower(new.path),'/htgeometry/')>0 THEN 100 ELSE 200 END) +
 CASE new.view WHEN 'method' THEN 0 WHEN 'type' THEN 1 WHEN 'statement' THEN 2 WHEN 'proof' THEN 3 WHEN 'shape' THEN 4 ELSE 5 END); END;
CREATE VIRTUAL TABLE IF NOT EXISTS document_fts USING fts5(text,module,view,
 content='documents',content_rowid='id',tokenize='unicode61 remove_diacritics 0');
CREATE TRIGGER IF NOT EXISTS doc_insert AFTER INSERT ON documents BEGIN
 INSERT INTO document_fts(rowid,text,module,view) VALUES(new.id,new.text,new.module,new.view); END;
CREATE TRIGGER IF NOT EXISTS doc_delete AFTER DELETE ON documents BEGIN
 INSERT INTO document_fts(document_fts,rowid,text,module,view) VALUES('delete',old.id,old.text,old.module,old.view); END;
CREATE TRIGGER IF NOT EXISTS doc_update AFTER UPDATE ON documents BEGIN
 INSERT INTO document_fts(document_fts,rowid,text,module,view) VALUES('delete',old.id,old.text,old.module,old.view);
 INSERT INTO document_fts(rowid,text,module,view) VALUES(new.id,new.text,new.module,new.view); END;
CREATE TABLE IF NOT EXISTS dependencies(
 source TEXT REFERENCES declarations(id) ON DELETE CASCADE,target TEXT NOT NULL,kind TEXT NOT NULL,
 PRIMARY KEY(source,target,kind));
CREATE INDEX IF NOT EXISTS dependency_target ON dependencies(target);
CREATE TABLE IF NOT EXISTS methods(
 decl_id TEXT PRIMARY KEY REFERENCES declarations(id) ON DELETE CASCADE,
 content_hash TEXT NOT NULL,model_version TEXT NOT NULL,prompt_version TEXT NOT NULL,
 description TEXT NOT NULL,assumptions TEXT NOT NULL,steps TEXT NOT NULL,obligations TEXT NOT NULL,
 evidence TEXT NOT NULL,status TEXT NOT NULL,error TEXT NOT NULL DEFAULT '');
CREATE TABLE IF NOT EXISTS method_chunks(
 decl_id TEXT NOT NULL REFERENCES declarations(id) ON DELETE CASCADE,
 chunk_hash TEXT NOT NULL,source_hash TEXT NOT NULL,model_version TEXT NOT NULL,
 prompt_version TEXT NOT NULL,payload TEXT NOT NULL,
 PRIMARY KEY(decl_id,chunk_hash,model_version,prompt_version));
CREATE TABLE IF NOT EXISTS vector_shards(
 id TEXT PRIMARY KEY,filename TEXT NOT NULL,model TEXT NOT NULL,count INTEGER NOT NULL,created REAL NOT NULL);
CREATE TABLE IF NOT EXISTS vectors(
 doc_id INTEGER PRIMARY KEY REFERENCES documents(id) ON DELETE CASCADE,content_hash TEXT NOT NULL,
 shard TEXT NOT NULL REFERENCES vector_shards(id),position INTEGER NOT NULL,model TEXT NOT NULL);
CREATE INDEX IF NOT EXISTS vector_shard ON vectors(shard);
CREATE INDEX IF NOT EXISTS vector_content ON vectors(model,content_hash);
CREATE TABLE IF NOT EXISTS embedding_cache(
 content_hash TEXT NOT NULL,model TEXT NOT NULL,
 shard TEXT NOT NULL REFERENCES vector_shards(id),vector_id INTEGER NOT NULL,
 PRIMARY KEY(model,content_hash));
CREATE INDEX IF NOT EXISTS embedding_cache_shard ON embedding_cache(shard);
CREATE TABLE IF NOT EXISTS cache(key TEXT PRIMARY KEY,generation INTEGER NOT NULL,result TEXT NOT NULL,created REAL NOT NULL);
"""


def digest(value: str | bytes) -> str:
    return hashlib.sha256(value.encode() if isinstance(value, str) else value).hexdigest()


def cache_directory(root: Path) -> Path:
    return root / "formal" / ".lake" / "hgt-research" / VERSION


def source_priority(path: str) -> int:
    parts = Path(path.lower()).parts
    return 0 if 'rhtower' in parts else 100 if 'htgeometry' in parts else 200


class EvidenceChanged(ValueError):
    """Source or dependencies changed while a generated description was pending."""


def mask_comments_strings(text: str) -> str:
    """Mask nested comments and strings without moving source offsets."""
    out = list(text)
    depth = 0
    string = False
    i = 0
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                out[i:i + 2] = "  "
                i += 2
                continue
            if pair == "-/":
                depth -= 1
                out[i:i + 2] = "  "
                i += 2
                continue
            if text[i] != "\n":
                out[i] = " "
        elif string:
            if text[i] == "\\" and i + 1 < len(text):
                out[i] = " "
                if text[i + 1] != "\n":
                    out[i + 1] = " "
                i += 2
                continue
            if text[i] == '"':
                string = False
            if text[i] != "\n":
                out[i] = " "
        elif pair == "/-":
            depth = 1
            out[i:i + 2] = "  "
            i += 2
            continue
        elif pair == "--":
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out[i:end] = " " * (end - i)
            i = end
            continue
        elif text[i] == '"':
            string = True
            out[i] = " "
        i += 1
    return "".join(out)


DECL = re.compile(
    r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local|public|meta)[ \t]+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\b"
    r"[ \t]*(?P<name>«[^»]+»|[\w'.]+)?", re.MULTILINE)
COMMAND = re.compile(r"^[ \t]*(namespace|section|end)\b(?:[ \t]+([^\s]+))?", re.MULTILINE)
IMPORT = re.compile(r"^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+([^\n]+)", re.MULTILINE)


def chunks(text: str, line: int = 1) -> Iterable[tuple[str, int, int]]:
    """Cover all bytes with bounded chunks, including declarations we cannot parse."""
    start = 0
    while start < len(text):
        end = min(len(text), start + CHUNK_CHARS)
        if end < len(text):
            newline = text.rfind("\n", start + CHUNK_CHARS // 2, end)
            if newline >= 0:
                end = newline + 1
        first = line + text.count("\n", 0, start)
        last = first + text.count("\n", start, end)
        yield text[start:end], first, last
        if end == len(text):
            break
        start = max(start + 1, end - CHUNK_OVERLAP)


def source_declarations(text: str, module: str, path: str) -> list[dict]:
    """Provisional source spans; the compiler is authoritative for signatures.

    Namespace and section commands are tracked to prevent common same-short-name
    collisions. Full file chunks ensure unusual syntax never disappears.
    """
    masked = mask_comments_strings(text)
    matches = list(DECL.finditer(masked))
    commands = list(COMMAND.finditer(masked))
    scope: list[tuple[str, str]] = []
    ci = 0
    result = []
    for i, match in enumerate(matches):
        while ci < len(commands) and commands[ci].start() < match.start():
            command = commands[ci]
            kind, name = command.group(1), command.group(2) or ""
            if kind == "end":
                if scope:
                    scope.pop()
            else:
                scope.append((kind, name))
            ci += 1
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        # Do not append following section/namespace commands to a proof body.
        for command in commands[ci:]:
            if match.end() <= command.start() < end:
                end = command.start()
                break
        name = match.group("name") or ""
        if name in {"where", "extends"} or not name:
            name = "<anonymous@%d>" % (text.count("\n", 0, match.start()) + 1)
        namespace = ".".join(n for k, n in scope if k == "namespace" and n)
        if name.startswith("_root_."):
            name = name[len("_root_."):]
        elif namespace:
            name = namespace + "." + name
        block = text[match.start():end].strip()
        block_mask = masked[match.start():end]
        # First assignment outside nested binders: default argument assignments
        # must not be confused with the declaration's proof.
        nesting = 0
        assign = -1
        for j, char in enumerate(block_mask):
            if char in "([{":
                nesting += 1
            elif char in ")]}":
                nesting = max(0, nesting - 1)
            elif not nesting and block_mask[j:j + 2] == ":=":
                assign = j
                break
        raw_block = text[match.start():end]
        statement = raw_block[:assign].strip() if assign >= 0 else block
        proof = raw_block[assign + 2:].strip() if assign >= 0 else ""
        prior = text[:match.start()].rstrip()
        doc = ""
        if prior.endswith("-/"):
            at = prior.rfind("/--")
            if at >= 0:
                doc = prior[at + 3:-2].strip()
        line = text.count("\n", 0, match.start()) + 1
        after_assignment = raw_block[assign + 2:] if assign >= 0 else ''
        leading_space = after_assignment[:len(after_assignment) - len(after_assignment.lstrip())]
        result.append(dict(id=digest(path + "\0" + name + "\0" + str(line)),
                           path=path, name=name, module=module, kind=match.group("kind"),
                           line=line, end_line=text.count("\n", 0, end) + 1,
                           proof_line=(line + raw_block[:assign + 2].count("\n") + leading_space.count('\n')) if assign >= 0 else line,
                           statement=statement, proof=proof, doc=doc, source_hash=digest(block)))
    return result


def inventory(root: Path) -> tuple[list[dict], list[dict]]:
    """All project sources and installed package sources; no traversal failures hidden."""
    roots = [(root / "formal", "project", "lean"), (root / "docs", "research", "prose")]
    package_dir = root / "formal" / ".lake" / "packages"
    errors: list[dict] = []
    if package_dir.exists():
        try:
            roots.extend((p, p.name, "lean") for p in sorted(package_dir.iterdir()) if p.is_dir())
        except OSError as exc:
            errors.append(dict(path=str(package_dir), error=str(exc)))
    items = []
    seen: set[str] = set()
    ignored = {".lake", ".git", "node_modules", "__pycache__", ".venv"}
    for base, package, collection in roots:
        if not base.exists():
            continue
        def onerror(exc: OSError) -> None:
            errors.append(dict(path=str(exc.filename), error=str(exc)))
        for directory, dirs, files in os.walk(base, onerror=onerror, followlinks=False):
            dirs[:] = sorted(d for d in dirs if d not in ignored)
            for filename in sorted(files):
                p = Path(directory) / filename
                if p.suffix not in {".lean", ".md"}:
                    continue
                # Generated catalogs copy the corpus; do not multiply every hit.
                if p.name in {"LEAN_API.md", "LEAN_OVERVIEW.md", "LEAN_GAPS.md"}:
                    continue
                path = str(p.relative_to(root))
                if path in seen:
                    continue
                seen.add(path)
                module = ".".join(p.relative_to(base).with_suffix("").parts)
                kind = "lean" if p.suffix == ".lean" else "prose"
                item = dict(path=path, abspath=str(p), module=module, package=package, collection=kind)
                try:
                    stat = p.stat()
                    item.update(size=stat.st_size, mtime_ns=stat.st_mtime_ns)
                except OSError as exc:
                    item.update(size=0, mtime_ns=0, error=str(exc))
                items.append(item)
    return sorted(items, key=lambda item: (source_priority(item['path']), item['path'])), errors


class Corpus:
    def __init__(self, directory: Path, *, readonly: bool = False):
        self.directory = directory
        self.path = directory / "corpus.sqlite3"
        if readonly:
            self.con = sqlite3.connect(self.path.as_uri() + "?mode=ro", uri=True, timeout=.1)
        else:
            directory.mkdir(parents=True, exist_ok=True)
            self.con = sqlite3.connect(self.path, timeout=.1)
            self.con.execute("PRAGMA journal_mode=WAL")
            self.con.execute("PRAGMA synchronous=NORMAL")
            self.con.executescript(SCHEMA)
            self.con.execute('DROP TRIGGER IF EXISTS embedding_insert')
            self.con.execute('DROP TRIGGER IF EXISTS embedding_update')
            if 'extractor_version' not in {r[1] for r in self.con.execute('PRAGMA table_info(files)')}:
                self.con.execute("ALTER TABLE files ADD COLUMN extractor_version TEXT NOT NULL DEFAULT ''")
            self.con.execute("INSERT OR IGNORE INTO meta VALUES('generation','0')")
            self.con.execute("INSERT OR IGNORE INTO meta VALUES('evidence_epoch','0')")
            self.con.commit()
        self.con.row_factory = sqlite3.Row
        self.con.execute("PRAGMA foreign_keys=ON")

    def __enter__(self):
        return self

    def __exit__(self, *args):
        self.close()

    def close(self):
        self.con.close()

    @property
    def generation(self) -> int:
        return int(self.con.execute("SELECT value FROM meta WHERE key='generation'").fetchone()[0])

    @property
    def evidence_epoch(self) -> int:
        return int(self.con.execute("SELECT value FROM meta WHERE key='evidence_epoch'").fetchone()[0])

    def bump(self, *, source=False):
        self.con.execute("UPDATE meta SET value=CAST(value AS INTEGER)+1 WHERE key='generation'")
        if source:
            self.con.execute("UPDATE meta SET value=CAST(value AS INTEGER)+1 WHERE key='evidence_epoch'")

    def _document(self, decl_id, path, module, view, text, line, end_line, provenance):
        if not text.strip():
            return
        self.con.execute("INSERT INTO documents(decl_id,path,module,view,line,end_line,text,content_hash,provenance) "
                         "VALUES(?,?,?,?,?,?,?,?,?)", (decl_id, path, module, view, line, end_line,
                                                      text, digest(text), json.dumps(provenance)))

    def refresh(self, root: Path, *, deadline: float = float("inf"), progress=None) -> dict:
        with (self.directory / 'source.lock').open('a') as lock:
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                return dict(changed=0, removed=0, failed=0, complete=False,
                            reason='source_indexer_busy', coverage=self.coverage())
            return self._refresh(root, deadline=deadline, progress=progress)

    def _refresh(self, root: Path, *, deadline: float, progress=None) -> dict:
        items, errors = inventory(root)
        current = {r["path"]: r for r in self.con.execute("SELECT path,size,mtime_ns,status,extractor_version,source_hash,toolchain,compile_status FROM files")}
        changed = failed = 0
        complete = True
        toolchain_file = root / "formal" / "lean-toolchain"
        toolchain = toolchain_file.read_text().strip() if toolchain_file.exists() else "unknown"
        manifest = root / 'formal' / 'lake-manifest.json'
        manifest_hash = digest(manifest.read_bytes()) if manifest.exists() else None
        # Register the complete inventory before bounded work starts. Each file
        # has an explicit outcome, including files awaiting their first parse.
        with self.con:
            inventory_changed = False
            for item in items:
                previous = current.get(item["path"])
                if previous is None:
                    self.con.execute("INSERT OR IGNORE INTO files(path,module,package,collection,size,mtime_ns,status,updated) VALUES(?,?,?,?,?,?,'pending',?)",
                                     (item["path"], item["module"], item["package"], item["collection"], item["size"], item["mtime_ns"], time.time()))
                    inventory_changed = True
                elif (previous["size"], previous["mtime_ns"]) != (item["size"], item["mtime_ns"]) or previous['extractor_version'] != EXTRACTION_VERSION:
                    self.con.execute("UPDATE files SET status='stale',compile_status='stale' WHERE path=?", (item["path"],))
                    inventory_changed = previous['status'] != 'stale' or inventory_changed
            if inventory_changed:
                self.bump(source=True)
        for number, item in enumerate(items):
            if time.monotonic() >= deadline:
                complete = False
                break
            previous = current.get(item["path"])
            if previous and previous["size"] == item["size"] and previous["mtime_ns"] == item["mtime_ns"] and previous["status"] == "indexed" and previous['extractor_version'] == EXTRACTION_VERSION:
                continue
            try:
                if item.get("error"):
                    raise OSError(item["error"])
                p = Path(item["abspath"])
                before = p.stat()
                raw = p.read_bytes()
                after = p.stat()
                if (before.st_size, before.st_mtime_ns) != (after.st_size, after.st_mtime_ns):
                    raise OSError("source changed during extraction; retry pending")
                text = raw.decode("utf-8")
                source_changed = not previous or previous['source_hash'] != digest(raw) or previous['toolchain'] != toolchain
                if not source_changed and previous['extractor_version'] == EXTRACTION_VERSION:
                    with self.con:
                        self.con.execute("UPDATE files SET size=?,mtime_ns=?,status='indexed',error='',compile_status=?,updated=? WHERE path=?",
                                         (after.st_size, after.st_mtime_ns, previous['compile_status'], time.time(), item['path']))
                    continue
                declarations = source_declarations(text, item["module"], item["path"]) if item["collection"] == "lean" else []
                imports = [n for m in IMPORT.finditer(mask_comments_strings(text)) for n in m.group(1).split()]
                with self.con:
                    old_names = [r[0] for r in self.con.execute("SELECT name FROM declarations WHERE path=?", (item["path"],))]
                    if source_changed:
                        self._invalidate_dependents(old_names, deadline=deadline)
                    self.con.execute("DELETE FROM files WHERE path=?", (item["path"],))
                    self.con.execute("INSERT INTO files(path,module,package,collection,size,mtime_ns,source_hash,status,imports,toolchain,updated) "
                                     "VALUES(?,?,?,?,?,?,?,?,?,?,?)", (item["path"], item["module"], item["package"],
                                     item["collection"], after.st_size, after.st_mtime_ns, digest(raw), "indexed", json.dumps(imports), toolchain, time.time()))
                    self.con.execute('UPDATE files SET extractor_version=?,compile_status=? WHERE path=?',
                                     (EXTRACTION_VERSION, 'pending' if item['collection']=='lean' else 'not_applicable', item['path']))
                    stage = next((p for p in Path(item['path']).parts if re.match(r'^[0-5]-(backlog|in-progress|fully-proven|formalized|publication-ready|failed)$', p)), None)
                    provenance = dict(kind="source", source_hash=digest(raw), toolchain=toolchain, status="source_only",
                                      extraction_version=EXTRACTION_VERSION, package=item['package'], manifest_hash=manifest_hash, recorded_stage=stage)
                    for d in declarations:
                        self.con.execute("INSERT INTO declarations(id,path,name,module,kind,line,end_line,statement,proof,doc,source_hash) "
                                         "VALUES(:id,:path,:name,:module,:kind,:line,:end_line,:statement,:proof,:doc,:source_hash)", d)
                        # Conservative source references support invalidation
                        # before compiler enrichment. They are not proof edges.
                        for token in set(re.findall(r"[\w][\w'.]*", mask_comments_strings(d['proof']))):
                            self.con.execute("INSERT OR IGNORE INTO dependencies VALUES(?,?,'source_reference')", (d['id'], token))
                        statement_text = d["name"] + "\n" + split_identifier(d["name"]) + "\n" + d["doc"] + "\n" + d["statement"]
                        for part, first, last in chunks(statement_text, d["line"]):
                            self._document(d["id"], item["path"], item["module"], "statement", part, d["line"], d["end_line"], provenance)
                        if d["proof"]:
                            for part, first, last in chunks(d["proof"], d["proof_line"]):
                                self._document(d["id"], item["path"], item["module"], "proof", part, first, last, provenance)
                    # The source view is exhaustive, even for unsupported syntax,
                    # anonymous examples, commands, comments and prose documents.
                    for part, first, last in chunks(text):
                        self._document(None, item["path"], item["module"], item["collection"], part, first, last, provenance)
                    self.bump(source=True)
                changed += 1
            except (OSError, UnicodeError, ValueError) as exc:
                with self.con:
                    # Keep last-good records, but never label them current.
                    self.con.execute("INSERT INTO files(path,module,package,collection,size,mtime_ns,status,error,updated) "
                                     "VALUES(?,?,?,?,?,?,?,?,?) ON CONFLICT(path) DO UPDATE SET status=excluded.status,error=excluded.error,updated=excluded.updated",
                                     (item["path"], item["module"], item["package"], item["collection"], item["size"], item["mtime_ns"], "failed", str(exc), time.time()))
                    self.bump(source=True)
                failed += 1
            if progress and (changed + failed) % 1000 == 0:
                progress(dict(visited=number + 1, total=len(items), changed=changed, failed=failed))
        removed = 0
        # Never interpret a traversal failure as deletion of a whole directory.
        if complete and not errors:
            known = {i["path"] for i in items}
            with self.con:
                for path in current.keys() - known:
                    names = [r[0] for r in self.con.execute("SELECT name FROM declarations WHERE path=?", (path,))]
                    self._invalidate_dependents(names)
                    self.con.execute("DELETE FROM files WHERE path=?", (path,))
                    removed += 1
                if removed:
                    self.bump(source=True)
        with self.con:
            for key, value in {"inventory_count": len(items), "inventory_errors": errors,
                               "inventory_complete": complete, "inventory_at": time.time()}.items():
                self.con.execute("INSERT OR REPLACE INTO meta VALUES(?,?)", (key, json.dumps(value)))
        return dict(changed=changed, removed=removed, failed=failed, complete=complete,
                    inventory_errors=errors, coverage=self.coverage())

    def _invalidate_dependents(self, names, *, deadline=float('inf')):
        if not names or not self.con.execute("SELECT 1 FROM methods WHERE status='ready' UNION ALL SELECT 1 FROM method_chunks LIMIT 1").fetchone():
            return
        stop = min(deadline, time.monotonic() + 2)
        pending = [variant for name in names for variant in (name, name.rsplit('.', 1)[-1])]
        seen = set()
        self.con.set_progress_handler(lambda: int(time.monotonic() >= stop), 1000)
        try:
            while pending:
                if time.monotonic() >= stop:
                    raise TimeoutError('dependency invalidation budget')
                name = pending.pop()
                if name in seen:
                    continue
                seen.add(name)
                rows = self.con.execute("SELECT d.id,d.name FROM declarations d JOIN dependencies e ON e.source=d.id WHERE e.target=?", (name,)).fetchall()
                for row in rows:
                    self.con.execute("UPDATE methods SET status='stale' WHERE decl_id=?", (row['id'],))
                    self.con.execute("DELETE FROM documents WHERE decl_id=? AND view='method'", (row['id'],))
                    self.con.execute('DELETE FROM method_chunks WHERE decl_id=?', (row['id'],))
                    pending.extend((row['name'], row['name'].rsplit('.', 1)[-1]))
        except (TimeoutError, sqlite3.OperationalError) as exc:
            if isinstance(exc, sqlite3.OperationalError) and 'interrupted' not in str(exc):
                raise
            self.con.set_progress_handler(None, 0)
            # Conservative invalidation preserves correctness when a broad
            # source-reference graph cannot be traversed within the file budget.
            # Raw sources/vectors remain available while descriptions regenerate.
            self.con.execute("UPDATE methods SET status='stale' WHERE status='ready'")
            self.con.execute("DELETE FROM documents WHERE view='method'")
            self.con.execute('DELETE FROM method_chunks')
            self.con.execute("INSERT OR REPLACE INTO meta VALUES('invalidation_fallback',?)",
                             (json.dumps(dict(reason='dependency_graph_budget', at=time.time())),))
        finally:
            self.con.set_progress_handler(None, 0)

    def coverage(self) -> dict:
        counts = lambda table, field: {r[0]: r[1] for r in self.con.execute(f"SELECT {field},COUNT(*) FROM {table} GROUP BY {field}")}
        total = self.con.execute("SELECT COUNT(*) FROM files").fetchone()[0]
        meta = {r[0]: r[1] for r in self.con.execute("SELECT key,value FROM meta")}
        inventory_count = int(meta.get("inventory_count", total))
        pending = self.con.execute("SELECT COUNT(*) FROM files WHERE status IN ('pending','stale')").fetchone()[0]
        return dict(files=total, inventoried=inventory_count, pending_files=pending + max(0, inventory_count - total),
                    outcomes=counts("files", "status"), compiler=counts("files", "compile_status"),
                    collections=counts("files", "collection"), declarations=self.con.execute("SELECT COUNT(*) FROM declarations").fetchone()[0],
                    documents=self.con.execute("SELECT COUNT(*) FROM documents").fetchone()[0],
                    vectors=self.con.execute("SELECT COUNT(*) FROM vectors").fetchone()[0], methods=counts("methods", "status"),
                    inventory_errors=json.loads(meta.get("inventory_errors", "[]")),
                    inventory_complete=json.loads(meta.get("inventory_complete", "false")), generation=self.generation)

    def install_compiler_rows(self, path: str, rows: list[dict], *, source_hash: str, status="checked") -> int:
        current = self.con.execute("SELECT * FROM files WHERE path=?", (path,)).fetchone()
        if not current or current["source_hash"] != source_hash:
            return 0
        applied = 0
        with self.con:
            for row in rows:
                match = self.con.execute("SELECT * FROM declarations WHERE path=? AND name=?", (path, row["name"])).fetchone()
                source = row.get('source') or {}
                source_range = source.get('range') or {}
                selection_range = source.get('selection_range') or source_range
                line = row.get('line') or (selection_range.get('start') or {}).get('line') or 1
                end_line = (source_range.get('end') or {}).get('line') or line
                if not match:
                    # Compiler-private names can carry a generated prefix; source
                    # line fallback is accepted only when unique and provided.
                    candidates = self.con.execute("SELECT * FROM declarations WHERE path=? AND line=?", (path, line)).fetchall()
                    candidates = [d for d in candidates if row['name'].endswith('.' + d['name']) or row['name'].endswith('.' + d['name'].rsplit('.', 1)[-1])]
                    if len(candidates) == 1:
                        match = candidates[0]
                    else:
                        # Constructors, instances and compiler-generated names
                        # absent from the provisional parser still get records.
                        did = digest(path + '\0compiler\0' + row['name'])
                        self.con.execute("INSERT OR IGNORE INTO declarations(id,path,name,module,kind,line,end_line,statement,proof,doc,source_hash) VALUES(?,?,?,?,?,?,?,?,'',?,?)",
                                         (did, path, row['name'], row['module'], row.get('kind') or 'unknown', line, end_line,
                                          row.get('type_text') or '', row.get('doc') or '', source_hash))
                        match = self.con.execute('SELECT * FROM declarations WHERE id=?', (did,)).fetchone()
                did = match["id"]
                self.con.execute("UPDATE declarations SET name=?,type_text=?,type_shape=?,binders=?,axioms=?,compiler_status=? WHERE id=?",
                                 (row["name"], row.get("type_text") or "", row.get("type_shape") or "", json.dumps(row.get("binders") or []),
                                  json.dumps(row["axioms"]) if row.get("axioms") is not None else None,
                                  'extraction_failed' if row.get('status') == 'error' else status, did))
                self.con.execute('INSERT OR REPLACE INTO compiler_metadata VALUES(?,?)', (did, json.dumps(row)))
                self.con.execute("DELETE FROM dependencies WHERE source=? AND kind<>'source_reference'", (did,))
                for kind, field in (("type", "type_dependencies"), ("proof", "proof_dependencies")):
                    for target in row.get(field, []) or []:
                        self.con.execute("INSERT OR IGNORE INTO dependencies VALUES(?,?,?)", (did, target, kind))
                self.con.execute("DELETE FROM documents WHERE decl_id=? AND view IN ('type','shape')", (did,))
                for view, field in (("type", "type_text"), ("shape", "type_shape")):
                    for part, _, _ in chunks(row.get(field) or ""):
                        self._document(did, path, match["module"], view, part, match["line"], match["end_line"],
                                       dict(kind="compiler", source_hash=source_hash, status=status, toolchain=current["toolchain"]))
                applied += 1
            self.con.execute("UPDATE files SET compile_status=? WHERE path=?", (status, path))
            if applied:
                self.bump(source=True)
        return applied

    def declaration(self, did: str) -> dict | None:
        row = self.con.execute("SELECT d.*,f.package,f.status AS file_status,f.compile_status FROM declarations d JOIN files f ON f.path=d.path WHERE d.id=?", (did,)).fetchone()
        if not row:
            return None
        out = dict(row)
        for key in ("binders", "axioms"):
            out[key] = json.loads(out[key]) if out[key] is not None else None
        out["dependencies"] = [dict(r) for r in self.con.execute("SELECT target,kind FROM dependencies WHERE source=?", (did,))]
        metadata = self.con.execute('SELECT payload FROM compiler_metadata WHERE decl_id=?', (did,)).fetchone()
        out['compiler_metadata'] = json.loads(metadata[0]) if metadata else None
        return out

    def search(self, query: str, *, views=("statement", "type"), limit=100, any_terms=False,
               exact=False, module="", exclude_modules=(), deadline=float("inf")) -> list[dict]:
        expression = build_match_expression(query, any_terms=any_terms, exact=exact)
        if not expression:
            return []
        clauses = ["document_fts MATCH ?", "d.view IN (%s)" % ",".join("?" for _ in views)]
        params = [expression, *views]
        if module:
            clauses.append("instr(lower(d.module),lower(?))>0")
            params.append(module)
        for excluded in exclude_modules:
            clauses.append("instr(lower(d.module),lower(?))=0")
            params.append(excluded)
        sql = ("SELECT d.*,bm25(document_fts,1.0,0.15,0.0) AS score FROM document_fts JOIN documents d ON d.id=document_fts.rowid WHERE "
               + " AND ".join(clauses) + " ORDER BY score,d.id LIMIT ?")
        self.con.set_progress_handler(lambda: int(time.monotonic() >= deadline), 1000)
        try:
            return [dict(r) for r in self.con.execute(sql, [*params, limit])]
        finally:
            self.con.set_progress_handler(None, 0)

    def neighbors(self, ids: list[str], *, limit=100) -> list[dict]:
        if not ids:
            return []
        placeholders = ",".join("?" for _ in ids)
        sql = ("SELECT DISTINCT d.* FROM dependencies e JOIN declarations d ON d.name=e.target "
               f"WHERE e.source IN ({placeholders}) ORDER BY d.name LIMIT ?")
        return [dict(r) for r in self.con.execute(sql, [*ids, limit])]

    def save_method(self, did: str, payload: dict, *, model_version: str, prompt_version: str,
                    expected_source_hash: str | None = None, expected_evidence_epoch: int | None = None) -> None:
        d = self.declaration(did)
        if not d:
            raise ValueError("method references a missing declaration")
        if expected_source_hash is not None and expected_source_hash != d['source_hash']:
            raise ValueError('source changed while method was being generated')
        evidence = payload.get("evidence", [])
        if not isinstance(evidence, list) or not evidence or any(not isinstance(e, str) or not e.strip() or e not in d["proof"] for e in evidence):
            raise ValueError("method evidence must be exact nonempty spans of the source proof")
        for key in ("description", "assumptions", "steps", "obligations"):
            if key not in payload:
                raise ValueError("method missing " + key)
        if not isinstance(payload['description'], str) or not payload['description'].strip():
            raise ValueError('method description must be nonempty text')
        for key in ('assumptions', 'steps', 'obligations'):
            if not isinstance(payload[key], list) or not all(isinstance(x, str) for x in payload[key]):
                raise ValueError('method ' + key + ' must be a list of strings')
        with self.con:
            # Acquire the writer lock before rechecking evidence. No concurrent
            # source/dependency transaction may slip between this check and save.
            self.con.execute("UPDATE meta SET value=value WHERE key='evidence_epoch'")
            if expected_evidence_epoch is not None and expected_evidence_epoch != self.evidence_epoch:
                raise EvidenceChanged('source or dependency evidence changed during method generation')
            current = self.declaration(did)
            if not current or current['source_hash'] != d['source_hash'] or current['file_status'] != 'indexed':
                raise EvidenceChanged('source changed during method generation')
            self.con.execute("INSERT OR REPLACE INTO methods VALUES(?,?,?,?,?,?,?,?,?,'ready','')",
                             (did, d["source_hash"], model_version, prompt_version, str(payload["description"]),
                              json.dumps(payload["assumptions"]), json.dumps(payload["steps"]),
                              json.dumps(payload["obligations"]), json.dumps(evidence)))
            self.con.execute("DELETE FROM documents WHERE decl_id=? AND view='method'", (did,))
            text = "\n".join(str(payload[k]) for k in ("description", "assumptions", "steps", "obligations"))
            for part, _, _ in chunks(text):
                self._document(did, d["path"], d["module"], "method", part, d["line"], d["end_line"],
                               dict(kind="generated", source_hash=d["source_hash"], model=model_version, prompt=prompt_version, evidence=evidence))
            self.bump()

    def method_chunk(self, did: str, chunk_hash: str, model: str, prompt: str):
        row = self.con.execute('SELECT c.payload FROM method_chunks c JOIN declarations d ON d.id=c.decl_id '
                               'WHERE c.decl_id=? AND c.chunk_hash=? AND c.model_version=? AND c.prompt_version=? '
                               'AND c.source_hash=d.source_hash', (did, chunk_hash, model, prompt)).fetchone()
        return json.loads(row[0]) if row else None

    def save_method_chunk(self, d: dict, chunk_hash: str, payload: dict, model: str, prompt: str, epoch: int):
        with self.con:
            self.con.execute("UPDATE meta SET value=value WHERE key='evidence_epoch'")
            current = self.declaration(d['id'])
            if epoch != self.evidence_epoch or not current or current['source_hash'] != d['source_hash'] or current['file_status'] != 'indexed':
                raise EvidenceChanged('source or dependency evidence changed during method generation')
            self.con.execute('INSERT OR REPLACE INTO method_chunks VALUES(?,?,?,?,?,?)',
                             (d['id'], chunk_hash, d['source_hash'], model, prompt, json.dumps(payload)))

    def method(self, did: str) -> dict | None:
        row = self.con.execute("SELECT * FROM methods WHERE decl_id=? AND status='ready'", (did,)).fetchone()
        if not row:
            return None
        result = dict(row)
        for key in ("assumptions", "steps", "obligations", "evidence"):
            result[key] = json.loads(result[key])
        return result

    def cached(self, key: str) -> dict | None:
        row = self.con.execute("SELECT result FROM cache WHERE key=? AND generation=?", (key, self.generation)).fetchone()
        return json.loads(row[0]) if row else None

    def cache(self, key: str, result: dict):
        with self.con:
            self.con.execute("INSERT OR REPLACE INTO cache VALUES(?,?,?,?)", (key, self.generation, json.dumps(result), time.time()))
            self.con.execute("DELETE FROM cache WHERE generation<>? OR created<?", (self.generation, time.time() - 86400))
