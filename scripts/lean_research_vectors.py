"""Bounded FAISS shards, with SQLite publication and source-hash validation.

FAISS is optional for lexical users. A shard is immutable; publishing its
metadata and document assignments is one transaction. Aborted writes can leave
an unreferenced file, never a partly visible generation.
"""
from __future__ import annotations

import os
import sys
import time
import uuid
from pathlib import Path

from lean_research_corpus import Corpus, PATH_PRIORITY_SQL, PRIORITY_VERSION
from lean_search_index import module_matches

MAX_SHARD_DOCUMENTS = 8192
EMBED_VIEWS = ('statement', 'type', 'shape', 'proof', 'method', 'prose')


class Vectors:
    def __init__(self, corpus: Corpus):
        if sys.platform == 'darwin' and 'torch' in sys.modules:
            raise ImportError('FAISS must run separately from Torch on macOS. Use research_runtime/audit.py for isolated tests; inference belongs in the shared model worker.')
        import faiss
        import numpy as np
        self.faiss, self.np, self.corpus = faiss, np, corpus
        self.directory = corpus.directory / "vectors"

    def coverage(self, model: str) -> dict:
        expected = self.corpus.con.execute("SELECT COUNT(*) FROM documents WHERE view<>'lean'").fetchone()[0]
        ready = self.corpus.con.execute("SELECT COUNT(*) FROM vectors v JOIN documents d ON d.id=v.doc_id WHERE d.view<>'lean' AND v.model=? AND v.content_hash=d.content_hash", (model,)).fetchone()[0]
        return dict(expected=expected, ready=ready, complete=expected > 0 and ready == expected)

    def publish(self, documents: list[dict], embeddings: list[list[float]], model: str) -> int:
        if len(documents) != len(embeddings):
            raise ValueError("embedding count does not match document count")
        if not documents:
            return 0
        if len(documents) > MAX_SHARD_DOCUMENTS:
            raise ValueError("shard exceeds bounded document count")
        matrix = self.np.asarray(embeddings, dtype="float32")
        if matrix.ndim != 2 or not self.np.isfinite(matrix).all() or matrix.shape[1] > 4096:
            raise ValueError("invalid embedding matrix")
        self.faiss.normalize_L2(matrix)
        index = self.faiss.IndexIDMap2(self.faiss.IndexFlatIP(matrix.shape[1]))
        index.add_with_ids(matrix, self.np.asarray([d["id"] for d in documents], dtype="int64"))
        self.directory.mkdir(parents=True, exist_ok=True)
        sid = uuid.uuid4().hex
        target = self.directory / (sid + ".faiss")
        temporary = target.with_suffix(".tmp")
        try:
            self.faiss.write_index(index, str(temporary))
            os.replace(temporary, target)
            with self.corpus.con:
                self.corpus.con.execute("INSERT INTO vector_shards VALUES(?,?,?,?,?)", (sid, target.name, model, len(documents), time.time()))
                installed = 0
                for position, doc in enumerate(documents):
                    current = self.corpus.con.execute("SELECT content_hash FROM documents WHERE id=?", (doc["id"],)).fetchone()
                    if current and current[0] == doc["content_hash"]:
                        self.corpus.con.execute("INSERT OR REPLACE INTO vectors VALUES(?,?,?,?,?)", (doc["id"], doc["content_hash"], sid, position, model))
                        self.corpus.con.execute("INSERT OR REPLACE INTO embedding_cache VALUES(?,?,?,?)", (doc['content_hash'], model, sid, doc['id']))
                        installed += 1
                        self.corpus.con.execute('DELETE FROM embedding_queue WHERE doc_id=? AND content_hash=?', (doc['id'], doc['content_hash']))
                self.corpus.bump()
            return installed
        finally:
            temporary.unlink(missing_ok=True)

    def pending(self, model: str, *, limit=64) -> list[dict]:
        active = self.corpus.con.execute("SELECT value FROM meta WHERE key='embedding_queue_model'").fetchone()
        priority = self.corpus.con.execute("SELECT value FROM meta WHERE key='embedding_queue_priority'").fetchone()
        if not priority or priority[0] != PRIORITY_VERSION:
            with self.corpus.con:
                self.corpus.con.execute('UPDATE embedding_queue SET priority=(SELECT ' + PATH_PRIORITY_SQL +
                    " + CASE view WHEN 'method' THEN 0 WHEN 'type' THEN 1 WHEN 'statement' THEN 2 WHEN 'proof' THEN 3 WHEN 'shape' THEN 4 ELSE 5 END FROM documents WHERE id=doc_id)")
                self.corpus.con.execute("INSERT OR REPLACE INTO meta VALUES('embedding_queue_priority',?)", (PRIORITY_VERSION,))
        if not active or active[0] != model:
            with self.corpus.con:
                self.corpus.con.execute("INSERT OR REPLACE INTO embedding_queue SELECT d.id,d.content_hash,"
                    "(" + PATH_PRIORITY_SQL + ") + CASE d.view WHEN 'method' THEN 0 WHEN 'type' THEN 1 WHEN 'statement' THEN 2 WHEN 'proof' THEN 3 WHEN 'shape' THEN 4 ELSE 5 END "
                    "FROM documents d LEFT JOIN vectors v ON v.doc_id=d.id WHERE d.view<>'lean' AND (v.doc_id IS NULL OR v.content_hash<>d.content_hash OR v.model<>?)", (model,))
                self.corpus.con.execute("INSERT OR REPLACE INTO meta VALUES('embedding_queue_model',?)", (model,))
        return [dict(r) for r in self.corpus.con.execute(
            "SELECT d.* FROM embedding_queue q JOIN documents d ON d.id=q.doc_id JOIN files f ON f.path=d.path WHERE f.status='indexed' ORDER BY q.priority,q.doc_id LIMIT ?", (limit,))]

    def reuse(self, documents: list[dict], model: str) -> dict[str, list[float]]:
        """Reuse identical source chunks without repeated model inference."""
        result = {}
        loaded_name, loaded = None, None
        for document in documents:
            sha = document['content_hash']
            if sha in result:
                continue
            row = self.corpus.con.execute('SELECT v.vector_id,s.filename FROM embedding_cache v JOIN vector_shards s ON s.id=v.shard WHERE v.model=? AND v.content_hash=?', (model, sha)).fetchone()
            if not row:
                # Indexes published before the content cache was introduced.
                row = self.corpus.con.execute('SELECT v.doc_id AS vector_id,s.filename FROM vectors v JOIN vector_shards s ON s.id=v.shard WHERE v.model=? AND v.content_hash=? LIMIT 1', (model, sha)).fetchone()
            if not row:
                continue
            if loaded_name != row['filename']:
                del loaded
                loaded = self.faiss.read_index(str(self.directory / row['filename']))
                loaded_name = row['filename']
            result[sha] = loaded.reconstruct(int(row['vector_id'])).tolist()
        return result

    def search(self, embedding: list[float], *, model: str, views: tuple[str, ...], limit=100,
               module="", exclude_modules=(), deadline=float("inf")) -> list[dict]:
        query = self.np.asarray([embedding], dtype="float32")
        self.faiss.normalize_L2(query)
        results: dict[int, dict] = {}
        shards = self.corpus.con.execute("SELECT * FROM vector_shards s WHERE model=? AND EXISTS(SELECT 1 FROM vectors v WHERE v.shard=s.id) ORDER BY created DESC", (model,)).fetchall()
        for shard in shards:
            if time.monotonic() >= deadline:
                raise TimeoutError("vector search deadline exceeded")
            path = self.directory / shard["filename"]
            index = self.faiss.read_index(str(path))
            if index.d != query.shape[1]:
                raise ValueError("model dimension differs from vector shard")
            # Search the full bounded shard before filters: filtering a truncated
            # nearest-neighbor list would silently miss a requested module.
            scores, ids = index.search(query, index.ntotal)
            allowed = {r["id"]: dict(r) for r in self.corpus.con.execute(
                "SELECT d.* FROM vectors v JOIN documents d ON d.id=v.doc_id "
                "WHERE v.shard=? AND v.model=? AND v.content_hash=d.content_hash", (shard["id"], model))
                if r["view"] in views and module_matches(r["module"], module, exclude_modules)}
            for score, did in zip(scores[0], ids[0]):
                did = int(did)
                if did in allowed:
                    row = allowed[did]
                    row["score"] = float(score)
                    if did not in results or results[did]["score"] < row["score"]:
                        results[did] = row
            if len(results) > limit * 2:
                results = {r["id"]: r for r in sorted(results.values(), key=lambda r: (-r["score"], r["id"]))[:limit]}
            del index
        return sorted(results.values(), key=lambda r: (-r["score"], r["id"]))[:limit]

    def compact(self, model: str, *, deadline=float("inf")) -> dict:
        """Merge small immutable shards; never allocate more than one bounded batch."""
        shards = self.corpus.con.execute("SELECT * FROM vector_shards WHERE model=? AND count<? ORDER BY created", (model, MAX_SHARD_DOCUMENTS)).fetchall()
        docs, vectors, old = [], [], []
        total = 0
        for shard in shards:
            if time.monotonic() >= deadline:
                break
            index = self.faiss.read_index(str(self.directory / shard["filename"]))
            active = list(self.corpus.con.execute("SELECT d.* FROM vectors v JOIN documents d ON d.id=v.doc_id WHERE v.shard=? AND v.content_hash=d.content_hash", (shard["id"],)))
            for doc in active:
                docs.append(dict(doc))
                vectors.append(index.reconstruct(int(doc["id"])).tolist())
                if len(docs) == MAX_SHARD_DOCUMENTS:
                    total += self.publish(docs, vectors, model)
                    docs, vectors = [], []
            old.append(shard["id"])
            del index
        if docs:
            total += self.publish(docs, vectors, model)
        # Keep old files: an already-open reader may still be using that
        # generation. A separate offline maintenance operation may remove them.
        with self.corpus.con:
            for sid in old:
                self.corpus.con.execute("DELETE FROM vector_shards WHERE id=? AND NOT EXISTS(SELECT 1 FROM vectors WHERE shard=?) AND NOT EXISTS(SELECT 1 FROM embedding_cache WHERE shard=?)", (sid, sid, sid))
        return dict(republished=total, old_shards=len(old))
