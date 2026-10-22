"""Local Qdrant retrieval and resumable publication from the SQLite outbox."""
from __future__ import annotations

import argparse
import hashlib
import http.client
import json
import math
from pathlib import Path
import time
from urllib.parse import urlsplit, quote

from lean_search_index import module_matches

IMAGE = 'qdrant/qdrant@sha256:12364fe851b9f17356fc88189fc06d1b521262e04659ec7345975b00c9246a10'
CONTAINER = 'hgt-research-qdrant'
VOLUME = 'hgt-research-qdrant'
DEFAULT_URL = 'http://127.0.0.1:16333'


def settings(directory):
    path = directory / 'qdrant.json'
    value = json.loads(path.read_text()) if path.exists() else {}
    return {'url': DEFAULT_URL, 'prefix': 'hgt_' + hashlib.sha256(str(directory.resolve()).encode()).hexdigest()[:12],
            'container': CONTAINER, 'volume': VOLUME, **value}


class Qdrant:
    def __init__(self, directory):
        self.config = settings(directory)
        self.url = urlsplit(self.config['url'])
        if self.url.scheme != 'http' or self.url.hostname not in ('127.0.0.1', 'localhost', '::1'):
            raise ValueError('Research Qdrant must use a local HTTP endpoint')

    def collection(self, model):
        return self.config['prefix'] + '_' + hashlib.sha256(model.encode()).hexdigest()[:16]

    def request(self, method, path, data=None, *, deadline=float('inf'), missing_ok=False):
        left = deadline - time.monotonic()
        if left <= 0:
            raise TimeoutError('Qdrant deadline exceeded')
        body = json.dumps(data, allow_nan=False).encode() if data is not None else None
        left = deadline - time.monotonic()
        if left <= 0:
            raise TimeoutError('Qdrant deadline exceeded')
        connection = http.client.HTTPConnection(self.url.hostname, self.url.port, timeout=min(30, left))
        try:
            connection.request(method, path, body, {'Content-Type': 'application/json'})
            response = connection.getresponse()
            raw = response.read()
            if response.status == 404 and missing_ok:
                return None
            if response.status >= 300:
                raise RuntimeError(f'Qdrant HTTP {response.status}: {raw.decode(errors="replace")[:800]}')
            if time.monotonic() > deadline:
                raise TimeoutError('Qdrant deadline exceeded')
            result = json.loads(raw)
            return result.get('result', result)
        except TimeoutError as exc:
            raise TimeoutError('Qdrant request timed out within its search budget') from exc
        except (OSError, http.client.HTTPException) as exc:
            raise RuntimeError('Local Qdrant unavailable; run ./launch.sh. ' + str(exc)) from exc
        finally:
            connection.close()

    def ensure(self, model, dimensions, *, deadline=float('inf')):
        path = '/collections/' + self.collection(model)
        existing = self.request('GET', path, deadline=deadline, missing_ok=True)
        if existing is None:
            # Memory tiers (Qdrant >=1.19): originals stay cold on disk and the
            # int8 copy is pinned. The HNSW graph keeps the default `cached`
            # tier: it is small next to the vectors and is traversed with
            # hnsw_ef=512 on every query, so paging it in cold costs latency
            # for no meaningful saving.
            self.request('PUT', path, dict(vectors=dict(size=dimensions, distance='Cosine', memory='cold'),
                hnsw_config=dict(m=16, ef_construct=100, max_indexing_threads=4),
                quantization_config=dict(scalar=dict(type='int8', memory='pinned')),
                optimizers_config=dict(max_optimization_threads=1, default_segment_number=4), on_disk_payload=True), deadline=deadline)
            for key in ('module', 'view'):
                self.request('PUT', path + '/index?wait=true', dict(field_name=key, field_schema='keyword'), deadline=deadline)
            # A token index on the module lets `--exclude-module` be answered
            # server side with a constant-size clause. Token matching is a
            # SUBSET of the substring semantics, so it may only under-exclude;
            # the exact SQLite post-filter removes the remainder.
            self.request('PUT', path + '/index?wait=true', dict(field_name='module_tokens',
                field_schema=dict(type='text', tokenizer='word', lowercase=True,
                                  min_token_len=1, max_token_len=60)), deadline=deadline)
        elif existing['config']['params']['vectors']['size'] != dimensions:
            raise ValueError('Qdrant dimension differs from embedding model')
        return path


# An enumerated `match.any` module list is exact but costs one JSON value per
# module, so it is sent only while the list is small.
MODULE_FILTER_VALUES = 512
MAX_PAGE = 1024
MAX_SCANNED = 4096
MIN_HNSW_EF = 512
SQL_VARIABLES = 900


def module_filter(corpus, module, exclude_modules):
    """Build a filter that never excludes a document `module_matches` accepts.

    An inclusion clause must be exact or a superset: a token clause can miss an
    infix match (`--module Tower` against `RHTower`), so inclusions are either
    enumerated exactly or left to the exact SQLite post-filter. An exclusion
    clause may be a subset, since under-excluding only yields extra candidates
    the post-filter drops; those use one constant-size token clause each.
    """
    must, must_not, exhaustive = [], [], True
    for term in exclude_modules:
        must_not.append(dict(key='module_tokens', match=dict(text=term)))
    if module:
        modules = [r[0] for r in corpus.con.execute('SELECT DISTINCT module FROM files')
                   if module_matches(r[0], module)]
        if not modules:
            return None, None, True
        if len(modules) <= MODULE_FILTER_VALUES:
            must.append(dict(key='module', match=dict(any=modules)))
        else:
            # Too broad to enumerate; rely on the post-filter and page instead.
            exhaustive = False
    return must, must_not, exhaustive


def hydrate(corpus, hits, model, views, module, exclude_modules):
    """Resolve a whole page in batched queries, never one round-trip per hit."""
    order = {}
    for hit in hits:
        order.setdefault(hit['id'], hit)
    rows = {}
    ids = list(order)
    for start in range(0, len(ids), SQL_VARIABLES):
        block = ids[start:start + SQL_VARIABLES]
        for row in corpus.con.execute(
                'SELECT d.*,v.model AS vector_model,v.content_hash AS vector_hash '
                'FROM documents d JOIN vectors v ON v.doc_id=d.id WHERE d.id IN (%s)'
                % ','.join('?' for _ in block), block):
            rows[row['id']] = row
    result = []
    for did, hit in order.items():
        row = rows.get(did)
        payload = hit.get('payload') or {}
        if (row and row['vector_model'] == model and row['vector_hash'] == row['content_hash']
                and row['content_hash'] == payload.get('content_hash') and row['view'] in views
                and row['module'] == payload.get('module') and row['view'] == payload.get('view')
                and module_matches(row['module'], module, exclude_modules)):
            value = dict(row)
            value.pop('vector_model'); value.pop('vector_hash')
            value['score'] = float(hit['score'])
            result.append(value)
    return result


def search(corpus, embedding, *, model, views, limit=100, module='', exclude_modules=(), deadline=float('inf')):
    if limit <= 0 or not views:
        return []
    if time.monotonic() >= deadline:
        raise TimeoutError('Qdrant deadline exceeded')
    if not embedding or not all(math.isfinite(float(x)) for x in embedding):
        raise ValueError('Invalid query embedding')
    client = Qdrant(corpus.directory)
    must, must_not, exhaustive = module_filter(corpus, module, exclude_modules)
    if must is None:
        return []
    must.append(dict(key='view', match=dict(any=list(views))))
    query_filter = dict(must=must)
    if must_not:
        query_filter['must_not'] = must_not
    # A filter left to the post-filter returns mostly non-matching hits, so it
    # starts from a wider page rather than discovering that by widening.
    collected, offset = {}, 0
    count = max(64, limit * 2) if exhaustive else max(256, limit * 4)
    while True:
        left = deadline - time.monotonic()
        if left <= 0:
            raise TimeoutError('Qdrant deadline exceeded')
        path = '/collections/' + client.collection(model) + '/points/query'
        if math.isfinite(left):
            path += '?timeout=' + str(max(1, math.ceil(left)))
        # Page with an offset: widening by re-querying from rank zero repeated
        # every comparison already paid for in the previous round. HNSW must
        # explore at least offset+limit candidates for a page to mean anything,
        # so ef tracks the depth actually requested.
        result = client.request('POST', path, dict(query=list(embedding), filter=query_filter,
            limit=count, offset=offset, with_payload=True, with_vector=False,
            params=dict(hnsw_ef=max(MIN_HNSW_EF, min(MAX_SCANNED, offset + count)),
                        quantization=dict(rescore=True, oversampling=2.0))), deadline=deadline, missing_ok=True)
        if result is None:
            return []
        hits = result['points']
        for row in hydrate(corpus, hits, model, views, module, exclude_modules):
            if row['id'] not in collected or collected[row['id']]['score'] < row['score']:
                collected[row['id']] = row
        offset += len(hits)
        if len(collected) >= limit or len(hits) < count or offset >= MAX_SCANNED:
            break
        count = min(MAX_PAGE, count * 2)
    return sorted(collected.values(), key=lambda r: (-r['score'], r['id']))[:limit]


def sync(corpus, *, deadline, batch_size=256):
    """Network writes precede receipts; acknowledgement only removes the observed queue sequence."""
    from lean_research_vectors import FaissVectors
    client = Qdrant(corpus.directory)
    report = dict(upserted=0, deleted=0, pending=0, backend='qdrant')
    archive = None
    loaded_name, loaded = None, None
    ensured = set()
    while time.monotonic() < deadline:
        queued = corpus.con.execute('SELECT * FROM qdrant_queue ORDER BY seq LIMIT ?', (batch_size,)).fetchall()
        if not queued:
            break
        operations = {}
        resolved = []
        for entry in queued:
            row = corpus.con.execute('SELECT d.*,v.model,v.content_hash AS vector_hash,s.filename '
                'FROM documents d JOIN vectors v ON v.doc_id=d.id JOIN vector_shards s ON s.id=v.shard '
                'WHERE d.id=? AND v.model=?', (entry['doc_id'], entry['model'])).fetchone()
            group = operations.setdefault(entry['model'], dict(upserts=[], deletes=[], entries=[]))
            group['entries'].append(entry)
            if row and row['content_hash'] == row['vector_hash']:
                resolved.append((entry, row))
            else:
                group['deletes'].append(entry['doc_id'])
        # Read each archive file once per batch. Queue order follows insertion,
        # not shard layout, so reconstructing in queue order reopened the same
        # index repeatedly.
        for entry, row in sorted(resolved, key=lambda pair: (pair[1]['filename'], pair[1]['id'])):
            if archive is None:
                archive = FaissVectors(corpus)
            if loaded_name != row['filename']:
                loaded = archive.faiss.read_index(str(archive.directory / row['filename']))
                loaded_name = row['filename']
            vector = loaded.reconstruct(int(row['id'])).tolist()
            # `module_tokens` carries the module again for the token index that
            # answers exclusions server side; `module` stays the exact keyword.
            operations[entry['model']]['upserts'].append(dict(id=row['id'], vector=vector,
                payload=dict(content_hash=row['content_hash'], module=row['module'],
                             module_tokens=row['module'], view=row['view'])))
        for model, group in operations.items():
            path = '/collections/' + client.collection(model)
            if group['upserts']:
                if model not in ensured:
                    client.ensure(model, len(group['upserts'][0]['vector']), deadline=deadline)
                    ensured.add(model)
                client.request('PUT', path + '/points?wait=true', dict(points=group['upserts']), deadline=deadline)
            if group['deletes']:
                client.request('POST', path + '/points/delete?wait=true', dict(points=group['deletes']),
                               deadline=deadline, missing_ok=True)
            with corpus.con:
                for point in group['upserts']:
                    payload=point['payload']
                    corpus.con.execute('INSERT OR REPLACE INTO qdrant_points SELECT d.id,v.model,d.content_hash '
                        'FROM documents d JOIN vectors v ON v.doc_id=d.id WHERE d.id=? AND v.model=? '
                        'AND v.content_hash=? AND d.content_hash=v.content_hash AND d.module=? AND d.view=?',
                        (point['id'], model, payload['content_hash'], payload['module'], payload['view']))
                for did in group['deletes']:
                    corpus.con.execute('DELETE FROM qdrant_points WHERE doc_id=? AND model=?', (did, model))
                corpus.con.executemany('DELETE FROM qdrant_queue WHERE seq=?', [(e['seq'],) for e in group['entries']])
                corpus.bump()
            report['upserted'] += len(group['upserts'])
            report['deleted'] += len(group['deletes'])
    report['pending'] = corpus.con.execute('SELECT COUNT(*) FROM qdrant_queue').fetchone()[0]
    return report


def reconcile(corpus):
    """Seed missing assignments and tombstones once; triggers maintain subsequent changes."""
    with corpus.con:
        corpus.con.execute("INSERT OR IGNORE INTO qdrant_queue(doc_id,model,operation) SELECT v.doc_id,v.model,'upsert' "
            'FROM vectors v LEFT JOIN qdrant_points p ON p.doc_id=v.doc_id AND p.model=v.model '
            'WHERE p.doc_id IS NULL OR p.content_hash<>v.content_hash')
        corpus.con.execute("INSERT OR IGNORE INTO qdrant_queue(doc_id,model,operation) SELECT p.doc_id,p.model,'delete' "
            'FROM qdrant_points p LEFT JOIN vectors v ON v.doc_id=p.doc_id AND v.model=p.model WHERE v.doc_id IS NULL')


def prune_collections(corpus, *, apply=False, deadline=float('inf')):
    """Report, and optionally drop, collections for retired embedding models.

    A retired model's collection still holds its pinned int8 copy in RAM, so a
    model swap doubles the footprint until it goes. This is never automatic: a
    populated Qdrant volume with an empty corpus database is the documented
    archive-restore path, and dropping collections there would destroy the only
    copy. It therefore refuses to act unless the database names some model.
    """
    client = Qdrant(corpus.directory)
    models = [r[0] for r in corpus.con.execute('SELECT DISTINCT model FROM vector_shards')]
    report = dict(known_models=models, keep=[], prunable=[], dropped=[], applied=bool(apply))
    if not models:
        report['refused'] = 'corpus database names no embedding model; refusing to drop any collection'
        return report
    keep = {client.collection(model) for model in models}
    listing = client.request('GET', '/collections', deadline=deadline) or {}
    for entry in listing.get('collections', []):
        name = entry.get('name', '')
        if not name.startswith(client.config['prefix']):
            continue  # Another cache's instance; never ours to touch.
        (report['keep'] if name in keep else report['prunable']).append(name)
    if apply:
        for name in report['prunable']:
            client.request('DELETE', '/collections/' + name, deadline=deadline, missing_ok=True)
            report['dropped'].append(name)
    return report


if __name__ == '__main__':
    from lean_research_corpus import Corpus
    from lean_research_batch import locks
    parser = argparse.ArgumentParser()
    parser.add_argument('--cache-dir', required=True, type=Path)
    parser.add_argument('--budget-seconds', type=float, default=30)
    parser.add_argument('--reconcile', action='store_true')
    parser.add_argument('--prune-collections', action='store_true',
                        help='report collections belonging to retired embedding models')
    parser.add_argument('--apply', action='store_true',
                        help='with --prune-collections, actually drop them')
    args = parser.parse_args()
    directory = args.cache_dir.resolve()
    try:
        with locks([directory/n for n in ('source.lock','compiler.lock','enrichment.lock')], seconds=5), Corpus(directory) as corpus:
            if args.prune_collections:
                print(json.dumps(prune_collections(corpus, apply=args.apply,
                    deadline=time.monotonic()+args.budget_seconds), indent=2), flush=True)
                raise SystemExit(0)
            if args.reconcile:
                reconcile(corpus)
            print(json.dumps(sync(corpus, deadline=time.monotonic()+args.budget_seconds)), flush=True)
    except TimeoutError as exc:
        print(json.dumps(dict(complete=False, deferred=[dict(stage='qdrant',
            reason='maintenance_busy' if str(exc).startswith('Maintenance busy:') else 'deadline', error=str(exc))])), flush=True)
