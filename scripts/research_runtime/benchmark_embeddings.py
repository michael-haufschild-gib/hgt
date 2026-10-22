"""Bounded offline comparison on fixed REAL corpus rows; no corpus writes.

Each backend runs in an owned child, preventing simultaneous model residency.
The reference encoders call the production adapter, so prefixes, mean pooling
and the text-tower load cannot drift from what actually serves searches.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sqlite3
import subprocess
import sys
import time

from .config import CONTEXT_TOKENS, DEFAULT_CACHE_DIR, RUNTIME_HOME, installation_status, offline_environment
from .processes import terminate_owned, cancellation_signals


def fixtures(cache_dir, selections=None):
    database = cache_dir/'corpus.sqlite3'
    con=sqlite3.connect(f'file:{database}?mode=ro',uri=True,timeout=1)
    con.execute('PRAGMA query_only=ON')
    groups={}
    metadata={}
    for label,view,long in (selections or [('statement','statement',False),('proof','proof',False),('long','proof',True)]):
        low,high=con.execute('SELECT min(id),max(id) FROM documents WHERE view=?',(view,)).fetchone()
        # Prose IDs are sparse clusters among declarations. Sample ordinal
        # positions in that view so ID gaps cannot repeat the same document.
        prose_ids = ([r[0] for r in con.execute('SELECT id FROM documents WHERE view=? ORDER BY id', (view,))]
                     if view == 'prose' else None)
        rows=[]
        seen=set()
        for i in range(32):
            target=low+(high-low)*i//32
            if prose_ids is not None:
                target = prose_ids[len(prose_ids)*i//32]
            extra=' AND length(text)>=4500' if long else ''
            # Long proofs are sparse in places, so two adjacent targets can land
            # on one row. Advance past a collision rather than giving up.
            while True:
                row=con.execute('SELECT id,module,content_hash,embed_text FROM documents WHERE view=? AND id>=?'+extra+
                                ' ORDER BY id LIMIT 1',(view,target)).fetchone()
                if row is None or row[0] not in seen:
                    break
                target=row[0]+1
            if row is None:
                raise RuntimeError('fixture sampling could not select 32 unique rows')
            seen.add(row[0]); rows.append(dict(zip(('id','module','content_hash','text'),row)))
        groups[label]=rows
        metadata[label]={'view':view,'count':32,'characters':sum(len(r['text']) for r in rows),
                         'min_chars':min(len(r['text']) for r in rows),'max_chars':max(len(r['text']) for r in rows)}
    con.close()
    result={'database':str(database),'sampling':'32 evenly spaced ID targets per view; long proof length >=4500',
            'groups':groups,'metadata':metadata,
            'queries':['Given a lower bound on a quadratic form, prove coercivity.',
                       'Find a theorem about continuity and convergence of a sequence.',
                       'Commutativity of addition for natural numbers.',
                       'Show that the measure of a union is at most the sum of the measures.']}
    return result


def child(backend, fixture, output, group=None):
    if backend == 'runtime':
        from lean_research_runtime import RuntimeClient
        data = json.loads(fixture.read_text())
        results = {}
        with RuntimeClient(DEFAULT_CACHE_DIR) as client:
            start = time.monotonic()
            client.embed(['theorem refl (n : ℕ) : n = n := rfl'], deadline=start+120)
            load_seconds = time.monotonic()-start
            for label, rows in data['groups'].items():
                if group and label != group:
                    continue
                start = time.monotonic()
                vectors = client.embed([r['text'] for r in rows], deadline=start+120)
                seconds = time.monotonic()-start
                results[label] = {'seconds': seconds, 'docs_per_second': len(rows)/seconds,
                                  'vectors': vectors}
                print(json.dumps({'backend': backend, 'group': label, 'seconds': seconds,
                                  'docs_per_second': len(rows)/seconds}), flush=True)
            queries = client.embed(data['queries'], query=True, deadline=time.monotonic()+120)
            status = client.status()
        output.write_text(json.dumps({'backend': backend, 'load_seconds': load_seconds,
                                     'results': results, 'queries': queries, 'status': status}))
        return
    from .adapters import LocalModels, enforce_offline
    enforce_offline()
    import numpy as np
    data = json.loads(fixture.read_text())
    # Delegate to the production adapter instead of reimplementing the task
    # prefixes, the mean pooling and the text-tower load beside it. A reference
    # that drifts from the real path fails the parity gate for the wrong reason.
    models = LocalModels(DEFAULT_CACHE_DIR)
    start = time.monotonic()
    models._torch_model('embedding', cpu=(backend == 'cpu'))
    def encode(texts, query=False):
        request = {'texts': list(texts), 'query': query, 'deadline': time.monotonic() + 600}
        return np.asarray(models._search(request, 'embedding'), dtype=np.float32)
    load_seconds = time.monotonic() - start
    batch = 4
    # One short warmup separates model load and kernel compilation from timings.
    encode(['theorem refl (n : ℕ) : n = n := rfl'])
    results = {}
    for label, rows in data['groups'].items():
        if group and label != group:
            continue
        begin = time.monotonic()
        vectors = np.concatenate([encode([r['text'] for r in rows[i:i + batch]])
                                  for i in range(0, len(rows), batch)])
        seconds = time.monotonic() - begin
        if not np.isfinite(vectors).all():
            raise RuntimeError(f'{backend}/{label} non-finite output')
        results[label] = {'seconds': seconds, 'docs_per_second': len(rows) / seconds,
                          'vectors': vectors.tolist()}
        print(json.dumps({'backend': backend, 'group': label, 'seconds': seconds,
                          'docs_per_second': len(rows) / seconds}), flush=True)
    queries = encode(data['queries'], query=True)
    output.write_text(json.dumps({'backend': backend, 'load_seconds': load_seconds,
                                  'batch_size': batch, 'results': results,
                                  'queries': queries.tolist()}))


@cancellation_signals()
def owned_run(command, seconds):
    process=subprocess.Popen(command,env=offline_environment(),start_new_session=True)
    try:
        code=process.wait(timeout=seconds)
        if code:
            raise RuntimeError(f'benchmark exited with {code}')
    finally:
        terminate_owned(process)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--backend',choices=('cpu','mps','runtime'))
    parser.add_argument('--child',action='store_true')
    parser.add_argument('--group', choices=('statement', 'proof', 'long', 'prose'))
    parser.add_argument('--fixtures-only',action='store_true')
    parser.add_argument('--prose-fixtures', action='store_true', help='append real prose without replacing existing samples')
    args=parser.parse_args()
    directory=RUNTIME_HOME/'cache'; directory.mkdir(exist_ok=True)
    fixture=directory/'real-embedding-fixtures.json'
    if args.prose_fixtures:
        data = json.loads(fixture.read_text())
        prose = fixtures(DEFAULT_CACHE_DIR, [('prose', 'prose', False)])
        data['groups'].update(prose['groups'])
        data['metadata'].update(prose['metadata'])
        fixture.write_text(json.dumps(data))
        print(json.dumps(prose['metadata']))
        return
    if args.fixtures_only:
        fixture.write_text(json.dumps(fixtures(DEFAULT_CACHE_DIR)))
        print(json.dumps(json.loads(fixture.read_text())['metadata']))
        return
    if args.child:
        suffix = '-'+args.group if args.group else ''
        child(args.backend,fixture,directory/f'embedding-{args.backend}{suffix}.json', args.group)
        return
    for backend in ([args.backend] if args.backend else ['cpu','runtime']):
        command = [sys.executable,'-m','research_runtime.benchmark_embeddings','--child','--backend',backend]
        if args.group:
            command.extend(['--group', args.group])
        owned_run(command,300)


if __name__=='__main__': main()
