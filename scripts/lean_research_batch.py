#!/usr/bin/env python3
"""Prepare an explicit cloud embedding bundle; safely import its completed shards.

Uses the dedicated research Python. Normal research commands never invoke this.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager, ExitStack
import fcntl
import gzip
import json
import os
from pathlib import Path
import re
import shutil
import sqlite3
import time

from lean_research_corpus import Corpus, source_priority
from research_runtime.config import (CONTEXT_TOKENS, DEFAULT_CACHE_DIR, DOCUMENT_TEMPLATE,
                                     EMBEDDING_DIMENSIONS, EMBEDDING_POOLING, MODELS,
                                     QUERY_TEMPLATE, RUNTIME_HOME, installation_status)
from research_batch.format import (FORMAT, SHARD_ROWS, atomic_bytes, atomic_json,
                                  checked_file, checked_result, descriptor, load_manifest,
                                  parity, read_shard, sha_file, sha_text)

BATCH_HOME = Path(__file__).resolve().parent / 'research_batch'
MATCH_INCOMING_SQL = ('SELECT c.id,c.content_hash,i.position FROM batch_incoming i '
                      'CROSS JOIN batch_current c INDEXED BY batch_hash ON c.content_hash=i.hash')


def embedding_spec():
    return dict(repo=MODELS['embedding']['repo'], revision=MODELS['embedding']['revision'],
                dimensions=EMBEDDING_DIMENSIONS, context_tokens=CONTEXT_TOKENS,
                padding='right', query_template=QUERY_TEMPLATE,
                document_template=DOCUMENT_TEMPLATE, pooling=EMBEDDING_POOLING,
                normalization='l2_float32', format=FORMAT)


@contextmanager
def locks(paths, *, seconds=150):
    """Maintenance cooperates with the local indexer; never kills its processes."""
    deadline = time.monotonic() + seconds
    with ExitStack() as stack:
        for path in paths:
            lock = stack.enter_context(Path(path).open('a'))
            while True:
                try:
                    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    break
                except BlockingIOError:
                    if time.monotonic() >= deadline:
                        raise TimeoutError(f'Maintenance busy: {Path(path).name}') from None
                    time.sleep(min(.1, max(0, deadline - time.monotonic())))
        yield


def snapshot(cache, directory, model):
    """Persist one committed read snapshot. No live corpus writes or ML loading."""
    target = directory / 'snapshot.sqlite3'
    if target.exists():
        con = sqlite3.connect(target)
        meta = json.loads(con.execute('SELECT value FROM meta').fetchone()[0])
        con.close()
        if meta['target_model'] != model or meta['spec'] != embedding_spec():
            raise ValueError('Existing snapshot belongs to another model; use a new directory')
        return meta
    temporary = target.with_suffix('.partial.sqlite3')
    temporary.unlink(missing_ok=True)
    con = sqlite3.connect(temporary)
    con.executescript('''
        PRAGMA journal_mode=DELETE;
        CREATE TABLE texts(hash TEXT PRIMARY KEY, text TEXT NOT NULL, priority INTEGER, view TEXT);
        CREATE TABLE files(path TEXT PRIMARY KEY, status TEXT, error TEXT, source_hash TEXT,
                           compile_status TEXT, extractor_version TEXT);
        CREATE TABLE meta(value TEXT);
    ''')
    start = time.monotonic()
    try:
        with Corpus(cache, readonly=True) as corpus:
            corpus.con.execute('BEGIN')
            generation = corpus.generation
            cached = {r[0] for r in corpus.con.execute(
                'SELECT content_hash FROM embedding_cache WHERE model=? UNION '
                'SELECT content_hash FROM vectors WHERE model=?', (model, model))}
            counts = dict(total_documents=0, eligible_documents=0, cached_documents=0,
                          exported_document_references=0)
            con.executemany('INSERT INTO files VALUES(?,?,?,?,?,?)', corpus.con.execute(
                'SELECT path,status,error,source_hash,compile_status,extractor_version FROM files'))
            cursor = corpus.con.execute('SELECT id,path,view,embed_text,content_hash FROM documents ORDER BY id')
            while rows := cursor.fetchmany(4096):
                pending = []
                for row in rows:
                    counts['total_documents'] += 1
                    if row['view'] == 'lean' or '/.lake/packages/' in row['path']:
                        continue
                    counts['eligible_documents'] += 1
                    if row['content_hash'] in cached:
                        counts['cached_documents'] += 1
                        continue
                    if sha_text(row['embed_text']) != row['content_hash']:
                        raise ValueError(f'Corpus text/hash mismatch at document {row["id"]}')
                    counts['exported_document_references'] += 1
                    pending.append((row['content_hash'], row['embed_text'], source_priority(row['path']), row['view']))
                con.executemany('INSERT INTO texts VALUES(?,?,?,?) ON CONFLICT(hash) DO UPDATE '
                                'SET priority=MIN(priority,excluded.priority)', pending)
                con.commit()
                if counts['total_documents'] // 100000 != (counts['total_documents'] - len(rows)) // 100000:
                    print(json.dumps(dict(event='snapshot', **counts)), flush=True)
            outcomes = dict(con.execute('SELECT status,COUNT(*) FROM files GROUP BY status'))
            unique = con.execute('SELECT COUNT(*) FROM texts').fetchone()[0]
            meta = dict(format=FORMAT, target_model=model, spec=embedding_spec(),
                        generation=generation, created=time.time(), file_outcomes=outcomes,
                        unique_pending=unique, snapshot_seconds=time.monotonic() - start, **counts)
        con.execute('CREATE INDEX texts_order ON texts(priority,hash)')
        con.execute('INSERT INTO meta VALUES(?)', (json.dumps(meta),))
        con.commit()
        con.close()
        os.replace(temporary, target)
        return meta
    finally:
        con.close()


def copy_checked(source, destination, expected):
    if destination.exists() and sha_file(destination) == expected['sha256']:
        return descriptor(destination)
    checked_file(source.parent, dict(name=source.name, **expected))
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = destination.with_suffix(destination.suffix + '.tmp')
    shutil.copyfile(source, temporary)
    os.replace(temporary, destination)
    return descriptor(destination)


def saved_reference(model):
    """Reuse the already measured CPU/runtime fixture, with version and parity checks."""
    import numpy as np
    directory = RUNTIME_HOME / 'cache'
    fixture = json.loads((directory / 'real-embedding-fixtures.json').read_text())
    runtime = json.loads((directory / 'embedding-runtime.json').read_text())
    cpu = json.loads((directory / 'embedding-cpu.json').read_text())
    if runtime['status']['embedding_model_version'] != model:
        raise ValueError('Saved runtime references are stale; regenerate the embedding benchmark first')
    documents, vectors, cpu_vectors, evidence = [], [], [], []
    for label, group in runtime['results'].items():
        rows = fixture['groups'][label]
        if len(rows) != len(group['vectors']) or len(rows) != len(cpu['results'][label]['vectors']):
            raise ValueError('Reference fixture length mismatch')
        for row in rows:
            if sha_text(row['text']) != row['content_hash']:
                raise ValueError('Reference source hash mismatch')
            documents.append(row['text'])
            evidence.append({k: row[k] for k in ('id', 'module', 'content_hash')})
        vectors.extend(group['vectors'])
        cpu_vectors.extend(cpu['results'][label]['vectors'])
    vectors.extend(runtime['queries'])
    cpu_vectors.extend(cpu['queries'])
    report = parity(cpu_vectors, np.asarray(vectors, dtype=np.float32), len(fixture['queries']),
                    EMBEDDING_DIMENSIONS)
    if not report['passed']:
        raise ValueError('Saved local/CPU compatibility failed')
    return dict(documents=documents, queries=fixture['queries'], vectors=vectors,
                target_model=model, evidence=evidence, local_cpu_audit=report,
                source_files=[descriptor(directory / name) for name in
                              ('real-embedding-fixtures.json', 'embedding-runtime.json', 'embedding-cpu.json')])


def prepare(cache, directory, wheelhouse=None, *, download_runtime=False):
    cache, directory = cache.resolve(), directory.resolve()
    wheelhouse = (wheelhouse or cache / 'runpod' / 'linux-wheels').resolve()
    directory.mkdir(parents=True, exist_ok=True)
    bundle = directory / 'bundle'
    bundle.mkdir(exist_ok=True)
    with locks([directory / 'prepare.lock'], seconds=0):
        status = installation_status(cache)
        if not status['ready']:
            raise ValueError(status['reason'])
        model = status['embedding_model_version']
        if (bundle / 'manifest.json').exists():
            result = load_manifest(bundle)
            if result['target_model'] != model or result['spec'] != embedding_spec():
                raise ValueError('Prepared bundle is from a different runtime; use a new directory')
            verify_bundle(bundle)
            return result
        reference = saved_reference(model)
        meta = snapshot(cache, directory, model)
        con = sqlite3.connect(directory / 'snapshot.sqlite3')
        shards = []
        try:
            (bundle / 'inputs').mkdir(exist_ok=True)
            for priority in (0, 100, 200):
                cursor = con.execute('SELECT hash,text,view FROM texts WHERE priority=? ORDER BY hash', (priority,))
                number = 0
                while rows := cursor.fetchmany(SHARD_ROWS):
                    path = bundle / 'inputs' / f'{priority:03d}-{number:05d}.jsonl.gz'
                    text = ''.join(json.dumps(dict(hash=h, text=t, view=v), ensure_ascii=False) + '\n'
                                   for h, t, v in rows)
                    payload = gzip.compress(text.encode('utf-8'), compresslevel=1, mtime=0)
                    # Deterministic shards survive interrupted preparation.
                    if not path.exists() or path.read_bytes() != payload:
                        atomic_bytes(path, payload)
                    shards.append(descriptor(path, count=len(rows), priority=priority,
                                             characters=sum(len(t) for _, t, _ in rows)))
                    number += 1
                print(json.dumps(dict(event='exported_priority', priority=priority, shards=number)), flush=True)
            inventory = ''.join(json.dumps(dict(zip(('path', 'status', 'error', 'source_hash',
                'compile_status', 'extractor_version'), row)), ensure_ascii=False) + '\n'
                for row in con.execute('SELECT * FROM files ORDER BY path'))
            atomic_bytes(bundle / 'file-outcomes.jsonl.gz', gzip.compress(inventory.encode(), compresslevel=1, mtime=0))
        finally:
            con.close()
        installed = json.loads((cache / 'runtime' / 'installed.json').read_text())['models']['embedding']
        model_files = []
        for name, expected in installed['files'].items():
            if Path(name).name != name:
                raise ValueError('Invalid model file path')
            model_files.append(copy_checked(Path(status['models']['embedding']['path']) / name,
                                            bundle / 'model' / name, expected))
        atomic_json(bundle / 'reference.json', reference)
        (bundle / 'research_batch').mkdir(exist_ok=True)
        runner_files = []
        for name in ('__init__.py', 'format.py', 'runner.py'):
            atomic_bytes(bundle / 'research_batch' / name, (BATCH_HOME / name).read_bytes())
            runner_files.append(descriptor(bundle / 'research_batch' / name))
        support_files = []
        for name in ('setup.sh', 'run.sh', 'requirements.txt', 'requirements-linux.lock', 'README.md'):
            atomic_bytes(bundle / name, (BATCH_HOME / name).read_bytes())
            support_files.append(descriptor(bundle / name))
        required = dict(re.findall(r'^([\w-]+)==([^\s]+)',
                                  (BATCH_HOME / 'requirements-linux.lock').read_text(), re.M))
        available = {(p.name.split('-')[0].replace('_', '-'), p.name.split('-')[1]): p
                     for p in wheelhouse.glob('*.whl') if '-cp311-cp311-' not in p.name}
        wheel_files = []
        pending_wheels = []
        for package, version in required.items():
            source = available.get((package, version))
            if source is None:
                if download_runtime:
                    pending_wheels.append(f'{package}=={version}')
                    continue
                raise ValueError(f'Prefetch Linux wheel {package}=={version}; see research_batch/README.md')
            wheel_files.append(copy_checked(source, bundle / 'wheelhouse' / source.name,
                                           dict(size=source.stat().st_size, sha256=sha_file(source))))
        manifest = dict(meta, shards=shards, model_files=model_files, runner_files=runner_files,
                        support_files=support_files, wheel_files=wheel_files,
                        runtime_python='3.12', offline_setup_ready=not pending_wheels,
                        pending_runtime_wheels=pending_wheels,
                        reference=descriptor(bundle / 'reference.json'),
                        file_inventory=descriptor(bundle / 'file-outcomes.jsonl.gz'))
        atomic_json(bundle / 'manifest.json', manifest)
        verify_bundle(bundle)
        return manifest


def verify_bundle(bundle):
    manifest = load_manifest(bundle)
    if manifest['spec'] != embedding_spec():
        raise ValueError('Embedding preprocessing mismatch')
    for name, folder in (('model_files', 'model'), ('runner_files', 'research_batch'),
                         ('support_files', ''), ('wheel_files', 'wheelhouse')):
        for item in manifest[name]:
            checked_file(bundle / folder, item)
    checked_file(bundle, manifest['reference'])
    checked_file(bundle, manifest['file_inventory'])
    total = sum(len(read_shard(bundle, entry)) for entry in manifest['shards'])
    if total != manifest['unique_pending']:
        raise ValueError('Manifest coverage mismatch')
    if [s['priority'] for s in manifest['shards']] != sorted(s['priority'] for s in manifest['shards']):
        raise ValueError('Corpus priority mismatch')
    return dict(verified=True, unique_vectors=total, shards=len(manifest['shards']),
                upload_bytes=sum(p.stat().st_size for p in bundle.rglob('*') if p.is_file()))


def validate_audit(bundle, output, manifest):
    import numpy as np
    path = output / 'audit.json'
    report = json.loads(path.read_text())
    manifest_sha = sha_file(bundle / 'manifest.json')
    if (report['manifest_sha256'] != manifest_sha or report['target_model'] != manifest['target_model']
            or report['reference_sha256'] != manifest['reference']['sha256']):
        raise ValueError('Audit provenance mismatch')
    if report['environment']['device'] != 'cuda' or report['environment']['dtype'] not in ('bfloat16', 'float32'):
        raise ValueError('A successful CUDA audit is required')
    reference = json.loads(checked_file(bundle, manifest['reference']).read_text())
    values = np.load(checked_file(output, report['vectors']), allow_pickle=False)
    verdict = parity(reference['vectors'], values, len(reference['queries']),
                     manifest['spec']['dimensions'])
    if not verdict['passed']:
        raise ValueError('Returned vectors failed numerical compatibility')
    return manifest_sha, sha_file(path), verdict


def import_results(cache, bundle, output, *, budget_seconds=600, lock_seconds=150):
    """Import completed shards only; later invocations resume by current hash/model."""
    from lean_research_vectors import Vectors, MAX_SHARD_DOCUMENTS
    start = time.monotonic()
    cache, bundle, output = cache.resolve(), bundle.resolve(), output.resolve()
    manifest = load_manifest(bundle)
    model = installation_status(cache)['embedding_model_version']
    if manifest['target_model'] != model or manifest['spec'] != embedding_spec():
        raise ValueError('Local model changed; refusing mixed embedding namespace')
    manifest_sha, audit_sha, audit_report = validate_audit(bundle, output, manifest)
    report = dict(published=0, checked_shards=0, pending_shards=0, unmatched_or_ready=0,
                  manifest_sha256=manifest_sha, audit_sha256=audit_sha, audit=audit_report)
    owned_locks = [cache / name for name in ('source.lock', 'compiler.lock', 'enrichment.lock')]
    with locks(owned_locks, seconds=lock_seconds), Corpus(cache) as corpus:
        corpus.con.execute('PRAGMA busy_timeout=10000')
        corpus.con.execute('PRAGMA temp_store=FILE')
        # Build once, on disk. Matching current hashes also reuses unchanged
        # chunks whose document IDs moved while the remote job was running.
        corpus.con.execute('CREATE TEMP TABLE batch_current AS SELECT d.id,d.content_hash '
            'FROM documents d JOIN files f ON f.path=d.path LEFT JOIN vectors v ON v.doc_id=d.id '
            "WHERE d.view<>'lean' AND f.status='indexed' AND "
            '(v.doc_id IS NULL OR v.content_hash<>d.content_hash OR v.model<>?)', (model,))
        corpus.con.execute('CREATE INDEX batch_hash ON batch_current(content_hash)')
        corpus.con.execute('CREATE TEMP TABLE batch_incoming(hash TEXT PRIMARY KEY, position INTEGER)')
        corpus.con.commit()
        vectors = Vectors(corpus)
        for entry in manifest['shards']:
            if time.monotonic() - start >= budget_seconds:
                report['budget_exhausted'] = True
                break
            marker = output / (entry['name'] + '.done.json')
            if not marker.exists():
                report['pending_shards'] += 1
                continue
            rows = read_shard(bundle, entry)
            _, matrix = checked_result(bundle, output, entry, manifest_sha, audit_sha,
                                       manifest['spec']['dimensions'])
            corpus.con.execute('DELETE FROM batch_incoming')
            corpus.con.executemany('INSERT INTO batch_incoming VALUES(?,?)',
                                  [(row['hash'], i) for i, row in enumerate(rows)])
            corpus.con.commit()
            # Fresh temp tables have no cardinality statistics. An ordinary JOIN
            # picked a full corpus scan for EVERY shard on the production DB.
            # Keep the bounded incoming shard outermost and probe the hash index.
            matches = corpus.con.execute(MATCH_INCOMING_SQL).fetchall()
            # A duplicate hash can map to more than one declaration/view.
            installed = 0
            for offset in range(0, len(matches), MAX_SHARD_DOCUMENTS):
                block = matches[offset:offset + MAX_SHARD_DOCUMENTS]
                # BEGIN IMMEDIATE prevents any non-cooperating source writer
                # changing IDs/hashes between validation and publication.
                corpus.con.execute('BEGIN IMMEDIATE')
                try:
                    current = []
                    positions = []
                    for row in block:
                        valid = corpus.con.execute('SELECT d.id FROM documents d LEFT JOIN vectors v ON v.doc_id=d.id '
                            'WHERE d.id=? AND d.content_hash=? AND '
                            '(v.doc_id IS NULL OR v.content_hash<>d.content_hash OR v.model<>?)',
                            (row['id'], row['content_hash'], model)).fetchone()
                        if valid:
                            current.append(dict(id=row['id'], content_hash=row['content_hash']))
                            positions.append(row['position'])
                    if current:
                        installed += vectors.publish(current, matrix[positions], model, provenance=dict(
                            kind='cuda_batch', manifest_sha256=manifest_sha,
                            input_sha256=entry['sha256'], audit_sha256=audit_sha,
                            environment=json.loads((output / 'audit.json').read_text())['environment'],
                            numerical_compatibility=audit_report))
                    else:
                        corpus.con.commit()
                except BaseException:
                    corpus.con.rollback()
                    raise
            report['published'] += installed
            report['checked_shards'] += 1
            report['unmatched_or_ready'] += len(rows) - len({row['position'] for row in matches})
            report['elapsed_seconds'] = time.monotonic() - start
            atomic_json(output / 'local-import.json', report)
            print(json.dumps(dict(event='imported', shard=entry['name'], installed=installed,
                                  total_published=report['published'])), flush=True)
    report['elapsed_seconds'] = time.monotonic() - start
    report['partial'] = bool(report['pending_shards'] or report.get('budget_exhausted'))
    atomic_json(output / 'local-import.json', report)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache-dir', type=Path, default=DEFAULT_CACHE_DIR)
    commands = parser.add_subparsers(dest='command', required=True)
    command = commands.add_parser('prepare')
    command.add_argument('--directory', type=Path, required=True)
    command.add_argument('--wheelhouse', type=Path)
    command.add_argument('--download-runtime', action='store_true',
                         help='Explicitly allow setup to fetch missing hash-pinned Linux wheels on the pod')
    command = commands.add_parser('verify')
    command.add_argument('--bundle', type=Path, required=True)
    command = commands.add_parser('import')
    command.add_argument('--bundle', type=Path, required=True)
    command.add_argument('--output', type=Path, required=True)
    command.add_argument('--budget-seconds', type=float, default=600)
    args = parser.parse_args()
    if args.command == 'prepare':
        result = prepare(args.cache_dir, args.directory, args.wheelhouse, download_runtime=args.download_runtime)
        result = {k: v for k, v in result.items() if k not in ('shards', 'model_files', 'runner_files', 'support_files', 'wheel_files')}
    elif args.command == 'verify':
        result = verify_bundle(args.bundle.resolve())
    else:
        result = import_results(args.cache_dir, args.bundle, args.output, budget_seconds=args.budget_seconds)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
