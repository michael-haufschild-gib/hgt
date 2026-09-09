"""Prepare and publish explicit GPU proof-method batches into the local corpus."""
from __future__ import annotations

import argparse
from collections import defaultdict, deque
import json
import os
from pathlib import Path
import shutil
import sqlite3
import time

from lean_research_batch import locks
from lean_research_corpus import Corpus, source_priority
from research_batch.format import atomic_json, checked_file, descriptor, sha_file
from research_batch.methods import (FORMAT, MAX_ROWS, MODEL, PRODUCER, METHOD_PROMPT_VERSION,
                                    checked_output, load_manifest, validated_payload, write_rows)
from research_runtime.config import DEFAULT_CACHE_DIR


def prepare(cache, directory, model_files):
    directory.mkdir(parents=True, exist_ok=True)
    bundle = directory / 'bundle'
    bundle.mkdir(exist_ok=True)
    with locks([directory / 'prepare.lock'], seconds=0):
        if (bundle / 'manifest.json').exists():
            return load_manifest(bundle)
        snapshot = directory / 'snapshot.sqlite3'
        if not snapshot.exists():
            temporary = snapshot.with_suffix('.partial.sqlite3')
            temporary.unlink(missing_ok=True)
            with sqlite3.connect(temporary) as target, Corpus(cache, readonly=True) as corpus:
                target.executescript('CREATE TABLE records(id TEXT PRIMARY KEY,priority INTEGER,path TEXT,line INTEGER,payload TEXT);'
                                     'CREATE TABLE metadata(key TEXT PRIMARY KEY,value TEXT);')
                corpus.con.execute('BEGIN')
                files = [dict(r) for r in corpus.con.execute('SELECT path,module,source_hash,status,imports,toolchain,extractor_version,size,mtime_ns FROM files')]
                for f in files:
                    f['imports'] = json.loads(f['imports'])
                target.execute('INSERT INTO metadata VALUES(?,?)', ('files', json.dumps(files)))
                target.execute('INSERT INTO metadata VALUES(?,?)', ('generation', str(corpus.generation)))
                query = ("SELECT d.id,d.name,d.path,d.line,d.statement,d.proof,d.source_hash FROM declarations d "
                         "JOIN files f ON f.path=d.path LEFT JOIN methods m ON m.decl_id=d.id "
                         "WHERE d.proof<>'' AND f.status='indexed' AND NOT (m.status IS 'ready' "
                         "AND m.content_hash=d.source_hash AND m.prompt_version=?) ORDER BY d.id")
                count = 0
                cursor = corpus.con.execute(query, (METHOD_PROMPT_VERSION,))
                while batch := cursor.fetchmany(2048):
                    target.executemany('INSERT INTO records VALUES(?,?,?,?,?)',
                        [(r['id'], source_priority(r['path']), r['path'], r['line'], json.dumps(dict(r), ensure_ascii=False)) for r in batch])
                    target.commit()
                    count += len(batch)
                    if count % 20480 == 0:
                        print(json.dumps(dict(event='method_snapshot', declarations=count)), flush=True)
                target.execute('CREATE INDEX ordering ON records(priority,path,line,id)')
                target.commit()
            os.replace(temporary, snapshot)
        inputs = bundle / 'inputs'
        inputs.mkdir(exist_ok=True)
        with sqlite3.connect(snapshot) as con:
            files = json.loads(con.execute("SELECT value FROM metadata WHERE key='files'").fetchone()[0])
            atomic_json(bundle / 'source-files.json', files)
            shards, rows, chars, priority = [], [], 0, None
            def flush():
                if not rows:
                    return
                entry = write_rows(inputs / ('%05d.jsonl.gz' % len(shards)), rows)
                shards.append(dict(**entry, priority=priority))
            for p, text in con.execute('SELECT priority,payload FROM records ORDER BY priority,path,line,id'):
                if rows and (p != priority or len(rows) >= MAX_ROWS or chars + len(text) > 2_000_000):
                    flush()
                    rows, chars = [], 0
                priority = p
                rows.append(json.loads(text))
                chars += len(text)
            flush()
            count = con.execute('SELECT COUNT(*) FROM records').fetchone()[0]
            generation = int(con.execute("SELECT value FROM metadata WHERE key='generation'").fetchone()[0])
        scripts = Path(__file__).resolve().parent
        code = []
        for name in ('lean_research_corpus.py', 'lean_search_index.py', 'lean_research_engine.py',
                     'research_batch/__init__.py', 'research_batch/format.py',
                     'research_batch/methods.py', 'research_batch/method_runner.py',
                     'research_batch/method_vectors.py'):
            dest = bundle / name
            dest.parent.mkdir(exist_ok=True)
            shutil.copy2(scripts / name, dest)
            code.append(dict(directory=str(Path(name).parent), file=descriptor(dest)))
        shutil.copy2(scripts / 'research_batch/method-pipeline.sh', bundle / 'method-pipeline.sh')
        code.append(dict(directory='.', file=descriptor(bundle / 'method-pipeline.sh')))
        shutil.copy2(scripts / 'research_batch/method-requirements.txt', bundle / 'method-requirements.txt')
        manifest = dict(format=FORMAT, producer=PRODUCER, model=MODEL, prompt_version=METHOD_PROMPT_VERSION,
                        declarations=count, generation=generation, created=time.time(), shards=shards,
                        source_files=descriptor(bundle / 'source-files.json'), code=code,
                        model_files=json.loads(model_files.read_text()),
                        runtime_packages=descriptor(bundle / 'method-requirements.txt'),
                        priority=['RHTower','HTGeometry','rest'])
        atomic_json(bundle / 'manifest.json', manifest)
        return manifest


def changed_paths(root, corpus, original):
    """Conservative source/import closure; compare disk too for unindexed edits."""
    old = {f['path']: f for f in original}
    current = {r['path']: dict(r) for r in corpus.con.execute('SELECT * FROM files')}
    toolchain_file = root / 'formal/lean-toolchain'
    toolchain = toolchain_file.read_text().strip() if toolchain_file.exists() else 'unknown'
    bad, reverse = set(), defaultdict(set)
    module_paths = defaultdict(set)
    for row in [*old.values(), *current.values()]:
        module_paths[row['module']].add(row['path'])
        imports = row['imports'] if isinstance(row['imports'], list) else json.loads(row['imports'])
        for module in imports:
            reverse[module].add(row['module'])
    for path in old.keys() | current.keys():
        before, after = old.get(path), current.get(path)
        if (not before or not after or after['status'] != 'indexed' or before['toolchain'] != toolchain or
                any(before.get(k) != after.get(k) for k in ('source_hash','toolchain','extractor_version'))):
            bad.add(path)
            continue
        try:
            source = root / path
            stat = source.stat()
            if (stat.st_size, stat.st_mtime_ns) != (after['size'], after['mtime_ns']):
                if sha_file(source) != after['source_hash']:
                    bad.add(path)
        except OSError:
            bad.add(path)
    pending = deque(row['module'] for path in bad for row in (old.get(path), current.get(path)) if row)
    seen = set()
    while pending:
        module = pending.popleft()
        if module in seen:
            continue
        seen.add(module)
        bad.update(module_paths[module])
        pending.extend(reverse[module])
    return bad


def import_results(cache, bundle, output, *, root, budget_seconds=90, lock_seconds=150):
    manifest = load_manifest(bundle)
    manifest_sha = sha_file(bundle / 'manifest.json')
    original = json.loads(checked_file(bundle, manifest['source_files']).read_text())
    report = dict(published=0, failed=0, stale=0, already_ready=0, checked_shards=0,
                  pending_shards=0, partial=True, manifest_sha256=manifest_sha)
    with locks([cache / n for n in ('source.lock','compiler.lock','enrichment.lock')], seconds=lock_seconds), Corpus(cache) as corpus:
        deadline = time.monotonic() + budget_seconds
        bad = changed_paths(root, corpus, original)
        report['changed_source_or_dependency_files'] = len(bad)
        for entry in manifest['shards']:
            key = 'method-batch:' + manifest_sha + ':' + entry['name']
            saved = corpus.con.execute('SELECT value FROM meta WHERE key=?', (key,)).fetchone()
            if saved:
                report['checked_shards'] += 1
                continue
            if time.monotonic() >= deadline or not (output / (entry['name'] + '.done.json')).exists():
                report['pending_shards'] += 1
                continue
            sources, results = checked_output(bundle, output, entry)
            before = {k:report[k] for k in ('published','failed','stale','already_ready')}
            for source, result in zip(sources, results):
                d = corpus.declaration(source['id'])
                if (source['path'] in bad or not d or d['source_hash'] != source['source_hash']
                        or d['statement'] != source['statement'] or d['proof'] != source['proof']):
                    report['stale'] += 1
                    continue
                existing = corpus.method(d['id'])
                if existing and existing['content_hash'] == d['source_hash'] and existing['prompt_version'] == METHOD_PROMPT_VERSION:
                    report['already_ready'] += 1
                    continue
                if result['status'] == 'failed':
                    with corpus.con:
                        corpus.con.execute("INSERT OR REPLACE INTO methods VALUES(?,?,?,?,?,?,?,?,?,'failed',?)",
                            (d['id'], d['source_hash'], PRODUCER, METHOD_PROMPT_VERSION, '', '[]','[]','[]','[]',result['error']))
                    report['failed'] += 1
                    continue
                payload = validated_payload(source, result)
                corpus.save_method(d['id'], payload, model_version=PRODUCER, prompt_version=METHOD_PROMPT_VERSION,
                                   expected_source_hash=d['source_hash'], expected_evidence_epoch=corpus.evidence_epoch,
                                   batch_provenance=dict(manifest_sha256=manifest_sha,input_sha256=entry['sha256'],
                                                         shard=entry['name'],interpretation_verified=False))
                report['published'] += 1
            with corpus.con:
                # Retain provenance and explicitly recognize this producer for
                # local reuse. Recognition is not a quality/applicability claim.
                value = corpus.con.execute("SELECT value FROM meta WHERE key='method_producers'").fetchone()
                producers = json.loads(value[0]) if value else {}
                producers[PRODUCER] = dict(manifest_sha256=manifest_sha, prompt_version=METHOD_PROMPT_VERSION)
                corpus.con.execute("INSERT OR REPLACE INTO meta VALUES('method_producers',?)", (json.dumps(producers),))
                receipt = {k:report[k]-before[k] for k in before}
                corpus.con.execute('INSERT OR REPLACE INTO meta VALUES(?,?)', (key, json.dumps(receipt)))
            report['checked_shards'] += 1
            atomic_json(output / 'local-import.json', report)
            print(json.dumps(dict(event='method_import', **report)), flush=True)
        report['partial'] = report['pending_shards'] > 0
        totals = dict.fromkeys(('published','failed','stale','already_ready'),0)
        for row in corpus.con.execute('SELECT value FROM meta WHERE key LIKE ?', ('method-batch:'+manifest_sha+':%',)):
            value = json.loads(row[0])
            for key in totals:
                totals[key] += value[key]
        report['totals'] = totals
        atomic_json(output / 'local-import.json', report)
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache-dir', type=Path, default=DEFAULT_CACHE_DIR)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('prepare')
    p.add_argument('--directory', type=Path, required=True)
    p.add_argument('--model-files', type=Path, required=True)
    p = sub.add_parser('import')
    p.add_argument('--bundle', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--root', type=Path, required=True)
    p.add_argument('--budget-seconds', type=float, default=90)
    args = parser.parse_args()
    if args.command == 'prepare':
        result = prepare(args.cache_dir, args.directory, args.model_files)
        result = {k:v for k,v in result.items() if k not in ('shards','model_files','code')}
    else:
        result = import_results(args.cache_dir, args.bundle, args.output, root=args.root, budget_seconds=args.budget_seconds)
    print(json.dumps(result))
