"""Build an audited embedding job from completed GPU method descriptions."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import shutil
import sqlite3
import subprocess

from lean_research_corpus import chunks
from research_batch.format import atomic_json, descriptor, sha_file, sha_text, SHARD_ROWS
from research_batch.methods import checked_output, load_manifest, validated_payload, write_rows


def prepare(method_bundle, method_results, template, destination):
    manifest = load_manifest(method_bundle)
    source_sha = sha_file(method_bundle / 'manifest.json')
    if (destination / 'manifest.json').exists():
        result = json.loads((destination / 'manifest.json').read_text())
        if result.get('method_manifest_sha256') != source_sha:
            raise ValueError('method vector bundle belongs to another source snapshot')
        return result
    completed = json.loads((method_results / 'run.json').read_text())
    if not completed['complete'] or completed['manifest_sha256'] != source_sha:
        raise ValueError('method generation is not complete')
    destination.mkdir(parents=True, exist_ok=True)
    database = destination / 'texts.sqlite3'
    database.unlink(missing_ok=True)
    with sqlite3.connect(database) as con:
        con.execute('CREATE TABLE texts(hash TEXT PRIMARY KEY,text TEXT,priority INTEGER)')
        for entry in manifest['shards']:
            sources, results = checked_output(method_bundle, method_results, entry)
            for source, result in zip(sources, results):
                if result['status'] != 'ready':
                    continue
                payload = validated_payload(source, result)
                # Exactly the representation used by Corpus.save_method.
                text = '\n'.join(str(payload[k]) for k in ('description','assumptions','steps','obligations'))
                con.executemany('INSERT INTO texts VALUES(?,?,?) ON CONFLICT(hash) DO UPDATE SET priority=MIN(priority,excluded.priority)',
                    [(sha_text(part),part,entry['priority']) for part,_,_ in chunks(text)])
            con.commit()
        (destination / 'inputs').mkdir(exist_ok=True)
        shards, rows, priority = [], [], None
        def flush():
            if rows:
                entry = write_rows(destination / 'inputs' / ('%05d.jsonl.gz' % len(shards)), rows)
                shards.append(dict(**entry, priority=priority))
        for h,text,p in con.execute('SELECT hash,text,priority FROM texts ORDER BY priority,hash'):
            if rows and (len(rows) == SHARD_ROWS or p != priority):
                flush()
                rows = []
            priority = p
            rows.append(dict(hash=h,text=text,view='method'))
        flush()
        count = con.execute('SELECT COUNT(*) FROM texts').fetchone()[0]
    base = json.loads((template / 'manifest.json').read_text())
    (destination / 'research_batch').mkdir(exist_ok=True)
    for entry in base['runner_files']:
        shutil.copy2(template / 'research_batch' / entry['name'], destination / 'research_batch' / entry['name'])
    # Existing pinned embedding weights remain on the same pod.
    if not (destination / 'model').exists():
        (destination / 'model').symlink_to(template / 'model', target_is_directory=True)
    shutil.copy2(template / base['reference']['name'], destination / base['reference']['name'])
    outcomes = json.loads((method_bundle / manifest['source_files']['name']).read_text())
    inventory = write_rows(destination / 'file-outcomes.jsonl.gz', outcomes)
    result = {key:base[key] for key in ('format','spec','target_model','model_files','runner_files','reference')}
    result.update(shards=shards, method_manifest_sha256=source_sha, unique_vectors=count,
                  unique_pending=count, method_description_vectors=True, file_inventory=inventory,
                  support_files=[], wheel_files=[], source_generation=manifest['generation'],
                  runtime_python='3.12', runtime_reuse='existing audited embedding environment')
    atomic_json(destination / 'manifest.json', result)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--method-bundle', type=Path, required=True)
    parser.add_argument('--method-results', type=Path, required=True)
    parser.add_argument('--embedding-template', type=Path, required=True)
    parser.add_argument('--destination', type=Path, required=True)
    args = parser.parse_args()
    result = prepare(args.method_bundle, args.method_results, args.embedding_template, args.destination)
    print(json.dumps(dict(unique_vectors=result['unique_vectors'], shards=len(result['shards']))), flush=True)
    raise SystemExit(subprocess.call([str(args.embedding_template / '.venv/bin/python'), '-u', '-m',
        'research_batch.runner', '--bundle', str(args.destination), '--output', str(args.destination / 'results')],
        cwd=args.destination))
