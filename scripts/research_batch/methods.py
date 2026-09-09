"""Proof-method batch interchange. No model imports, downloads, or Lean execution."""
from __future__ import annotations

import gzip
import json
from pathlib import Path

from lean_research_corpus import CHUNK_OVERLAP, chunks, mask_comments_strings
from lean_research_engine import METHOD_PROMPT_VERSION, json_object, method_payload, method_prompt
from research_batch.format import atomic_bytes, checked_file, descriptor, sha_file, sha_text

FORMAT = 'proof-methods-1'
MODEL = {'repo': 'Qwen/Qwen3-4B-Instruct-2507',
         'revision': 'cdbee75f17c01a7cc42f958dc650907174af0554', 'license': 'Apache-2.0'}
VLLM_VERSION = '0.29.0'
PRODUCER = f"{MODEL['repo']}@{MODEL['revision']}:vllm-{VLLM_VERSION}:bf16"
MAX_ROWS = 256


def proof_parts(proof):
    # Mask once across the entire argument: a chunk can start inside a comment.
    code = mask_comments_strings(proof, mask_strings=False)
    cursor = 0
    for text, _, _ in chunks(proof):
        start = proof.find(text, cursor)
        safe = code[start:start + len(text)]
        if safe.strip():
            yield text, safe
        cursor = max(start + 1, start + len(text) - CHUNK_OVERLAP)


def proof_chunks(proof):
    return [text for text, _ in proof_parts(proof)]


def write_rows(path, rows):
    data = ''.join(json.dumps(row, ensure_ascii=False, sort_keys=True) + '\n' for row in rows)
    atomic_bytes(path, gzip.compress(data.encode(), compresslevel=3, mtime=0))
    return descriptor(path, count=len(rows))


def read_rows(directory, entry):
    with gzip.open(checked_file(directory, entry), 'rt', encoding='utf-8') as stream:
        rows = [json.loads(line) for line in stream]
    if len(rows) != entry['count'] or not 0 < len(rows) <= MAX_ROWS:
        raise ValueError('method shard count mismatch')
    if len({row['id'] for row in rows}) != len(rows):
        raise ValueError('duplicate declaration in method shard')
    return rows


def load_manifest(bundle):
    manifest = json.loads((Path(bundle) / 'manifest.json').read_text())
    if (manifest['format'] != FORMAT or manifest['model'] != MODEL
            or manifest['prompt_version'] != METHOD_PROMPT_VERSION or manifest['producer'] != PRODUCER):
        raise ValueError('unsupported method batch specification')
    if len({row['name'] for row in manifest['shards']}) != len(manifest['shards']):
        raise ValueError('duplicate method shard')
    return manifest


def combine(summaries):
    if not summaries:
        raise ValueError('proof has no code chunks')
    return dict(description='\n'.join(s['description'] for s in summaries),
                **{key: list(dict.fromkeys(x for summary in summaries for x in summary[key]))
                   for key in ('assumptions', 'steps', 'obligations', 'evidence')})


def validated_payload(source, result):
    if (result['id'] != source['id'] or result['source_hash'] != source['source_hash']
            or result.get('status') != 'ready'):
        raise ValueError('method output identity/status mismatch')
    parts = list(proof_parts(source['proof']))
    if len(result['chunks']) != len(parts):
        raise ValueError('method output omits proof chunks')
    summaries = []
    for (part, code), answer in zip(parts, result['chunks']):
        if answer['chunk_hash'] != sha_text(part):
            raise ValueError('method proof chunk/order mismatch')
        if answer.get('finish_reason') != 'stop':
            raise ValueError('method generation did not finish')
        ids = json_object(answer['response']).get('evidence_lines')
        lines = code.splitlines()
        if not isinstance(ids, list) or any(type(i) is not int or not 1 <= i <= len(lines) or not lines[i-1].strip() for i in ids):
            raise ValueError('evidence cites comment-only text across a chunk boundary')
        summaries.append(method_payload(answer['response'], part))
    return combine(summaries)


def checked_output(bundle, output, entry):
    marker = Path(output) / (entry['name'] + '.done.json')
    value = json.loads(marker.read_text())
    if (value['manifest_sha256'] != sha_file(Path(bundle) / 'manifest.json')
            or value['input_sha256'] != entry['sha256'] or value['producer'] != PRODUCER):
        raise ValueError('method completion belongs to different input or producer')
    sources = read_rows(Path(bundle) / 'inputs', entry)
    results = read_rows(output, value['results'])
    if len(results) != len(sources) or [r['id'] for r in results] != [r['id'] for r in sources]:
        raise ValueError('method results omit or reorder declarations')
    for source, result in zip(sources, results):
        if result['source_hash'] != source['source_hash']:
            raise ValueError('method source hash mismatch')
        if result['status'] == 'ready':
            validated_payload(source, result)
        elif result['status'] != 'failed' or not result.get('error'):
            raise ValueError('missing method failure outcome')
    return sources, results
