"""Versioned, checksum-verified batch interchange; no ML imports or downloads."""
from __future__ import annotations

import gzip
import hashlib
import json
import os
from pathlib import Path
import uuid

FORMAT = 1
DIMENSIONS = 1024
SHARD_ROWS = 4096
COSINE_MIN = 0.999
RANK_OVERLAP_MIN = 0.95


def sha_file(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(4 * 1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def sha_text(text):
    return hashlib.sha256(text.encode('utf-8')).hexdigest()


def atomic_json(path, value):
    atomic_bytes(path, (json.dumps(value, ensure_ascii=False, sort_keys=True) + '\n').encode())


def atomic_bytes(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + '.' + uuid.uuid4().hex + '.tmp')
    try:
        with temporary.open('wb') as stream:
            stream.write(value)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def checked_file(directory, entry):
    name = entry['name']
    if not isinstance(name, str) or Path(name).name != name or name in ('.', '..'):
        raise ValueError('invalid artifact filename')
    path = Path(directory) / name
    if path.is_symlink() or not path.is_file() or path.stat().st_size != entry['size']:
        raise ValueError(f'missing or incomplete artifact: {name}')
    if sha_file(path) != entry['sha256']:
        raise ValueError(f'checksum mismatch: {name}')
    return path


def descriptor(path, **extra):
    path = Path(path)
    return dict(name=path.name, size=path.stat().st_size, sha256=sha_file(path), **extra)


def load_manifest(bundle):
    manifest = json.loads((Path(bundle) / 'manifest.json').read_text())
    if manifest['format'] != FORMAT or manifest['spec']['dimensions'] != DIMENSIONS:
        raise ValueError('unsupported embedding bundle')
    names = [s['name'] for s in manifest['shards']]
    if len(names) != len(set(names)):
        raise ValueError('duplicate input shard')
    return manifest


def read_shard(bundle, entry):
    path = checked_file(Path(bundle) / 'inputs', entry)
    with gzip.open(path, 'rt', encoding='utf-8') as stream:
        rows = [json.loads(line) for line in stream]
    if len(rows) != entry['count'] or not 0 < len(rows) <= SHARD_ROWS:
        raise ValueError('invalid input shard count')
    seen = set()
    for row in rows:
        if not isinstance(row['text'], str) or sha_text(row['text']) != row['hash'] or row['hash'] in seen:
            raise ValueError('invalid or duplicate source hash')
        seen.add(row['hash'])
    return rows


def validate_matrix(value, rows):
    import numpy as np
    matrix = np.asarray(value)
    if matrix.dtype != np.float32 or matrix.shape != (rows, DIMENSIONS):
        raise ValueError('embedding dtype, dimensions or row count mismatch')
    if not np.isfinite(matrix).all() or not np.allclose(np.linalg.norm(matrix, axis=1), 1, atol=1e-4):
        raise ValueError('non-finite or non-unit embedding')
    return matrix


def parity(reference, actual, query_count):
    """Numerical compatibility only; this is not a retrieval-quality benchmark."""
    import numpy as np
    reference = validate_matrix(np.asarray(reference, dtype=np.float32), len(reference))
    actual = validate_matrix(np.asarray(actual, dtype=np.float32), len(reference))
    if query_count < 1 or query_count >= len(reference):
        raise ValueError('reference needs both documents and queries')
    cosines = np.sum(reference * actual, axis=1)
    docs = len(reference) - query_count
    k = min(20, docs)
    # Local query vectors remain in use after import. Audit that mixed backend
    # retrieval too, not just CUDA queries against CUDA documents.
    expected = reference[docs:] @ reference[:docs].T
    mixed = reference[docs:] @ actual[:docs].T
    cuda = actual[docs:] @ actual[:docs].T
    def overlap(scores):
        return float(np.mean([len(set(np.argsort(a)[-k:]) & set(np.argsort(b)[-k:])) / k
                              for a, b in zip(expected, scores)]))
    mixed_overlap, cuda_overlap = overlap(mixed), overlap(cuda)
    minimum = float(cosines.min())
    return dict(passed=minimum >= COSINE_MIN and min(mixed_overlap, cuda_overlap) >= RANK_OVERLAP_MIN,
                minimum_cosine=minimum, mixed_top20_overlap=mixed_overlap,
                cuda_top20_overlap=cuda_overlap, rows=len(reference), query_count=query_count,
                thresholds=dict(minimum_cosine=COSINE_MIN, mean_top20_overlap=RANK_OVERLAP_MIN))


def checked_result(bundle, output, entry, manifest_sha, audit_sha):
    """A completion marker binds vectors to the input order and successful audit."""
    import numpy as np
    marker = Path(output) / (entry['name'] + '.done.json')
    report = json.loads(marker.read_text())
    if (report['manifest_sha256'] != manifest_sha or report['input_sha256'] != entry['sha256']
            or report['audit_sha256'] != audit_sha or report['count'] != entry['count']):
        raise ValueError('result provenance mismatch')
    path = checked_file(output, report['vectors'])
    matrix = np.load(path, allow_pickle=False, mmap_mode='r')
    return report, validate_matrix(matrix, entry['count'])
