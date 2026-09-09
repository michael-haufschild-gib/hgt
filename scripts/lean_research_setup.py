#!/usr/bin/env python3
"""Explicit setup for local inference. Only this module may download weights.

Callable integration: setup(cache_dir: Path) -> dict; main(argv=None) -> int.
Default cache is formal/.lake/hgt-research/discovery-1. See research_runtime/README.md.
"""
from __future__ import annotations

import argparse
import fcntl
import fnmatch
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

try:
    from .research_runtime.config import DEFAULT_CACHE_DIR, MODELS, PYTHON, RUNTIME_HOME, fingerprints
except ImportError:
    from research_runtime.config import DEFAULT_CACHE_DIR, MODELS, PYTHON, RUNTIME_HOME, fingerprints


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def _owned_run(command: list[str]) -> None:
    """Wait in foreground; on interruption terminate/reap only this child group."""
    import signal
    child = subprocess.Popen(command, start_new_session=True)
    try:
        if child.wait():
            raise RuntimeError(f'setup command failed: {command[0]}')
    except BaseException:
        if child.poll() is None:
            os.killpg(child.pid, signal.SIGTERM)
            try:
                child.wait(timeout=2)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()
        raise


def install_environment() -> None:
    _owned_run(['uv', 'sync', '--project', str(RUNTIME_HOME), '--python', '3.12', '--locked'])


def download_models(cache_dir: Path) -> dict:
    """Run only in dedicated Python, never called by RuntimeClient or worker."""
    from huggingface_hub import HfApi, snapshot_download
    from huggingface_hub.utils import disable_progress_bars

    disable_progress_bars()

    cache_dir = Path(cache_dir).resolve() / 'runtime'
    cache_dir.mkdir(parents=True, exist_ok=True, mode=0o700)
    with (cache_dir / 'setup.lock').open('a') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise RuntimeError('setup already running for this cache') from None
        manifest = {'fingerprint': fingerprints()['runtime'], 'models': {}}
        for role, spec in MODELS.items():
            folder = cache_dir / 'models' / role / spec['revision']
            print(f"Downloading/verifying {spec['repo']}@{spec['revision']}", flush=True)
            upstream = HfApi().model_info(spec['repo'], revision=spec['revision'], files_metadata=True)
            if upstream.sha != spec['revision']:
                raise RuntimeError(f'upstream revision mismatch: {role}')
            # These adapters use root-level AutoModel/tokenizer artifacts, not
            # SentenceTransformers' unused pooling/score submodules.
            patterns = ('*.json', '*.safetensors', '*.txt', '*.jinja', 'README.md', 'LICENSE*')
            filenames = [f.rfilename for f in upstream.siblings if '/' not in f.rfilename
                         and any(fnmatch.fnmatchcase(f.rfilename, p) for p in patterns)]
            snapshot_download(repo_id=spec['repo'], revision=spec['revision'], local_dir=str(folder),
                              allow_patterns=filenames, max_workers=2)
            files = {p.name: {'size': p.stat().st_size, 'sha256': _sha256(p)}
                     for p in sorted(folder.iterdir()) if p.is_file()}
            expected = {f.rfilename: f for f in upstream.siblings}
            for name, info in files.items():
                remote = expected[name]
                if info['size'] != remote.size:
                    raise RuntimeError(f'upstream size mismatch: {role}/{name}')
                if remote.lfs:
                    correct = info['sha256'] == remote.lfs.sha256
                else:
                    data = (folder / name).read_bytes()
                    git_blob = b'blob ' + str(len(data)).encode() + b'\0' + data
                    correct = hashlib.sha1(git_blob).hexdigest() == remote.blob_id
                if not correct:
                    raise RuntimeError(f'upstream content hash mismatch: {role}/{name}')
            if not {'config.json', 'tokenizer.json'} <= files.keys() or not any(
                    name.endswith('.safetensors') for name in files):
                raise RuntimeError(f'incomplete local snapshot: {role}')
            manifest['models'][role] = {**spec, 'files': files}
        temporary = cache_dir / 'installed.json.tmp'
        temporary.write_text(json.dumps(manifest, indent=2) + '\n')
        temporary.replace(cache_dir / 'installed.json')
        return manifest


def verify(cache_dir: Path) -> dict:
    """Full offline snapshot hash audit. No imports of model libraries."""
    cache_dir = cache_dir / 'runtime'
    manifest = json.loads((cache_dir / 'installed.json').read_text())
    if manifest['fingerprint'] != fingerprints()['runtime']:
        raise RuntimeError('runtime pins changed; rerun explicit setup')
    for role, spec in MODELS.items():
        entry = manifest['models'][role]
        if entry['revision'] != spec['revision']:
            raise RuntimeError(f'revision mismatch: {role}')
        folder = cache_dir / 'models' / role / spec['revision']
        for name, info in entry['files'].items():
            if Path(name).name != name or _sha256(folder / name) != info['sha256']:
                raise RuntimeError(f'snapshot hash mismatch: {role}/{name}')
    return {'verified': True, 'fingerprints': fingerprints()}


def setup(cache_dir: Path = DEFAULT_CACHE_DIR) -> dict:
    """Explicit opt-in: install locked Python 3.12 dependencies and pinned weights."""
    cache_dir = Path(cache_dir).resolve()
    install_environment()
    _owned_run([str(PYTHON), str(Path(__file__).resolve()), '--cache-dir', str(cache_dir), '--download-only'])
    return verify(cache_dir)


def smoke(cache_dir: Path, seconds: float = 180) -> dict:
    import math
    import time
    try:
        from .lean_research_runtime import RuntimeClient
    except ImportError:
        from lean_research_runtime import RuntimeClient
    client = RuntimeClient(cache_dir)
    deadline = time.monotonic() + seconds
    vectors = client.embed(['A natural number equals itself.', 'The moon is made of cheese.'], deadline=deadline)
    query = client.embed(['natural number reflexivity'], query=True, deadline=deadline)
    if len(vectors) != 2 or any(len(v) != 1024 for v in vectors + query):
        raise RuntimeError('embedding dimension/order smoke failed')
    if any(not all(map(math.isfinite, v)) or abs(sum(x*x for x in v) - 1) > 0.01 for v in vectors + query):
        raise RuntimeError('embedding normalization smoke failed')
    scores = client.rerank('What is the capital of China?',
                           ['The capital of China is Beijing.', 'Bananas are yellow.'], deadline=deadline)
    if len(scores) != 2 or not all(0 <= x <= 1 for x in scores) or scores[0] <= scores[1]:
        raise RuntimeError(f'yes/no relevance smoke failed: {scores}')
    search_status = client.status()
    generated = client.generate('Reply with the single word local.', max_tokens=16, deadline=deadline)
    if not generated.strip():
        raise RuntimeError('generation smoke returned empty text')
    return {'embedding_dimensions': len(query[0]), 'scores': scores, 'generated': generated,
            'search_status': search_status, 'status': client.status()}


def embedding_smoke(cache_dir: Path, seconds: float = 120) -> dict:
    """32 representative-length documents through the actual shared client."""
    import math
    import time
    try:
        from .lean_research_runtime import RuntimeClient
    except ImportError:
        from lean_research_runtime import RuntimeClient
    base = ('theorem bounded_spectral_coercivity (f : ℝ → ℝ) (h : ∀ x, 0 ≤ f x) : '
            '0 ≤ f 0 := by\n  exact h 0\n/- A lower bound on a quadratic form controls '
            'the norm on the orthogonal complement of its nullspace. -/\n')
    documents = [(base * 30)[:5000-(i % 4)*137] for i in range(32)]
    with RuntimeClient(cache_dir) as client:
        start = time.monotonic()
        embeddings = client.embed(documents, deadline=start+seconds)
        elapsed = time.monotonic()-start
        if len(embeddings) != 32 or any(len(v) != 1024 or not all(map(math.isfinite, v))
                or abs(sum(x*x for x in v)-1) > 0.01 for v in embeddings):
            raise RuntimeError('embedding throughput smoke failed output checks')
        return {'documents': 32, 'characters': sum(map(len, documents)),
                'elapsed_seconds_including_load': elapsed,
                'documents_per_second': 32/elapsed, 'status': client.status()}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache-dir', type=Path, default=DEFAULT_CACHE_DIR)
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--env-only', action='store_true')
    group.add_argument('--download-only', action='store_true', help=argparse.SUPPRESS)
    group.add_argument('--verify', action='store_true')
    group.add_argument('--smoke', action='store_true', help='offline actual-model smoke; does not install')
    group.add_argument('--embedding-smoke', action='store_true', help='offline 32-document throughput probe')
    group.add_argument('--status', action='store_true')
    args = parser.parse_args(argv)
    if args.env_only:
        install_environment()
        result = {'python': str(PYTHON)}
    elif args.download_only:
        result = download_models(args.cache_dir)
        result = {'installed': True, 'fingerprint': result['fingerprint']}
    elif args.verify:
        result = verify(args.cache_dir)
    elif args.smoke:
        result = smoke(args.cache_dir)
    elif args.embedding_smoke:
        result = embedding_smoke(args.cache_dir)
    elif args.status:
        try:
            from .lean_research_runtime import RuntimeClient
        except ImportError:
            from lean_research_runtime import RuntimeClient
        result = RuntimeClient(args.cache_dir).status()
    else:
        result = setup(args.cache_dir)
    print(json.dumps(result, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
