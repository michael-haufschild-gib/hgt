"""Versioned local-runtime configuration. No third-party imports or network I/O."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path

RUNTIME_HOME = Path(__file__).resolve().parent
DEFAULT_CACHE_DIR = RUNTIME_HOME.parents[1] / 'formal' / '.lake' / 'hgt-research' / 'discovery-1'
PYTHON = RUNTIME_HOME / '.venv' / 'bin' / 'python'
MODELS = json.loads((RUNTIME_HOME / 'models.json').read_text())
EMBEDDING_DIMENSIONS = MODELS['embedding']['dimensions']
PROTOCOL_VERSION = 2
ADAPTER_VERSION = 4
MAX_FRAME = 2 * 1024 * 1024
MAX_ITEMS = 64
# Indexing requests are small so an agent's query waits well under a second
# behind one. Queries are served first but never cancel work in flight.
ENRICHMENT_ITEMS = 2
MAX_TEXT = 32768
MAX_TOTAL_TEXT = 262144
MAX_PENDING = 32
MAX_SECONDS = 600.0
MAX_TOKENS = 2048
CONTEXT_TOKENS = 2048
BATCH_SIZE = 4
# Padded tokens per embedding forward pass, and the batch ceiling. Short
# statements dominate the corpus, so a fixed small batch left the GPU idle.
TOKEN_BUDGET = 8192
MAX_BATCH_SIZE = 64
PAD_MULTIPLE = 32
RERANK_PAD_MULTIPLE = 64
GENERATION_CONTEXT = 8192
# EmbeddingGemma's task prefixes are a fixed set from its model card, not a
# free-text instruction: queries and documents use DIFFERENT prefixes, and the
# prefix tokens are inside the mean (1_Pooling sets include_prompt: true).
QUERY_TEMPLATE = 'task: search result | query: {text}'
DOCUMENT_TEMPLATE = 'title: none | text: {text}'
EMBEDDING_POOLING = MODELS['embedding'].get('pooling', 'mean')
# mlx-lm must ship a matching architecture for the Metal fast path. 0.32.2 has
# no embedding_gemma2, so the pinned model omits this and search runs on Torch
# MPS. Setting it back on enables the fast path without other changes.
MLX_EMBEDDING_MODULE = MODELS['embedding'].get('mlx_module')


def fingerprints() -> dict:
    """Change with model revisions, prompts, token limits, or dependency lock."""
    roles = {role: hashlib.sha256(json.dumps(spec, sort_keys=True).encode()).hexdigest()
             for role, spec in MODELS.items()}
    payload = {'models': MODELS, 'adapter': ADAPTER_VERSION,
               'query_template': QUERY_TEMPLATE, 'document_template': DOCUMENT_TEMPLATE,
               'pooling': EMBEDDING_POOLING, 'dimensions': EMBEDDING_DIMENSIONS,
               'context': CONTEXT_TOKENS, 'generation_context': GENERATION_CONTEXT,
               'lock': hashlib.sha256((RUNTIME_HOME / 'uv.lock').read_bytes()).hexdigest()}
    return {'models': roles, 'runtime': hashlib.sha256(
        json.dumps(payload, sort_keys=True).encode()).hexdigest()}


def installation_status(cache_dir: Path) -> dict:
    """Cheap manifest/size check; setup --verify performs the full hash audit."""
    cache_dir = cache_dir / 'runtime'
    result = {'ready': False, 'available': False, 'python': str(PYTHON), 'models': {},
              'fingerprints': fingerprints(), 'offline': True}
    try:
        manifest = json.loads((cache_dir / 'installed.json').read_text())
    except (OSError, ValueError):
        manifest = {}
    if not isinstance(manifest, dict) or not isinstance(manifest.get('models', {}), dict):
        manifest = {}
    for role, spec in MODELS.items():
        entry = manifest.get('models', {}).get(role, {})
        if not isinstance(entry, dict):
            entry = {}
        folder = cache_dir / 'models' / role / spec['revision']
        files = entry.get('files', {})
        if not isinstance(files, dict):
            files = {}
        ready = (entry.get('revision') == spec['revision'] and bool(files)
                 and 'config.json' in files and 'tokenizer.json' in files
                 and any(n.endswith('.safetensors') for n in files))
        if ready:
            try:
                ready = all(Path(name).name == name and (folder / name).is_file()
                            and (folder / name).stat().st_size == info['size']
                            for name, info in files.items())
            except (OSError, KeyError, TypeError):
                ready = False
        result['models'][role] = {**spec, 'installed': ready, 'path': str(folder),
                                  'device': None, 'loaded': False}
    result['ready'] = (PYTHON.is_file() and manifest.get('fingerprint') ==
                       result['fingerprints']['runtime'] and
                       all(m['installed'] for m in result['models'].values()))
    result['available'] = result['ready']
    result['reason'] = None if result['ready'] else 'pinned local environment or snapshots missing/stale; run explicit setup'
    for role in MODELS:
        result[f'{role}_model_version'] = (f"{MODELS[role]['repo']}@{MODELS[role]['revision']}"
                                          f":{result['fingerprints']['runtime']}")
    return result


def offline_environment() -> dict[str, str]:
    """Force offline before importing HF; do not inherit permissive fallback."""
    return {**os.environ, 'HF_HUB_OFFLINE': '1', 'TRANSFORMERS_OFFLINE': '1',
            'HF_DATASETS_OFFLINE': '1', 'HF_HUB_DISABLE_TELEMETRY': '1',
            'DO_NOT_TRACK': '1', 'TOKENIZERS_PARALLELISM': 'false',
            'PYTORCH_ENABLE_MPS_FALLBACK': '0', 'OMP_NUM_THREADS': '2',
            'MKL_NUM_THREADS': '2'}
