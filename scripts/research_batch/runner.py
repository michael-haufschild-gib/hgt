"""One CUDA process; length-bucketed inference, bounded atomic output, safe resume.

Run from the transferred bundle: python -m research_batch.runner --bundle .
CPU is available only via --cpu-audit, which cannot produce importable results.
"""
from __future__ import annotations

import argparse
import fcntl
import importlib.metadata
import io
import json
import os
from pathlib import Path
import platform
import signal
import time

from .format import (atomic_bytes, atomic_json, checked_file, checked_result, descriptor,
                     load_manifest, parity, read_shard, sha_file, validate_matrix)

for key in ('HF_HUB_OFFLINE', 'TRANSFORMERS_OFFLINE', 'HF_HUB_DISABLE_TELEMETRY'):
    os.environ[key] = '1'
os.environ['TOKENIZERS_PARALLELISM'] = 'true'
os.environ.setdefault('RAYON_NUM_THREADS', str(min(8, os.cpu_count() or 1)))


def validate_cuda(torch):
    if not torch.cuda.is_available():
        raise RuntimeError('CUDA required; refusing CPU fallback')
    if torch.cuda.device_count() != 1:
        raise RuntimeError('Expose exactly one GPU with CUDA_VISIBLE_DEVICES')
    capability = torch.cuda.get_device_capability(0)
    if capability not in ((10, 0), (10, 3)):
        raise RuntimeError('This prepared job requires B200 or B300')
    if torch.version.cuda not in ('12.8', '12.9'):
        raise RuntimeError('Expected the prepared CUDA 12.8/12.9 image')
    if capability == (10, 3) and torch.version.cuda != '12.9':
        raise RuntimeError('Use the prepared CUDA 12.9 image for B300')


class Encoder:
    def __init__(self, bundle, spec, *, dtype='bfloat16', cpu_audit=False,
                 token_budget=65536, max_batch=256):
        import torch
        from transformers import AutoModel, AutoTokenizer
        self.torch = torch
        for name, version in (('torch', '2.8.0'), ('transformers', '4.56.2'),
                              ('tokenizers', '0.22.2'), ('numpy', '2.3.3'), ('safetensors', '0.8.0')):
            if importlib.metadata.version(name).split('+')[0] != version:
                raise RuntimeError(f'Expected pinned {name}=={version}; run setup.sh')
        self.device = 'cpu' if cpu_audit else 'cuda'
        if cpu_audit:
            dtype = 'float32'
            torch.set_num_threads(2)
        else:
            validate_cuda(torch)
        torch.backends.cuda.matmul.allow_tf32 = False
        self.dtype = dtype
        self.spec = spec
        self.token_budget, self.max_batch = token_budget, max_batch
        self.tokenizer = AutoTokenizer.from_pretrained(str(Path(bundle) / 'model'),
            local_files_only=True, trust_remote_code=False, padding_side='right')
        self.model = AutoModel.from_pretrained(str(Path(bundle) / 'model'),
            local_files_only=True, trust_remote_code=False,
            dtype=getattr(torch, dtype), attn_implementation='sdpa').eval().to(self.device)

    def encode(self, texts, *, query=False):
        import numpy as np
        torch = self.torch
        if query:
            texts = [self.spec['query_template'].format(text=text) for text in texts]
        tokens = self.tokenizer(texts, padding=False, truncation=True,
                                max_length=self.spec['context_tokens'])['input_ids']
        if any(not ids for ids in tokens):
            raise ValueError('empty token sequence')
        order = sorted(range(len(tokens)), key=lambda i: len(tokens[i]))
        result = np.empty((len(tokens), self.spec['dimensions']), dtype=np.float32)
        cursor = 0
        with torch.inference_mode():
            while cursor < len(order):
                count = 1
                while count < self.max_batch and cursor + count < len(order):
                    padded = ((len(tokens[order[cursor + count]]) + 31) // 32) * 32
                    if (count + 1) * padded > self.token_budget:
                        break
                    count += 1
                indices = order[cursor:cursor + count]
                batch = hidden = pooled = None
                try:
                    batch = self.tokenizer.pad({'input_ids': [tokens[i] for i in indices]},
                        padding=True, pad_to_multiple_of=32, return_attention_mask=True,
                        return_tensors='pt').to(self.device)
                    hidden = self.model(**batch, use_cache=False).last_hidden_state
                    pooled = hidden[torch.arange(count, device=self.device),
                                    batch['attention_mask'].sum(dim=1) - 1]
                    result[indices] = torch.nn.functional.normalize(pooled.float(), dim=1).cpu().numpy()
                except torch.cuda.OutOfMemoryError:
                    if count == 1:
                        raise
                    del batch, hidden, pooled
                    torch.cuda.empty_cache()
                    self.max_batch = max(1, count // 2)
                    print(json.dumps(dict(event='oom_retry', max_batch=self.max_batch)), flush=True)
                    continue
                del batch, hidden, pooled
                cursor += count
        return validate_matrix(result, len(texts)), sum(map(len, tokens))

    def environment(self):
        torch = self.torch
        return dict(device=self.device, dtype=self.dtype, attention='sdpa',
                    gpu=None if self.device == 'cpu' else torch.cuda.get_device_name(0),
                    capability=None if self.device == 'cpu' else list(torch.cuda.get_device_capability(0)),
                    cuda=torch.version.cuda, python=platform.python_version(),
                    packages={n: importlib.metadata.version(n) for n in
                              ('torch', 'transformers', 'tokenizers', 'numpy', 'safetensors')},
                    token_budget=self.token_budget, max_batch=self.max_batch)


def audit(encoder, bundle, manifest, output, *, publish=True):
    import numpy as np
    reference_path = checked_file(bundle, manifest['reference'])
    reference = json.loads(reference_path.read_text())
    docs, _ = encoder.encode(reference['documents'])
    queries, _ = encoder.encode(reference['queries'], query=True)
    actual = np.concatenate([docs, queries])
    report = parity(reference['vectors'], actual, len(reference['queries']))
    report.update(manifest_sha256=sha_file(Path(bundle) / 'manifest.json'),
                  reference_sha256=manifest['reference']['sha256'],
                  environment=encoder.environment(), target_model=manifest['target_model'])
    print(json.dumps(dict(event='compatibility', **report)), flush=True)
    if not report['passed']:
        raise RuntimeError('Compatibility gate failed; use a fresh output directory with --dtype float32')
    if publish:
        stream = io.BytesIO()
        np.save(stream, actual, allow_pickle=False)
        atomic_bytes(output / 'audit-vectors.npy', stream.getvalue())
        report['vectors'] = descriptor(output / 'audit-vectors.npy')
        atomic_json(output / 'audit.json', report)
    return report


def run(args):
    import numpy as np
    bundle, output = args.bundle.resolve(), args.output.resolve()
    manifest = load_manifest(bundle)
    manifest_sha = sha_file(bundle / 'manifest.json')
    for item in manifest['model_files']:
        checked_file(bundle / 'model', item)
    for item in manifest['runner_files']:
        checked_file(bundle / 'research_batch', item)
    output.mkdir(parents=True, exist_ok=True)
    with (output / 'runner.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        if (output / 'audit.json').exists():
            previous = json.loads((output / 'audit.json').read_text())
            if previous['manifest_sha256'] != manifest_sha or previous['environment']['dtype'] != args.dtype:
                raise ValueError('Output directory belongs to a different run or dtype')
        encoder = Encoder(bundle, manifest['spec'], dtype=args.dtype, cpu_audit=args.cpu_audit,
                          token_budget=args.token_budget, max_batch=args.max_batch)
        print(json.dumps(dict(event='loaded', **encoder.environment())), flush=True)
        if args.cpu_audit:
            audit(encoder, bundle, manifest, output, publish=False)
            return
        # Preserve the original audit marker across resumes: output shards bind
        # to that exact marker, including its original batch configuration.
        if not (output / 'audit.json').exists():
            audit(encoder, bundle, manifest, output)
        else:
            previous = json.loads((output / 'audit.json').read_text())
            for key in ('device', 'dtype', 'attention', 'gpu', 'capability', 'cuda', 'packages'):
                if previous['environment'][key] != encoder.environment()[key]:
                    raise ValueError(f'Resume environment changed: {key}')
            ref = json.loads(checked_file(bundle, manifest['reference']).read_text())
            values = np.load(checked_file(output, previous['vectors']), allow_pickle=False)
            if not parity(ref['vectors'], values, len(ref['queries']))['passed']:
                raise ValueError('Stored compatibility audit failed')
        audit_sha = sha_file(output / 'audit.json')
        started = time.monotonic()
        new_count, new_tokens, resumed, completed = 0, 0, 0, 0
        for entry in manifest['shards']:
            if (output / (entry['name'] + '.done.json')).exists():
                checked_result(bundle, output, entry, manifest_sha, audit_sha)
                resumed += entry['count']
                completed += 1
                continue
            if args.max_shards and completed >= args.max_shards:
                break
            start = time.monotonic()
            rows = read_shard(bundle, entry)
            values, token_count = encoder.encode([row['text'] for row in rows])
            target = output / (entry['name'] + '.npy')
            stream = io.BytesIO()
            np.save(stream, values, allow_pickle=False)
            atomic_bytes(target, stream.getvalue())
            seconds = time.monotonic() - start
            report = dict(manifest_sha256=manifest_sha, input_sha256=entry['sha256'],
                          audit_sha256=audit_sha, count=len(rows), tokens=token_count,
                          seconds=seconds, priority=entry['priority'], vectors=descriptor(target))
            atomic_json(output / (entry['name'] + '.done.json'), report)
            new_count += len(rows)
            new_tokens += token_count
            completed += 1
            elapsed = time.monotonic() - started
            progress = dict(event='progress', complete_shards=completed,
                            total_shards=len(manifest['shards']), new_vectors=new_count,
                            resumed_vectors=resumed, total_vectors=manifest['unique_pending'],
                            elapsed_seconds=elapsed, vectors_per_second=new_count / elapsed,
                            tokens_per_second=new_tokens / elapsed,
                            remaining_hours_same_mix=(manifest['unique_pending'] - resumed - new_count)
                            * elapsed / new_count / 3600,
                            eta_caveat='Current shard mix only; lengths differ across corpus',
                            peak_vram_bytes=encoder.torch.cuda.max_memory_allocated())
            atomic_json(output / 'progress.json', progress)
            print(json.dumps(progress), flush=True)
        atomic_json(output / 'run.json', dict(complete=completed == len(manifest['shards']),
                    completed_shards=completed, total_shards=len(manifest['shards']),
                    manifest_sha256=manifest_sha, elapsed_seconds=time.monotonic() - started))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bundle', type=Path, default=Path('.'))
    parser.add_argument('--output', type=Path, default=Path('results'))
    parser.add_argument('--dtype', choices=('bfloat16', 'float32'), default='bfloat16')
    parser.add_argument('--token-budget', type=int, default=65536)
    parser.add_argument('--max-batch', type=int, default=256)
    parser.add_argument('--max-shards', type=int, default=0, help='0: all; first shards give a measured pilot')
    parser.add_argument('--cpu-audit', action='store_true', help='Local audit only; cannot publish')
    args = parser.parse_args()
    if args.token_budget < 2048 or not 1 <= args.max_batch <= 1024 or args.max_shards < 0:
        parser.error('invalid batch limits')
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt()))
    run(args)


if __name__ == '__main__':
    main()
