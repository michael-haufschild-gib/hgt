"""Explicit offline embedding parity/throughput probe. Never used by queries.

Run with dedicated Python: python -m research_runtime.probe_embedding
The parent command owns a bounded foreground child so stalled kernels stop.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

from .config import DEFAULT_CACHE_DIR, CONTEXT_TOKENS, installation_status, offline_environment
from .processes import terminate_owned, cancellation_signals


def probe(cache_dir, count=32):
    from .adapters import enforce_offline
    enforce_offline()
    import torch
    from transformers import AutoModel, AutoTokenizer
    path = installation_status(cache_dir)['models']['embedding']['path']
    tokenizer = AutoTokenizer.from_pretrained(path, local_files_only=True, trust_remote_code=False,
                                              padding_side='right')
    model = AutoModel.from_pretrained(path, local_files_only=True, trust_remote_code=False,
                                     dtype=torch.float32, attn_implementation='sdpa').eval()
    texts = ['theorem refl (n : ℕ) : n = n := rfl',
             'theorem add_comm (m n : ℕ) : m + n = n + m := by omega',
             'A spectral gap gives a coercivity estimate on the orthogonal complement. '*8,
             'by exact h']
    texts = [(text + '\n') * 600 for text in texts]
    texts = [text[:5000-i*137] for i, text in enumerate(texts)]
    inputs = tokenizer(texts, padding=True, truncation=True, max_length=CONTEXT_TOKENS, return_tensors='pt')
    torch.set_num_threads(2)

    def embed(batch, device):
        batch = batch.to(device)
        with torch.inference_mode():
            hidden = model(**batch, use_cache=False).last_hidden_state
            lengths = batch['attention_mask'].sum(dim=1)-1
            last = hidden[torch.arange(hidden.shape[0], device=device), lengths]
            return torch.nn.functional.normalize(last.float(), p=2, dim=1).cpu()

    cpu = embed(inputs, 'cpu')
    if not torch.backends.mps.is_available():
        raise RuntimeError('MPS unavailable for probe')
    model.to('mps')
    mps = embed(inputs, 'mps')
    finite = bool(torch.isfinite(mps).all().item())
    max_error = (cpu-mps).abs().max().item() if finite else None
    cosines = (cpu*mps).sum(dim=1).tolist() if finite else []
    report = {'mps_right_pad_finite': finite, 'max_abs_error_vs_cpu': max_error,
              'cosine_vs_cpu': cosines, 'dtype': 'float32', 'batch_size': 4,
              'token_limit': CONTEXT_TOKENS}
    print(json.dumps({'parity': report}), flush=True)
    if not finite or max_error > 0.001 or min(cosines) < 0.999:
        raise RuntimeError('right-padding parity gate failed')
    base = ('theorem bounded_spectral_coercivity (f : ℝ → ℝ) (h : ∀ x, 0 ≤ f x) : '
            '0 ≤ f 0 := by\n  exact h 0\n/- A lower bound on a quadratic form controls '
            'the norm on the orthogonal complement of its nullspace. -/\n')
    docs = [(base * 30)[:5000-(i%4)*137] for i in range(count)]
    start = time.monotonic()
    for offset in range(0,len(docs),4):
        batch = tokenizer(docs[offset:offset+4], padding=True, truncation=True,
                          max_length=CONTEXT_TOKENS, return_tensors='pt')
        out = embed(batch, 'mps')
        if not torch.isfinite(out).all().item():
            raise RuntimeError('non-finite long mixed-length embeddings')
    elapsed = time.monotonic()-start
    report.update({'documents':count, 'total_characters':sum(map(len,docs)),
                   'elapsed_seconds':elapsed, 'documents_per_second':count/elapsed})
    print(json.dumps(report), flush=True)


@cancellation_signals()
def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache-dir',type=Path,default=DEFAULT_CACHE_DIR)
    parser.add_argument('--seconds',type=float,default=180)
    parser.add_argument('--child',action='store_true')
    args=parser.parse_args()
    if args.child:
        probe(args.cache_dir)
        return
    child=subprocess.Popen([sys.executable,'-m','research_runtime.probe_embedding','--child',
                            '--cache-dir',str(args.cache_dir)],env=offline_environment(),start_new_session=True)
    try:
        code=child.wait(timeout=args.seconds)
        if code:
            raise SystemExit(code)
    finally:
        terminate_owned(child)


if __name__=='__main__':
    main()
