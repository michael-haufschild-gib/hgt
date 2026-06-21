#!/usr/bin/env python3
"""STEP11 backbone/percolation test for preferential seam paths."""

from __future__ import annotations

import argparse
import importlib.util
import sys
from collections import deque
from pathlib import Path

import numpy as np


def load_base(path: str):
    spec = importlib.util.spec_from_file_location("preferential_base", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def components(mask: np.ndarray):
    seen = np.zeros(mask.shape, dtype=bool)
    out = []
    for i in range(mask.shape[0]):
        for j in range(mask.shape[1]):
            if not mask[i, j] or seen[i, j]:
                continue
            q = deque([(i, j)])
            seen[i, j] = True
            cells = []
            while q:
                ci, cj = q.popleft()
                cells.append((ci, cj))
                for di, dj in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                    ni, nj = ci + di, cj + dj
                    if 0 <= ni < mask.shape[0] and 0 <= nj < mask.shape[1] and mask[ni, nj] and not seen[ni, nj]:
                        seen[ni, nj] = True
                        q.append((ni, nj))
            out.append(cells)
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--module-path", default="computations/2026-06-21-conway-preferential-seam-paths.py")
    parser.add_argument("--samples", type=int, default=180)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    module_path = args.module_path
    if not Path(module_path).exists() and Path("/tmp/2026-06-21-conway-preferential-seam-paths.py").exists():
        module_path = "/tmp/2026-06-21-conway-preferential-seam-paths.py"
    base = load_base(module_path)
    primes = base.first_primes(args.prime_count)
    sigmas = np.linspace(0.2, 1.2, 11)
    seam_rows = set(np.where(np.abs(sigmas - 0.5) <= 0.11)[0].tolist())
    print("STEP11 right-theorem test: connected high-capacity backbone")
    print(f"samples_per_window={args.samples} prime_count={args.prime_count}")
    print("window kind quantile occupied components largest_frac t_span seam_touch seam_t_span")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        window_name = f"{int(window[0])}-{int(window[1])}"
        for kind in ["true", "finite", "random"]:
            seed = 707900 + int(window[0]) + {"true": 1, "finite": 2, "random": 3}[kind]
            grid = base.capacity_grid(kind, sigmas, window, args.samples, primes, np.random.default_rng(seed))
            for qv in [0.65, 0.75, 0.85]:
                threshold = float(np.quantile(grid, qv))
                mask = grid >= threshold
                comps = components(mask)
                if comps:
                    sizes = np.asarray([len(c) for c in comps], dtype=float)
                    largest = comps[int(np.argmax(sizes))]
                    largest_frac = float(np.max(sizes) / max(np.sum(mask), 1))
                    cols = {j for _, j in largest}
                    rows = {i for i, _ in largest}
                    t_span = int(len(cols) == mask.shape[1])
                    seam_touch = int(bool(rows & seam_rows))
                    seam_cols = {j for i, j in largest if i in seam_rows}
                    seam_t_span = int(len(seam_cols) == mask.shape[1])
                else:
                    largest_frac = 0.0
                    t_span = seam_touch = seam_t_span = 0
                print(
                    f"{window_name:7s} {kind:6s} {qv:.2f} {np.mean(mask):8.4f} "
                    f"{len(comps):4d} {largest_frac:8.4f} {t_span:d} {seam_touch:d} {seam_t_span:d}"
                )


if __name__ == "__main__":
    main()
