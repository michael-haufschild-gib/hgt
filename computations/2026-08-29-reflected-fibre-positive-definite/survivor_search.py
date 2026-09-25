#!/usr/bin/env python3
"""Random hostile search for smallest reflected-fibre Gram failure.

Diagnostic only. No output may be imported into Lean proofs.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import os
import sys
import time
from multiprocessing import Pool
from pathlib import Path

os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")

import mpmath as mp
import numpy as np


HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("pdscan", HERE / "run_experiments.py")
pdscan = importlib.util.module_from_spec(spec)
assert spec.loader is not None
sys.modules[spec.name] = pdscan
spec.loader.exec_module(pdscan)


def random_worker(task):
    x, size, seed, count = task
    rng = np.random.default_rng(seed)
    best_value = math.inf
    best_points = None
    batch_size = 2000
    for start in range(0, count, batch_size):
        batch = min(batch_size, count - start)
        scales = 10 ** rng.uniform(-3.0, 0.8, size=(batch, 1))
        gaps = rng.exponential(1.0, size=(batch, size - 1))
        gaps /= gaps.sum(axis=1, keepdims=True)
        points = np.concatenate((np.zeros((batch, 1)), np.cumsum(gaps, axis=1)), axis=1)
        points *= scales
        differences = points[:, :, None] - points[:, None, :]
        matrices = pdscan.reflected_fibre_float(x, differences)
        eigenvalues = np.linalg.eigvalsh(matrices)[:, 0]
        index = int(np.argmin(eigenvalues))
        if eigenvalues[index] < best_value:
            best_value = float(eigenvalues[index])
            best_points = points[index].tolist()
    return {"x": x, "size": size, "minimum_eigenvalue": best_value,
            "points": best_points, "seed": seed, "count": count}


def gram_min_mp(x, points):
    points = [mp.mpf(point) for point in points]
    size = len(points)
    matrix = mp.matrix(size)
    for i in range(size):
        for j in range(size):
            matrix[i, j] = pdscan.reflected_fibre_mp(x, points[i] - points[j])
    return min(mp.eigsy(matrix, eigvals_only=True))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="survivor-results.json")
    parser.add_argument("--workers", type=int, default=max(1, os.cpu_count() or 1))
    parser.add_argument("--points-per-case", type=int, default=2_560_000)
    parser.add_argument("--centers", type=int, default=2)
    parser.add_argument("--dps", type=int, default=100)
    args = parser.parse_args()
    started = time.time()
    centers = np.linspace(0.0, 137 / 2000, args.centers).tolist()
    cases = [(x, size) for x in centers for size in (4, 5)]
    tasks = []
    per_worker = math.ceil(args.points_per_case / args.workers)
    for case_index, (x, size) in enumerate(cases):
        remaining = args.points_per_case
        seed = 2026082900 + case_index * 10000
        while remaining:
            count = min(per_worker, remaining)
            tasks.append((x, size, seed, count))
            remaining -= count
            seed += 1
    with Pool(args.workers) as pool:
        records = list(pool.imap_unordered(random_worker, tasks, chunksize=1))
    best = {}
    for record in records:
        key = (record["x"], record["size"])
        if key not in best or record["minimum_eigenvalue"] < best[key]["minimum_eigenvalue"]:
            best[key] = record
    mp.mp.dps = args.dps
    summaries = []
    for key in sorted(best):
        record = best[key]
        verified = gram_min_mp(record["x"], record["points"])
        summaries.append({**record,
            "high_precision_minimum_eigenvalue": mp.nstr(verified, 70),
            "high_precision_sign": int(mp.sign(verified))})
    result = {
        "scope": "diagnostic only; forbidden as Lean input",
        "parameters": vars(args),
        "total_packets": len(cases) * args.points_per_case,
        "cases": summaries,
        "elapsed_seconds": time.time() - started,
    }
    Path(args.output).write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
