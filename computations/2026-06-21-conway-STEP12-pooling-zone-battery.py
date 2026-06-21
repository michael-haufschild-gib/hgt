#!/usr/bin/env python3
"""STEP12 battery for transverse wet/gel/dry phase-zone coexistence."""

from __future__ import annotations

import argparse
import importlib.util
import math
import sys
from pathlib import Path

import numpy as np


def load_base(path: str):
    spec = importlib.util.spec_from_file_location("pooling_base", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def metrics(base, kind: str, sigmas: list[float], low: float, high: float, samples: int, primes, seed: int):
    rng = np.random.default_rng(seed)
    all_three = ordered = total = 0
    entropies = []
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for t in np.linspace(window[0], window[1], samples):
            vals = np.asarray([base.defect_at(kind, sigma, float(t), primes, rng) for sigma in sigmas])
            wet = vals > high
            gel = (vals > low) & (vals <= high)
            dry = vals <= low
            all_three += int(np.any(wet) and np.any(gel) and np.any(dry))
            ordered += int(vals[0] > high and vals[-1] <= low)
            counts = np.asarray([np.sum(wet), np.sum(gel), np.sum(dry)], dtype=float)
            probs = counts[counts > 0] / len(vals)
            entropies.append(float(-np.sum(probs * np.log(probs)) / math.log(3.0)))
            total += 1
    return all_three / total, float(np.mean(entropies)), ordered / total


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--module-path", default="computations/2026-06-21-conway-pooling-zone-coexistence.py")
    parser.add_argument("--samples", type=int, default=160)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    module_path = args.module_path
    if not Path(module_path).exists() and Path("/tmp/2026-06-21-conway-pooling-zone-coexistence.py").exists():
        module_path = "/tmp/2026-06-21-conway-pooling-zone-coexistence.py"
    base = load_base(module_path)
    primes = base.first_primes(args.prime_count)
    grids = {
        "coarse": [0.3, 0.5, 0.8, 1.2],
        "dense": [0.3, 0.4, 0.5, 0.7, 0.9, 1.2],
    }
    print("STEP12 battery: transverse phase-zone coexistence")
    print(f"samples_per_window={args.samples} prime_count={args.prime_count}")
    print("grid low high kind all_three entropy ordered")
    for grid_name, sigmas in grids.items():
        for low, high in [(0.15, 0.80), (0.20, 1.00), (0.30, 1.20), (0.40, 1.40)]:
            for kind in ["true", "finite", "random"]:
                seed = 1310000 + len(sigmas) * 1000 + int(100 * low) + int(100 * high) + {"true": 1, "finite": 2, "random": 3}[kind]
                all_three, entropy, ordered = metrics(base, kind, sigmas, low, high, args.samples, primes, seed)
                print(f"{grid_name:6s} {low:.2f} {high:.2f} {kind:6s} {all_three:.4f} {entropy:.4f} {ordered:.4f}")


if __name__ == "__main__":
    main()
