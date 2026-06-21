#!/usr/bin/env python3
"""STEP11 refinement monotone for phase-weld drift."""

from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path

import numpy as np


def load_base(path: str):
    spec = importlib.util.spec_from_file_location("arnold_phaseweld_base", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def drift(base, kind: str, sigma: float, samples: int, h: float, primes):
    windows = [(100.0, 170.0), (900.0, 970.0)]
    means = []
    for window in windows:
        seed = 830000 + int(100 * sigma) + samples + int(1e6 * h) + {"true": 1, "finite": 2, "random": 3}[kind]
        mean, _ = base.mean_phase_weld(kind, sigma, window, samples, primes, np.random.default_rng(seed), h)
        means.append(mean)
    return means[1] - means[0]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--module-path", default="computations/2026-06-21-conway-arnold-numerical-drift-phaseweld.py")
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    module_path = args.module_path
    if not Path(module_path).exists() and Path("/tmp/2026-06-21-conway-arnold-numerical-drift-phaseweld.py").exists():
        module_path = "/tmp/2026-06-21-conway-arnold-numerical-drift-phaseweld.py"
    base = load_base(module_path)
    primes = base.first_primes(args.prime_count)
    hs = [1e-3, 3e-4, 1e-4]
    sample_grid = [70, 100, 140, 190]
    print("STEP11 monotone: numerical refinement should shrink drift uncertainty")
    print(f"prime_count={args.prime_count}")
    print("kind sigma drift_s70 drift_s100 drift_s140 drift_s190 sample_range h_range verdict")
    for sigma in [0.3, 0.5, 0.7, 1.2]:
        for kind in ["true", "finite", "random"]:
            sample_drifts = [drift(base, kind, sigma, s, 1e-4, primes) for s in sample_grid]
            h_drifts = [drift(base, kind, sigma, 140, h, primes) for h in hs]
            sample_range = float(np.max(sample_drifts) - np.min(sample_drifts))
            h_range = float(np.max(h_drifts) - np.min(h_drifts))
            verdict = "stable" if sample_range < 0.03 and h_range < 0.002 else "fragile"
            print(
                f"{kind:6s} {sigma:.1f} "
                f"{sample_drifts[0]:9.4f} {sample_drifts[1]:10.4f} {sample_drifts[2]:10.4f} {sample_drifts[3]:10.4f} "
                f"{sample_range:11.5f} {h_range:8.5f} {verdict}"
            )


if __name__ == "__main__":
    main()
