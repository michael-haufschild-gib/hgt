#!/usr/bin/env python3
"""THE-MACHINE Step 11: similar objects for phase-state metastability.

Method #8:
    Look for similar objects.

Question:
    Is the apparent metastability of high phase states HT-specific, or do
    smooth/order-correlated controls with the same marginal histogram reproduce
    the same finite dwell behavior?
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path

import numpy as np


def load_step8_module():
    path = Path(__file__).with_name("2026-06-21-hgt-STEP8-epigenetic-metastability-phase.py")
    spec = importlib.util.spec_from_file_location("metastable_step8", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def quantile_map(source: np.ndarray, target: np.ndarray) -> np.ndarray:
    order = np.argsort(source, kind="mergesort")
    target_sorted = np.sort(target)
    out = np.zeros_like(source, dtype=float)
    out[order] = target_sorted
    return out


def ar1(n: int, rho: float, rng: np.random.Generator) -> np.ndarray:
    x = np.zeros(n)
    noise = rng.normal(size=n)
    for i in range(1, n):
        x[i] = rho * x[i - 1] + noise[i]
    return x


def sine_control(n: int, cycles: float, rng: np.random.Generator) -> np.ndarray:
    t = np.linspace(0, 2 * np.pi * cycles, n)
    return np.sin(t) + 0.08 * rng.normal(size=n)


def report(module, label: str, vals: np.ndarray) -> tuple[float, float, float, float, float]:
    row = module.metastability(vals, 0.50)
    return row["median"], row["max"], row["s8"], row["s32"], row["escape_h"]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=420)
    parser.add_argument("--prime-count", type=int, default=180)
    args = parser.parse_args()
    module = load_step8_module()
    primes = module.first_primes(args.prime_count)
    rng = np.random.default_rng(260621082)
    print("STEP11 similar-object metastability controls")
    print(f"samples={args.samples} prime_count={args.prime_count}")
    print("sigma window object median_run max_run survive8 survive32 escape_h")
    for sigma in [0.3, 0.5, 0.7, 1.2]:
        for window in [(100.0, 170.0), (500.0, 570.0)]:
            true_vals = module.series("true", sigma, window, args.samples, primes, rng)
            finite_vals = module.series("finite", sigma, window, args.samples, primes, rng)
            random_vals = module.series("random", sigma, window, args.samples, primes, rng)
            controls = {
                "true": true_vals,
                "finite": finite_vals,
                "random": random_vals,
                "true_shuffled": rng.permutation(true_vals),
                "sine_histmatched": quantile_map(sine_control(args.samples, cycles=7.0, rng=rng), true_vals),
                "ar1_095_histmatched": quantile_map(ar1(args.samples, rho=0.95, rng=rng), true_vals),
                "ar1_060_histmatched": quantile_map(ar1(args.samples, rho=0.60, rng=rng), true_vals),
            }
            for name, vals in controls.items():
                med, mx, s8, s32, escape = report(module, name, vals)
                print(
                    f"{sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {name:20s} "
                    f"{med:.1f} {mx:.0f} {s8:.3f} {s32:.3f} {escape:.0f}"
                )


if __name__ == "__main__":
    main()
