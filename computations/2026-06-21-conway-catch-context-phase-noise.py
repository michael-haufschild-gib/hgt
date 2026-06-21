#!/usr/bin/env python3
"""STEP11 metaphor test: context phase scrambling as cofactor loss."""

from __future__ import annotations

import argparse
import importlib.util
import math
import sys
from pathlib import Path

import numpy as np


def load_base(path: str):
    spec = importlib.util.spec_from_file_location("catch_context_base", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def max_fraction_under_phase_noise(
    base,
    g: np.ndarray,
    p: np.ndarray,
    noise: float,
    threshold: float,
    rng: np.random.Generator,
) -> float:
    forces = np.asarray([0.0, 0.75, 1.5, 2.25, 3.0, 3.75, 4.5, 5.25, 6.0])
    lambda0 = 0.11
    alpha = 0.43
    phase_noise = np.exp(1j * rng.normal(0.0, noise, size=p.shape))
    vals = []
    for force in forces:
        lam = lambda0 * math.exp(alpha * float(force))
        defect = base.phase_defect(g, lam * phase_noise * p)
        vals.append(float(np.mean(defect > threshold)))
    return max(vals)


def monotone_violations(values: list[float]) -> int:
    return sum(1 for a, b in zip(values, values[1:]) if b > a + 1e-4)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--module-path", default="computations/2026-06-21-conway-catch-context.py")
    parser.add_argument("--samples", type=int, default=180)
    parser.add_argument("--prime-count", type=int, default=160)
    parser.add_argument("--threshold", type=float, default=1.0)
    parser.add_argument("--replicates", type=int, default=24)
    args = parser.parse_args()
    module_path = args.module_path
    if not Path(module_path).exists() and Path("/tmp/2026-06-21-conway-catch-context.py").exists():
        module_path = "/tmp/2026-06-21-conway-catch-context.py"
    base = load_base(module_path)
    primes = base.first_primes(args.prime_count)
    noises = [0.0, 0.10, 0.20, 0.35, 0.55, 0.80, 1.10, 1.50, 2.00]
    print("STEP11 metaphor: phase-context scrambling monotone test")
    print(f"samples_per_window={args.samples} prime_count={args.prime_count} threshold={args.threshold:.3f} replicates={args.replicates}")
    print("kind sigma means stds violations")
    for sigma in [0.3, 0.5, 1.2]:
        for kind in ["true", "finite", "random"]:
            trace_rng = np.random.default_rng(822000 + int(100 * sigma) + {"true": 1, "finite": 2, "random": 3}[kind])
            g, p = base.traces(kind, sigma, args.samples, primes, trace_rng)
            means = []
            stds = []
            for noise in noises:
                vals = []
                for rep in range(args.replicates):
                    rng = np.random.default_rng(913000 + int(1000 * noise) + rep + int(100 * sigma) + {"true": 11, "finite": 22, "random": 33}[kind])
                    vals.append(max_fraction_under_phase_noise(base, g, p, noise, args.threshold, rng))
                means.append(float(np.mean(vals)))
                stds.append(float(np.std(vals)))
            print(
                f"{kind:6s} {sigma:.1f} "
                f"{','.join(f'{x:.4f}' for x in means)} "
                f"{','.join(f'{x:.4f}' for x in stds)} "
                f"{monotone_violations(means)}"
            )


if __name__ == "__main__":
    main()
