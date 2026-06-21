#!/usr/bin/env python3
"""STEP12 battery for context-phase scrambling monotonicity."""

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


def traces_windows(base, kind: str, sigma: float, samples: int, primes: tuple[int, ...], rng: np.random.Generator, windows):
    gs: list[complex] = []
    ps: list[complex] = []
    for window in windows:
        for t in np.linspace(window[0], window[1], samples):
            s = complex(float(sigma), float(t))
            g = base.gamma_part(s)
            if kind == "true":
                p = base.dlog_zeta(s)
            elif kind == "finite":
                p = base.dlog_finite_euler(s, primes)
            else:
                z = base.dlog_zeta(s)
                theta = rng.uniform(-math.pi, math.pi)
                p = abs(z) * complex(math.cos(theta), math.sin(theta))
            gs.append(g)
            ps.append(p)
    return np.asarray(gs, dtype=np.complex128), np.asarray(ps, dtype=np.complex128)


def max_fraction(base, g: np.ndarray, p: np.ndarray, threshold: float, noise: float, rng: np.random.Generator) -> float:
    forces = [0.0, 0.75, 1.5, 2.25, 3.0, 3.75, 4.5, 5.25, 6.0]
    phase_noise = np.exp(1j * rng.normal(0.0, noise, size=p.shape))
    best = 0.0
    for force in forces:
        lam = 0.11 * math.exp(0.43 * force)
        defect = base.phase_defect(g, lam * phase_noise * p)
        best = max(best, float(np.mean(defect > threshold)))
    return best


def noise_curve(base, g, p, threshold: float, reps: int, seed_base: int):
    noises = [0.0, 0.10, 0.20, 0.35, 0.55, 0.80, 1.10, 1.50, 2.00]
    means = []
    for n_i, noise in enumerate(noises):
        vals = []
        for rep in range(reps):
            rng = np.random.default_rng(seed_base + 1000 * n_i + rep)
            vals.append(max_fraction(base, g, p, threshold, noise, rng))
        means.append(float(np.mean(vals)))
    violations = sum(1 for a, b in zip(means, means[1:]) if b > a + 1e-4)
    drop = means[-1] / max(means[0], 1e-12)
    return means, violations, drop


def print_curve(label: str, means: list[float], violations: int, drop: float) -> None:
    print(f"{label} start={means[0]:.4f} end={means[-1]:.4f} drop={drop:.4f} violations={violations} means={','.join(f'{x:.4f}' for x in means)}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--module-path", default="computations/2026-06-21-conway-catch-context.py")
    parser.add_argument("--samples", type=int, default=140)
    parser.add_argument("--prime-count", type=int, default=160)
    parser.add_argument("--replicates", type=int, default=16)
    args = parser.parse_args()
    module_path = args.module_path
    if not Path(module_path).exists() and Path("/tmp/2026-06-21-conway-catch-context.py").exists():
        module_path = "/tmp/2026-06-21-conway-catch-context.py"
    base = load_base(module_path)
    primes = base.first_primes(args.prime_count)
    combined = [(100.0, 170.0), (500.0, 570.0)]
    print("STEP12 battery: context-phase monotone under phase scrambling")
    print(f"samples_per_window={args.samples} prime_count={args.prime_count} replicates={args.replicates}")

    print("\nSECTION threshold_sweep combined_windows")
    for threshold in [0.8, 1.0, 1.2]:
        for sigma in [0.3, 0.5, 1.2]:
            for kind in ["true", "finite", "random"]:
                rng = np.random.default_rng(121000 + int(100 * sigma) + {"true": 1, "finite": 2, "random": 3}[kind])
                g, p = traces_windows(base, kind, sigma, args.samples, primes, rng, combined)
                means, violations, drop = noise_curve(base, g, p, threshold, args.replicates, 131000 + int(1000 * threshold) + int(100 * sigma) + {"true": 10, "finite": 20, "random": 30}[kind])
                print_curve(f"threshold={threshold:.1f} kind={kind:6s} sigma={sigma:.1f}", means, violations, drop)

    print("\nSECTION window_sweep threshold_1.0")
    for win_name, windows in [
        ("low", [(100.0, 170.0)]),
        ("high", [(500.0, 570.0)]),
        ("combined", combined),
    ]:
        for sigma in [0.3, 0.5, 1.2]:
            for kind in ["true", "finite", "random"]:
                rng = np.random.default_rng(141000 + len(win_name) + int(100 * sigma) + {"true": 1, "finite": 2, "random": 3}[kind])
                g, p = traces_windows(base, kind, sigma, args.samples, primes, rng, windows)
                means, violations, drop = noise_curve(base, g, p, 1.0, args.replicates, 151000 + len(win_name) + int(100 * sigma) + {"true": 10, "finite": 20, "random": 30}[kind])
                print_curve(f"window={win_name:8s} kind={kind:6s} sigma={sigma:.1f}", means, violations, drop)

    print("\nSECTION finite_prime_sweep threshold_1.0 combined_windows")
    for sigma in [0.3, 0.5]:
        for count in [30, 80, 160, 320]:
            local_primes = base.first_primes(count)
            rng = np.random.default_rng(161000 + count + int(100 * sigma))
            g, p = traces_windows(base, "finite", sigma, args.samples, local_primes, rng, combined)
            means, violations, drop = noise_curve(base, g, p, 1.0, args.replicates, 171000 + count + int(100 * sigma))
            print_curve(f"finite_N={count:3d} sigma={sigma:.1f}", means, violations, drop)


if __name__ == "__main__":
    main()
