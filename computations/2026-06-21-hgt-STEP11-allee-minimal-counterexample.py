#!/usr/bin/env python3
"""THE-MACHINE Step 11 for the Allee-threshold NODE.

Method #16: use a minimal counterexample.

Metaphor:
    An Allee threshold sounds like a clean survival/non-survival boundary. The
    tempting HT statement is that threshold survival distinguishes true
    analytic zeta from finite/random controls.

Counterexample search:
    Vary the required survival depth and threshold. If finite/random controls
    pass at shallow depth, or if true collapses away from the left strip, then
    the threshold picture adds no independent content beyond phase-defect
    run persistence.
"""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def first_primes(n: int) -> tuple[int, ...]:
    primes: list[int] = []
    candidate = 2
    while len(primes) < n:
        ok = True
        for p in primes:
            if p * p > candidate:
                break
            if candidate % p == 0:
                ok = False
                break
        if ok:
            primes.append(candidate)
        candidate += 1 if candidate == 2 else 2
    return tuple(primes)


def gamma_part(s: complex) -> complex:
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def dlog_zeta(s: complex, h: float = 1e-4) -> complex:
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite_euler(s: complex, primes: tuple[int, ...]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(g: complex, p: complex) -> float:
    return math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)


def run_lengths(mask: np.ndarray) -> list[int]:
    runs: list[int] = []
    cur = 0
    for val in mask:
        if bool(val):
            cur += 1
        elif cur:
            runs.append(cur)
            cur = 0
    if cur:
        runs.append(cur)
    return runs


def survive(defects: np.ndarray, threshold: float, depth: int) -> float:
    runs = run_lengths(defects > threshold)
    return float(np.mean([r >= depth for r in runs])) if runs else 0.0


def panel(sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], seed: int) -> dict[str, np.ndarray]:
    rng = np.random.default_rng(seed)
    rows = {"true": [], "finite": [], "ampmatched-finite": [], "random-phase": []}
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        p_true = dlog_zeta(s)
        p_finite = dlog_finite_euler(s, primes)
        theta = rng.uniform(-math.pi, math.pi)
        p_random = abs(p_true) * complex(math.cos(theta), math.sin(theta))
        p_amp = p_finite * (abs(p_true) / (abs(p_finite) + 1e-300))
        rows["true"].append(max(0.0, phase_defect(g, p_true)))
        rows["finite"].append(max(0.0, phase_defect(g, p_finite)))
        rows["ampmatched-finite"].append(max(0.0, phase_defect(g, p_amp)))
        rows["random-phase"].append(max(0.0, phase_defect(g, p_random)))
    return {k: np.asarray(v, dtype=float) for k, v in rows.items()}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=240)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()

    primes = first_primes(args.prime_count)
    thresholds = [0.0, 0.05, 0.10, 0.20, 0.35]
    depths = [2, 4, 8, 16, 32, 64]
    cases = [(0.3, (100.0, 170.0)), (0.3, (500.0, 570.0)), (0.5, (100.0, 170.0)), (1.2, (100.0, 170.0))]

    print("STEP11 method #16: minimal counterexamples to a threshold-survival claim")
    print(f"samples={args.samples} finite_prime_count={args.prime_count}")
    print("sigma window threshold depth true finite ampmatched random max_control separation")

    for case_i, (sigma, window) in enumerate(cases):
        defects = panel(sigma, window, args.samples, primes, seed=20260621 + case_i)
        for threshold in thresholds:
            for depth in depths:
                vals = {kind: survive(arr, threshold, depth) for kind, arr in defects.items()}
                max_control = max(vals["finite"], vals["ampmatched-finite"], vals["random-phase"])
                sep = vals["true"] - max_control
                print(
                    f"{sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {threshold:.2f} {depth:2d} "
                    f"{vals['true']:.3f} {vals['finite']:.3f} {vals['ampmatched-finite']:.3f} "
                    f"{vals['random-phase']:.3f} {max_control:.3f} {sep:.3f}"
                )

    print("\nBoundary interpretation")
    print(
        "A real new Allee-threshold observable would separate at shallow and long depths, "
        "or persist under right-strip/control stresses. Instead, shallow depths let finite "
        "or random controls pass, while long-depth separation only reuses the known left-strip "
        "phase-carrier persistence."
    )


if __name__ == "__main__":
    main()
