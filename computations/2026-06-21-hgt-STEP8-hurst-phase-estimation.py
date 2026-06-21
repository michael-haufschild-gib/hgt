#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 transfer: phase Hurst estimation bias.

NODE:
    Estimating H from finite data is highly sensitive to trends,
    nonstationarity, aggregation, and measurement noise.

STEP 8:
    Levenshtein-minimal HT transfer:
    - A_phase_hurst_estimation_bias:      10 / 33 = 0.3030
    - C_prime_cutoff_hurst_sensitivity:   20 / 33 = 0.6061
    - B_zero_shadow_scaling_bias:         22 / 33 = 0.6667

    Replace fBm/fGn path by a continuum vertical trace of the phase-defect
    observable Delta(s). Estimate an H-like variogram exponent from finite
    windows of Delta(t), then perturb by measurement noise and aggregation.

STEP 9 method #23:
    Classify boundary cases: clean, noisy, aggregated, left/middle/right strip,
    true/finite/random controls.
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


def dlog_finite(s: complex, primes: tuple[int, ...]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(g: complex, p: complex) -> float:
    return max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))


def phase_series(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> np.ndarray:
    vals = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true":
            p = dlog_zeta(s)
        elif kind == "finite":
            p = dlog_finite(s, primes)
        elif kind == "random":
            base = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(base) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        vals.append(phase_defect(g, p))
    return np.asarray(vals, dtype=float)


def aggregate(vals: np.ndarray, block: int) -> np.ndarray:
    usable = (len(vals) // block) * block
    return vals[:usable].reshape(-1, block).mean(axis=1)


def estimate_h(vals: np.ndarray) -> float:
    lags = [1, 2, 4, 8, 16, 32, 64]
    used = []
    vars_ = []
    for lag in lags:
        if lag >= len(vals) // 2:
            continue
        diff = vals[lag:] - vals[:-lag]
        vars_.append(float(np.var(diff)))
        used.append(lag)
    return 0.5 * float(np.polyfit(np.log(used), np.log(np.maximum(vars_, 1e-300)), 1)[0])


def summarize(kind: str, sigma: float, window: tuple[float, float], vals: np.ndarray, rng: np.random.Generator) -> None:
    inc_sd = float(np.std(np.diff(vals)))
    noisy = vals + rng.normal(0.0, 0.40 * inc_sd, size=vals.shape)
    agg4 = aggregate(vals, 4)
    shift = vals.copy()
    shift[len(shift) // 2 :] += 0.65 * float(np.std(vals))
    clean_h = estimate_h(vals)
    noisy_h = estimate_h(noisy)
    agg_h = estimate_h(agg4)
    shift_h = estimate_h(shift)
    spread = float(max(clean_h, noisy_h, agg_h, shift_h) - min(clean_h, noisy_h, agg_h, shift_h))
    print(
        f"{kind:6s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
        f"clean={clean_h:.4f} noisy={noisy_h:.4f} aggregate={agg_h:.4f} "
        f"shift={shift_h:.4f} artifact_spread={spread:.4f}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=768)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    rng = np.random.default_rng(2606212323)
    primes = first_primes(args.prime_count)
    print("STEP8/9 phase Hurst-estimation boundary cases")
    print(f"samples={args.samples} prime_count={args.prime_count} method=23 classify_boundary_cases")
    print("kind sigma window clean noisy aggregate shift artifact_spread")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for sigma in [0.3, 0.5, 0.7, 1.2]:
            for kind in ["true", "finite", "random"]:
                vals = phase_series(kind, sigma, window, args.samples, primes, rng)
                summarize(kind, sigma, window, vals, rng)
    print("\nreduction gate")
    print("Promote nothing if H-like estimates are artifact-sensitive for true and controls alike, or if right-strip true/finite collapse.")


if __name__ == "__main__":
    main()
