#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 transfer: phase covariance range gate.

NODE:
    Short-range associated fields differ from long-range dependent associated
    fields, which may have nonstandard limits.

STEP 8:
    Levenshtein-minimal HT transfer:
    - A_phase_covariance_range_gate:          24 / 34 = 0.7059
    - B_zero_shadow_long_memory_gate:         28 / 34 = 0.8235
    - C_prime_cutoff_covariance_summability: 30 / 35 = 0.8571

    Replace the associated field by a continuum vertical trace of the
    phase-defect observable Delta(s). Test whether block-sum variance scales
    like n (short range) or n^beta with beta > 1 (long-range-like).

STEP 9 method #12:
    Find an invariant. Use the fitted block-variance exponent beta as a
    covariance-range invariant and compare true, finite, and random controls.
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


def series(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> np.ndarray:
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


def block_variance_exponent(vals: np.ndarray) -> dict[str, float]:
    x = vals - float(np.mean(vals))
    blocks = np.asarray([8, 16, 32, 64, 128], dtype=int)
    variances = []
    for b in blocks:
        usable = (len(x) // b) * b
        sums = x[:usable].reshape(-1, b).sum(axis=1)
        variances.append(float(np.var(sums)))
    variances_arr = np.asarray(variances, dtype=float)
    beta = float(np.polyfit(np.log(blocks), np.log(np.maximum(variances_arr, 1e-300)), 1)[0])
    ratio = float((variances_arr[-1] / blocks[-1]) / max(variances_arr[0] / blocks[0], 1e-300))
    return {
        "beta": beta,
        "var_per_step_ratio": ratio,
        "var8": float(variances_arr[0]),
        "var128": float(variances_arr[-1]),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=1024)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    rng = np.random.default_rng(2606211212)
    primes = first_primes(args.prime_count)
    print("STEP8/9 phase covariance-range invariant")
    print(f"samples={args.samples} prime_count={args.prime_count} method=12 find_invariant")
    print("kind sigma window beta var_per_step_ratio var8 var128")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for sigma in [0.3, 0.5, 0.7, 1.2]:
            for kind in ["true", "finite", "random"]:
                row = block_variance_exponent(series(kind, sigma, window, args.samples, primes, rng))
                print(
                    f"{kind:6s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                    f"{row['beta']:.4f} {row['var_per_step_ratio']:.4f} "
                    f"{row['var8']:.6g} {row['var128']:.6g}"
                )
    print("\nreduction gate")
    print("Promote nothing if beta>1 is matched by finite/random controls or if right-strip true/finite collapse.")


if __name__ == "__main__":
    main()
