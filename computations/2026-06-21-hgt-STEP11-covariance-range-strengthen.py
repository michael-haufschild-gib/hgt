#!/usr/bin/env python3
"""STEP 11: strengthen phase covariance-range test.

Scientific method #15:
    Strengthen the conjecture. A real covariance-range signal should survive
    rank normalization of each trace; raw marginal amplitude is too weak.
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


def normal_score(u: np.ndarray) -> np.ndarray:
    # Rational approximation to inverse normal CDF via erfinv from mpmath.
    clipped = np.clip(u, 1e-6, 1.0 - 1e-6)
    return np.asarray([float(mp.sqrt(2) * mp.erfinv(2 * x - 1)) for x in clipped], dtype=float)


def rank_gaussianize(vals: np.ndarray) -> np.ndarray:
    order = np.argsort(vals, kind="mergesort")
    ranks = np.empty_like(order, dtype=float)
    ranks[order] = np.arange(1, len(vals) + 1)
    return normal_score((ranks - 0.5) / len(vals))


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


def beta(vals: np.ndarray) -> float:
    x = vals - float(np.mean(vals))
    blocks = np.asarray([8, 16, 32, 64, 128], dtype=int)
    vars_ = []
    for b in blocks:
        usable = (len(x) // b) * b
        sums = x[:usable].reshape(-1, b).sum(axis=1)
        vars_.append(float(np.var(sums)))
    return float(np.polyfit(np.log(blocks), np.log(np.maximum(vars_, 1e-300)), 1)[0])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=768)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    rng = np.random.default_rng(2606211515)
    primes = first_primes(args.prime_count)
    print("STEP11 strengthen covariance-range test with rank normalization")
    print(f"samples={args.samples} prime_count={args.prime_count} method=15 strengthen")
    print("kind sigma window beta_raw beta_rank beta_shuffle_rank")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for sigma in [0.3, 0.5, 0.7, 1.2]:
            for kind in ["true", "finite", "random"]:
                vals = series(kind, sigma, window, args.samples, primes, rng)
                ranked = rank_gaussianize(vals)
                shuffled = ranked.copy()
                rng.shuffle(shuffled)
                print(
                    f"{kind:6s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                    f"{beta(vals):.4f} {beta(ranked):.4f} {beta(shuffled):.4f}"
                )
    print("\nreduction gate")
    print("If rank-normalized beta separation does not persist against controls, the strengthened covariance-range conjecture dies.")


if __name__ == "__main__":
    main()
