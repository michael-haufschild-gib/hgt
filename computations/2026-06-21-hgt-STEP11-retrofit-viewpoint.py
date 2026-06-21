#!/usr/bin/env python3
"""THE-MACHINE Step 11 for retrofit fatigue.

Method #4: change the viewpoint.

Raw fatigue amplification is dominated by the chosen p-norm/endurance floor.
This script changes viewpoint to a random-notch null distribution: is the
"bad retrofit" notch placement exceptional relative to random retrofit holes
for the same signal, or is the statistic just generic local roughness?
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


def signal(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> np.ndarray:
    vals = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "gamma-only":
            z = g
        elif kind == "true-zeta":
            z = g + dlog_zeta(s)
        elif kind == "finite-euler":
            z = g + dlog_finite_euler(s, primes)
        elif kind == "random-phase":
            p = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            z = g + abs(p) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        vals.append(math.log1p(abs(z)))
    return np.asarray(vals, dtype=float)


def damage(vals: np.ndarray, mask: np.ndarray, *, kt: float, q: float, exponent: float) -> float:
    endurance = float(np.quantile(vals, q))
    v = vals.copy()
    v[mask] *= kt
    return float(np.sum(np.maximum(v - endurance, 0.0) ** exponent))


def bad_mask(vals: np.ndarray, count: int) -> np.ndarray:
    grad = np.abs(np.gradient(vals))
    idx = np.argsort(grad)[-count:]
    mask = np.zeros(len(vals), dtype=bool)
    mask[idx] = True
    return mask


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=240)
    parser.add_argument("--prime-count", type=int, default=160)
    parser.add_argument("--random-masks", type=int, default=120)
    args = parser.parse_args()

    rng = np.random.default_rng(20260622)
    primes = first_primes(args.prime_count)
    cases = [(0.3, (100.0, 170.0)), (0.5, (100.0, 170.0)), (1.2, (100.0, 170.0))]
    kinds = ["gamma-only", "true-zeta", "finite-euler", "random-phase"]
    count = max(1, int(round(0.08 * args.samples)))

    print("STEP11 method #4: change viewpoint to random-notch null distribution")
    print(f"samples={args.samples} finite_prime_count={args.prime_count} random_masks={args.random_masks}")
    print("kind sigma exponent random_median random_q90 bad_damage bad_over_median bad_percentile")

    for sigma, window in cases:
        for exponent in [2.0, 5.0, 8.0]:
            for kind in kinds:
                vals = signal(kind, sigma, window, args.samples, primes, rng)
                random_damages = []
                for _ in range(args.random_masks):
                    idx = rng.choice(len(vals), size=count, replace=False)
                    mask = np.zeros(len(vals), dtype=bool)
                    mask[idx] = True
                    random_damages.append(damage(vals, mask, kt=2.4, q=0.70, exponent=exponent))
                random_arr = np.asarray(random_damages)
                bad = damage(vals, bad_mask(vals, count), kt=2.4, q=0.70, exponent=exponent)
                percentile = float(np.mean(random_arr <= bad))
                print(
                    f"{kind:12s} {sigma:.1f} {exponent:.0f} "
                    f"{np.median(random_arr):.6e} {np.quantile(random_arr,0.90):.6e} "
                    f"{bad:.6e} {bad / max(np.median(random_arr), 1e-300):.3e} {percentile:.3f}"
                )

    print(
        "\nInterpretation: if bad-retrofit placement is not exceptional, or if finite/gamma/random "
        "are equally or more exceptional, the transfer is a generic notch/p-norm artifact rather "
        "than HT-native fatigue structure."
    )


if __name__ == "__main__":
    main()
