#!/usr/bin/env python3
"""STEP 11: fake-proof audit for phase Hurst estimation.

Scientific method #19:
    Write the fake proof, then identify the exact gap.

Fake proof:
    "True zeta has a larger finite-window H-like phase exponent than finite
    Euler/random controls, hence true has a long-memory phase carrier."

Audit:
    The proof only works if the true-vs-control H gap survives aggregation,
    measurement noise, level shifts, and right-strip boundary cases. This
    script measures those exact failure points.
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


def aggregate(vals: np.ndarray, block: int) -> np.ndarray:
    usable = (len(vals) // block) * block
    return vals[:usable].reshape(-1, block).mean(axis=1)


def estimate_h(vals: np.ndarray) -> float:
    used = []
    vars_ = []
    for lag in [1, 2, 4, 8, 16, 32, 64]:
        if lag >= len(vals) // 2:
            continue
        d = vals[lag:] - vals[:-lag]
        vars_.append(float(np.var(d)))
        used.append(lag)
    return 0.5 * float(np.polyfit(np.log(used), np.log(np.maximum(vars_, 1e-300)), 1)[0])


def transforms(vals: np.ndarray, rng: np.random.Generator) -> dict[str, np.ndarray]:
    inc_sd = float(np.std(np.diff(vals)))
    shifted = vals.copy()
    shifted[len(vals) // 2 :] += 0.65 * float(np.std(vals))
    return {
        "clean": vals,
        "noise": vals + rng.normal(0.0, 0.40 * inc_sd, size=vals.shape),
        "aggregate4": aggregate(vals, 4),
        "shift": shifted,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=768)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    rng = np.random.default_rng(2606211919)
    primes = first_primes(args.prime_count)
    print("STEP11 fake-proof audit for phase Hurst estimation")
    print(f"samples={args.samples} prime_count={args.prime_count} method=19 fake_proof")
    print("sigma window transform true_H finite_H random_H true_minus_max_control fake_proof_survives")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for sigma in [0.3, 0.5, 0.7, 1.2]:
            base = {kind: series(kind, sigma, window, args.samples, primes, rng) for kind in ["true", "finite", "random"]}
            transformed = {kind: transforms(vals, rng) for kind, vals in base.items()}
            for mode in ["clean", "noise", "aggregate4", "shift"]:
                hs = {kind: estimate_h(transformed[kind][mode]) for kind in ["true", "finite", "random"]}
                gap = hs["true"] - max(hs["finite"], hs["random"])
                survives = int(gap > 0.08 and sigma < 1.0)
                print(
                    f"{sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {mode:10s} "
                    f"{hs['true']:.4f} {hs['finite']:.4f} {hs['random']:.4f} {gap:.4f} {survives}"
                )
    print("\nproof_gap")
    print("The fake proof fails wherever aggregation/noise/right-strip controls destroy or invert the true-minus-control H gap.")


if __name__ == "__main__":
    main()
