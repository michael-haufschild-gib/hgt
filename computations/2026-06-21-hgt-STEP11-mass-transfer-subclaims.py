#!/usr/bin/env python3
"""THE-MACHINE Step 11 for mass-transfer catalytic hot spots.

Method #1: split into subclaims.

Subclaims:
1. Transport/supply normalization changes hot-spot ranking.
2. True zeta remains separated from finite/random controls after normalization.
3. The separation is stable across smoothing widths defining the transport field.
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
    return max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))


def moving_mean(x: np.ndarray, width: int) -> np.ndarray:
    kernel = np.ones(max(3, width), dtype=float)
    kernel /= kernel.sum()
    return np.convolve(x, kernel, mode="same")


def arrays(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> tuple[np.ndarray, np.ndarray]:
    defect = []
    supply_raw = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true":
            p = dlog_zeta(s)
        elif kind == "finite":
            p = dlog_finite_euler(s, primes)
        elif kind == "random-phase":
            pt = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(pt) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        defect.append(phase_defect(g, p))
        supply_raw.append(math.log1p(abs(g) + abs(p)))
    return np.asarray(defect), np.asarray(supply_raw)


def top_overlap(a: np.ndarray, b: np.ndarray, q: float = 0.90) -> float:
    ma = a >= np.quantile(a, q)
    mb = b >= np.quantile(b, q)
    return float(np.mean(ma & mb) / max(np.mean(ma), 1e-300))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=260)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()

    rng = np.random.default_rng(20260622)
    primes = first_primes(args.prime_count)
    widths = [5, 13, 29, 57]
    cases = [(0.3, (100.0, 170.0)), (0.3, (500.0, 570.0)), (0.5, (100.0, 170.0)), (1.2, (100.0, 170.0))]

    print("STEP11 method #1: split mass-transfer transfer into subclaims")
    print(f"samples={args.samples} finite_prime_count={args.prime_count}")
    print("kind sigma window width raw_q90 apparent_q90 top_overlap raw_sep_vs_finite apparent_sep_vs_finite")
    cache: dict[tuple[str, float, tuple[float, float]], tuple[np.ndarray, np.ndarray]] = {}
    for sigma, window in cases:
        for kind in ["true", "finite", "random-phase"]:
            cache[(kind, sigma, window)] = arrays(kind, sigma, window, args.samples, primes, rng)
        finite_defect, finite_supply_raw = cache[("finite", sigma, window)]
        for width in widths:
            finite_app = finite_defect / (moving_mean(finite_supply_raw, width) + 1e-9)
            finite_raw_q90 = float(np.quantile(finite_defect, 0.90))
            finite_app_q90 = float(np.quantile(finite_app, 0.90))
            for kind in ["true", "finite", "random-phase"]:
                defect, supply_raw = cache[(kind, sigma, window)]
                app = defect / (moving_mean(supply_raw, width) + 1e-9)
                print(
                    f"{kind:12s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {width:2d} "
                    f"{np.quantile(defect,0.90):.6f} {np.quantile(app,0.90):.6f} "
                    f"{top_overlap(app, defect):.3f} "
                    f"{np.quantile(defect,0.90) - finite_raw_q90:.6f} "
                    f"{np.quantile(app,0.90) - finite_app_q90:.6f}"
                )

    print(
        "\nInterpretation: if top_overlap stays high and true-vs-finite separation is "
        "already present before normalization, the mass-transfer metaphor adds no new "
        "observable."
    )


if __name__ == "__main__":
    main()
