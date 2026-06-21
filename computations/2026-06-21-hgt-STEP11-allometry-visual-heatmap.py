#!/usr/bin/env python3
"""THE-MACHINE Step 11: visual phase-exponent growth chart.

Metaphor:
    An allometric exponent is like a growth-chart slope. If the same organism
    is being measured, the chart should not redraw itself when we choose a
    different clade, size band, or life stage.

Scientific method #5:
    Make it visual. Build a sigma-by-height heatmap of fitted phase exponents
    and compare visual roughness/coherence against finite/random controls.
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


def fit_slope(xs: np.ndarray, ys: np.ndarray) -> float:
    if xs.size < 8 or float(np.std(xs)) < 1e-12 or float(np.std(ys)) < 1e-12:
        return float("nan")
    return float(np.polyfit(xs, ys, 1)[0])


def slope_for(
    kind: str,
    sigma: float,
    window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> float:
    xs: list[float] = []
    ys: list[float] = []
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
        xs.append(math.log1p(abs(g)))
        ys.append(math.log1p(phase_defect(g, p)))
    return fit_slope(np.asarray(xs), np.asarray(ys))


def symbol(value: float) -> str:
    if not np.isfinite(value):
        return "?"
    if value < -0.8:
        return "v"
    if value < -0.25:
        return "-"
    if value < 0.25:
        return "."
    if value < 0.8:
        return "+"
    return "^"


def roughness(mat: np.ndarray) -> float:
    vals = []
    for axis in [0, 1]:
        diff = np.diff(mat, axis=axis)
        vals.extend(np.abs(diff[np.isfinite(diff)]).tolist())
    return float(np.mean(vals)) if vals else float("nan")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=120)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    rng = np.random.default_rng(2606210505)
    primes = first_primes(args.prime_count)
    sigmas = [0.2, 0.3, 0.5, 0.7, 0.9, 1.2]
    windows = [(14.0, 84.0), (100.0, 170.0), (260.0, 330.0), (500.0, 570.0)]
    mats: dict[str, np.ndarray] = {}

    print("STEP11 visual phase-exponent heatmap")
    print(f"samples={args.samples} prime_count={args.prime_count} method=5 make_visual")
    print("columns=[14,84] [100,170] [260,330] [500,570]")
    for kind in ["true", "finite", "random"]:
        mat = np.zeros((len(sigmas), len(windows)), dtype=float)
        for i, sigma in enumerate(sigmas):
            for j, window in enumerate(windows):
                mat[i, j] = slope_for(kind, sigma, window, args.samples, primes, rng)
        mats[kind] = mat
        print(f"\nHEATMAP {kind}")
        for sigma, row in zip(sigmas, mat):
            print(f"sigma={sigma:.1f} " + " ".join(symbol(v) for v in row) + "   " + " ".join(f"{v:+.2f}" for v in row))
        print(f"SUMMARY {kind} roughness={roughness(mat):.4f} mean={float(np.nanmean(mat)):.4f} sd={float(np.nanstd(mat)):.4f}")

    print("\nPAIRWISE_FROBENIUS")
    for a, b in [("true", "finite"), ("true", "random"), ("finite", "random")]:
        diff = mats[a] - mats[b]
        print(f"{a}_vs_{b} {float(np.linalg.norm(diff)):.4f}")

    print("\nreduction gate")
    print("A visual slope texture is not promoted if it is as rough as controls or if true/finite collapse in right-side rows.")


if __name__ == "__main__":
    main()
