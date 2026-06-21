#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 transfer: phase exponent subset sensitivity.

NODE:
    The fitted allometric exponent often changes with taxonomic range,
    body-size range, and life stage included in the dataset.

STEP 8:
    Levenshtein-minimal HT transfer:
    - A_phase_exponent_subset_sensitivity:  9 / 38 = 0.2368
    - C_prime_cutoff_life_stage_scaling:   29 / 38 = 0.7632
    - B_zero_shadow_clade_range_slope:     31 / 38 = 0.8158

    Replace body-size by the archimedean lane magnitude log(1+|Gamma_infty|)
    and the biological trait by log(1+Delta), where
        Delta=max(log|Gamma_infty|, log|P|)-log|Gamma_infty+P|.

STEP 9 method #3:
    Reverse it. Instead of assuming subset-sensitive exponents, ask whether a
    universal phase exponent survives restrictions by sigma lane and height
    range. A useful signal must be true-specific and not shared by finite Euler
    or random-phase controls.
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
    if xs.size < 6 or float(np.std(xs)) < 1e-12 or float(np.std(ys)) < 1e-12:
        return float("nan")
    return float(np.polyfit(xs, ys, 1)[0])


def collect(
    kind: str,
    sigma: float,
    height_window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> tuple[np.ndarray, np.ndarray]:
    xs: list[float] = []
    ys: list[float] = []
    for t in np.linspace(height_window[0], height_window[1], samples):
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
    return np.asarray(xs, dtype=float), np.asarray(ys, dtype=float)


def summarize_kind(
    kind: str,
    sigmas: list[float],
    windows: list[tuple[float, float]],
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> None:
    all_x: list[np.ndarray] = []
    all_y: list[np.ndarray] = []
    sigma_slopes: dict[float, list[float]] = {sigma: [] for sigma in sigmas}
    window_slopes: dict[str, list[float]] = {f"[{a:.0f},{b:.0f}]": [] for a, b in windows}
    print(f"\nKIND {kind}")
    print("subset slope")
    for sigma in sigmas:
        for window in windows:
            xs, ys = collect(kind, sigma, window, samples, primes, rng)
            all_x.append(xs)
            all_y.append(ys)
            slope = fit_slope(xs, ys)
            sigma_slopes[sigma].append(slope)
            window_slopes[f"[{window[0]:.0f},{window[1]:.0f}]"].append(slope)
            print(f"sigma={sigma:.1f} window=[{window[0]:.0f},{window[1]:.0f}] {slope:.6f}")
    whole = fit_slope(np.concatenate(all_x), np.concatenate(all_y))
    by_sigma = {sigma: float(np.nanmedian(vals)) for sigma, vals in sigma_slopes.items()}
    by_window = {window: float(np.nanmedian(vals)) for window, vals in window_slopes.items()}
    vals = np.asarray(list(by_sigma.values()) + list(by_window.values()), dtype=float)
    finite_vals = vals[np.isfinite(vals)]
    slope_range = float(np.max(finite_vals) - np.min(finite_vals)) if finite_vals.size else float("nan")
    slope_sd = float(np.std(finite_vals)) if finite_vals.size else float("nan")
    print(f"SUMMARY {kind} whole={whole:.6f} subset_range={slope_range:.6f} subset_sd={slope_sd:.6f}")
    for sigma, slope in by_sigma.items():
        print(f"BY_SIGMA {kind} {sigma:.1f} {slope:.6f}")
    for window, slope in by_window.items():
        print(f"BY_WINDOW {kind} {window} {slope:.6f}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=180)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    rng = np.random.default_rng(2606210303)
    primes = first_primes(args.prime_count)
    sigmas = [0.3, 0.5, 0.7, 1.2]
    windows = [(14.0, 84.0), (100.0, 170.0), (500.0, 570.0)]
    print("STEP8/9 phase exponent subset-sensitivity")
    print(f"samples={args.samples} prime_count={args.prime_count} method=3 reverse_it")
    print("reverse_question=does a universal phase exponent survive sigma/window restriction?")
    for kind in ["true", "finite", "random"]:
        summarize_kind(kind, sigmas, windows, args.samples, primes, rng)
    print("\nreduction gate")
    print("Promote nothing if slope instability is shared by controls or if any apparent stability is caused by zero/degenerate phase-defect values.")


if __name__ == "__main__":
    main()
