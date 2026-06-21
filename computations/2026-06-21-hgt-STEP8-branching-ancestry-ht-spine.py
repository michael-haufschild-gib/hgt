#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 transfer: survival-conditioned phase ancestry.

NODE:
    Backward-in-time ancestry differs from forward-in-time population growth,
    especially under conditioning on survival.

STEP 8:
    Three HT transfers were scored by Levenshtein against the NODE constraint:
    - A_phase_ancestry_survivor_size_bias: 12 / 96 = 0.1250
    - C_jet_curvature_survival_spine:      25 / 109 = 0.2294
    - B_zero_shadow_component_spine:       31 / 109 = 0.2844

    Continue with A. Replace terminal surviving individuals by terminal
    positive phase-defect samples along vertical traces in C. Trace dyadic
    time-scale ancestors backward and ask whether terminal survival size-biases
    the ancestor intervals.

STEP 9 method #1:
    Split it into subclaims.
    S1: conditioning on terminal positive phase samples size-biases ancestor
        intervals relative to forward intervals;
    S2: the size-bias exceeds a shuffled-occupancy baseline, so it is not just
        the number of positive samples;
    S3: any HT meaning requires a true-zeta/finite/random separation with a
        left-strip boundary and finite-prime stress.
"""

from __future__ import annotations

import argparse
import math
from statistics import mean

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


def phase_series(
    kind: str,
    sigma: float,
    window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> np.ndarray:
    vals: list[float] = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true":
            p = dlog_zeta(s)
        elif kind == "finite":
            p = dlog_finite_euler(s, primes)
        elif kind == "random":
            base = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(base) * complex(math.cos(theta), math.sin(theta))
        elif kind == "gamma-only":
            p = 0.0 + 0.0j
        else:
            raise ValueError(kind)
        vals.append(max(0.0, phase_defect(g, p)))
    return np.asarray(vals, dtype=float)


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


def level_stats(mask: np.ndarray, level: int, rng: np.random.Generator, shuffles: int) -> tuple[float, float, float]:
    bins = 2**level
    width = len(mask) // bins
    trimmed = mask[: bins * width]
    loads = trimmed.reshape(bins, width).sum(axis=1).astype(float)
    forward = float(np.mean(loads))
    if loads.sum() <= 0 or forward <= 0:
        return 0.0, 0.0, 0.0
    backward = float(np.sum(loads * loads) / np.sum(loads))
    spine_ratio = backward / forward

    shuffled: list[float] = []
    for _ in range(shuffles):
        perm = np.array(trimmed, copy=True)
        rng.shuffle(perm)
        ploads = perm.reshape(bins, width).sum(axis=1).astype(float)
        pforward = float(np.mean(ploads))
        if ploads.sum() <= 0 or pforward <= 0:
            continue
        pback = float(np.sum(ploads * ploads) / np.sum(ploads))
        shuffled.append(pback / pforward)
    shuffle_ratio = float(mean(shuffled)) if shuffled else 0.0
    excess = math.log((spine_ratio + 1e-12) / (shuffle_ratio + 1e-12))
    return spine_ratio, shuffle_ratio, excess


def ancestry_summary(values: np.ndarray, threshold: float, rng: np.random.Generator, shuffles: int) -> dict[str, float]:
    mask = values > threshold
    runs = run_lengths(mask)
    levels = [2, 3, 4, 5, 6, 7]
    ratios = []
    baselines = []
    excesses = []
    for level in levels:
        ratio, baseline, excess = level_stats(mask, level, rng, shuffles)
        if ratio > 0:
            ratios.append(ratio)
            baselines.append(baseline)
            excesses.append(excess)
    return {
        "occupancy": float(np.mean(mask)),
        "median_delta": float(np.median(values)),
        "run_median": float(np.median(runs)) if runs else 0.0,
        "run_q90": float(np.quantile(runs, 0.90)) if runs else 0.0,
        "spine_ratio": float(mean(ratios)) if ratios else 0.0,
        "shuffle_ratio": float(mean(baselines)) if baselines else 0.0,
        "excess_log": float(mean(excesses)) if excesses else 0.0,
    }


def scan_cases(samples: int, prime_count: int, threshold: float, shuffles: int) -> None:
    primes = first_primes(prime_count)
    rng = np.random.default_rng(260621191)
    windows = [(100.0, 170.0), (500.0, 570.0), (14.0, 84.0)]
    sigmas = [0.3, 0.5, 0.7, 1.2]
    print("STEP8/9 HT survival-conditioned phase ancestry")
    print(f"samples={samples} prime_count={prime_count} threshold={threshold} shuffles={shuffles}")
    print("S1: terminal positive phase samples size-bias ancestor intervals.")
    print("S2: excess_log compares observed spine-ratio with shuffled occupancy baseline.")
    print("S3: HT meaning requires true-vs-control separation plus boundary/stress behavior.")
    print(
        "kind sigma window occupancy median_delta run_median run_q90 "
        "spine_ratio shuffle_ratio excess_log"
    )
    for sigma in sigmas:
        for window in windows:
            for kind in ["true", "finite", "random", "gamma-only"]:
                vals = phase_series(kind, sigma, window, samples, primes, rng)
                row = ancestry_summary(vals, threshold, rng, shuffles)
                print(
                    f"{kind:10s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                    f"{row['occupancy']:.3f} {row['median_delta']:.4f} "
                    f"{row['run_median']:.1f} {row['run_q90']:.1f} "
                    f"{row['spine_ratio']:.3f} {row['shuffle_ratio']:.3f} {row['excess_log']:.4f}"
                )


def finite_prime_stress(samples: int, threshold: float, shuffles: int) -> None:
    rng = np.random.default_rng(260621192)
    sigma = 0.3
    window = (100.0, 170.0)
    true_vals = phase_series("true", sigma, window, samples, first_primes(30), rng)
    true_row = ancestry_summary(true_vals, threshold, rng, shuffles)
    print("\nFinite-prime stress at sigma=0.3 window=[100,170]")
    print("N kind occupancy run_q90 spine_ratio shuffle_ratio excess_log true_excess_gap")
    for n in [30, 80, 160, 240, 400]:
        primes = first_primes(n)
        vals = phase_series("finite", sigma, window, samples, primes, rng)
        row = ancestry_summary(vals, threshold, rng, shuffles)
        gap = true_row["excess_log"] - row["excess_log"]
        print(
            f"{n:3d} finite {row['occupancy']:.3f} {row['run_q90']:.1f} "
            f"{row['spine_ratio']:.3f} {row['shuffle_ratio']:.3f} "
            f"{row['excess_log']:.4f} {gap:.4f}"
        )
    print(
        f"true reference occupancy={true_row['occupancy']:.3f} "
        f"run_q90={true_row['run_q90']:.1f} excess_log={true_row['excess_log']:.4f}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=512)
    parser.add_argument("--prime-count", type=int, default=160)
    parser.add_argument("--threshold", type=float, default=0.0)
    parser.add_argument("--shuffles", type=int, default=24)
    args = parser.parse_args()
    scan_cases(args.samples, args.prime_count, args.threshold, args.shuffles)
    finite_prime_stress(args.samples, args.threshold, args.shuffles)


if __name__ == "__main__":
    main()
