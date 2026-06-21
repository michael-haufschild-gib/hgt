#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 transfer: phase catalog scaling depth.

NODE:
    Early fractal-cosmology arguments often relied on shallower catalogs whose
    apparent scaling could change with deeper surveys.

STEP 8:
    Levenshtein-minimal HT transfer:
    - A_phase_catalog_scaling_depth: 11 / 30 = 0.3667
    - B_zero_shadow_survey_depth:    23 / 30 = 0.7667
    - C_prime_event_counts_depth:    26 / 30 = 0.8667

    Replace a galaxy catalog by a continuum vertical catalog of phase-defect
    events in s = sigma + it. Survey depth is trace length. Apparent scaling is
    the fitted exponent of event counts versus subdepth.

STEP 9 method #21:
    Build a dependency chain:
    continuum trace -> fixed event threshold -> count-vs-depth exponent ->
    depth stability -> true-specificity versus finite/random controls.
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


def trace_bundle(
    sigma: float,
    t0: float,
    span: float,
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> dict[str, np.ndarray]:
    out = {"true": [], "finite": [], "random": []}
    for t in np.linspace(t0, t0 + span, samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        true_p = dlog_zeta(s)
        finite_p = dlog_finite(s, primes)
        theta = rng.uniform(-math.pi, math.pi)
        random_p = abs(true_p) * complex(math.cos(theta), math.sin(theta))
        out["true"].append(phase_defect(g, true_p))
        out["finite"].append(phase_defect(g, finite_p))
        out["random"].append(phase_defect(g, random_p))
    return {k: np.asarray(v, dtype=float) for k, v in out.items()}


def fit_count_exponent(vals: np.ndarray, threshold: float, depth: int) -> tuple[float, int]:
    clipped = vals[:depth]
    events = clipped > threshold
    subdepths = np.unique(np.geomspace(max(16, depth // 16), depth, 18).astype(int))
    counts = np.asarray([np.count_nonzero(events[:d]) for d in subdepths], dtype=float)
    mask = counts >= 3.0
    if np.count_nonzero(mask) < 4:
        return float("nan"), int(np.count_nonzero(events))
    return float(np.polyfit(np.log(subdepths[mask]), np.log(counts[mask]), 1)[0]), int(np.count_nonzero(events))


def run_case(kind: str, vals: np.ndarray, threshold: float, depths: list[int]) -> list[tuple[int, float, int]]:
    return [(depth, *fit_count_exponent(vals, threshold, depth)) for depth in depths]


def summarize_case(
    sigma: float,
    t0: float,
    bundle: dict[str, np.ndarray],
    depths: list[int],
) -> None:
    threshold = float(np.quantile(bundle["true"], 0.80))
    print(f"\nCASE sigma={sigma:.1f} t0={t0:.0f} threshold_true_q80={threshold:.6g}")
    print("kind depth event_count exponent label")
    drift: dict[str, float] = {}
    for kind in ["true", "finite", "random"]:
        rows = run_case(kind, bundle[kind], threshold, depths)
        shallow_exp = rows[1][1]
        deep_exp = rows[-1][1]
        drift[kind] = abs(deep_exp - shallow_exp) if np.isfinite(shallow_exp) and np.isfinite(deep_exp) else float("nan")
        for depth, exponent, count in rows:
            if not np.isfinite(exponent):
                label = "too_sparse"
            elif exponent < 0.70:
                label = "sublinear"
            elif exponent > 1.20:
                label = "superlinear"
            else:
                label = "linear_like"
            print(f"{kind:6s} {depth:5d} {count:11d} {exponent:8.4f} {label}")
    print(
        "DEPTH_DRIFT "
        + " ".join(f"{kind}={value:.4f}" if np.isfinite(value) else f"{kind}=nan" for kind, value in drift.items())
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=1024)
    parser.add_argument("--span", type=float, default=320.0)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()

    rng = np.random.default_rng(2606212121)
    primes = first_primes(args.prime_count)
    depths = [96, 160, 256, 384, 640, args.samples]
    print("STEP8/9 phase catalog scaling-depth test")
    print(f"samples={args.samples} span={args.span} prime_count={args.prime_count}")
    print("dependency_chain=trace->fixed_threshold->count_exponent->depth_drift->controls")
    for sigma in [0.3, 0.5, 1.2]:
        for t0 in [100.0, 500.0]:
            bundle = trace_bundle(sigma, t0, args.span, args.samples, primes, rng)
            summarize_case(sigma, t0, bundle, depths)

    print("\nreduction gate")
    print("A depth-drift signal is not promoted if finite Euler or random-phase controls have comparable drift, or if true/finite collapse in the right strip.")


if __name__ == "__main__":
    main()
