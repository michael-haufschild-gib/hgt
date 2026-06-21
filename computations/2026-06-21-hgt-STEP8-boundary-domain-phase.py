#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 transfer: phase boundary-domain geometry.

NODE:
    Considering boundary effects and domain geometry in crowded or confined
    systems.

STEP 8:
    Levenshtein-minimal HT transfer:
    - A_phase_boundary_domain_geometry:    16 / 34 = 0.4706
    - C_critical_strip_absorbing_domain:   27 / 34 = 0.7941
    - B_zero_shadow_reflecting_boundary:   29 / 34 = 0.8529

    Replace physical confinement by the chosen sigma-domain for a continuum
    phase-defect field Delta(s). Apparent diffusion exponent is fitted from
    MSD of Delta increments along t, averaged over the chosen sigma lanes.

STEP 9 method #16:
    Use a minimal counterexample. If the same true analytic field gives
    different apparent exponents under two sigma-domain choices, then the
    exponent is domain-geometry dependent before it is HT-specific.
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


def build_fields(
    sigmas: list[float],
    window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> dict[str, np.ndarray]:
    fields = {kind: np.zeros((len(sigmas), samples), dtype=float) for kind in ["true", "finite", "random"]}
    ts = np.linspace(window[0], window[1], samples)
    for i, sigma in enumerate(sigmas):
        for j, t in enumerate(ts):
            s = complex(float(sigma), float(t))
            g = gamma_part(s)
            zp = dlog_zeta(s)
            fp = dlog_finite(s, primes)
            theta = rng.uniform(-math.pi, math.pi)
            rp = abs(zp) * complex(math.cos(theta), math.sin(theta))
            fields["true"][i, j] = phase_defect(g, zp)
            fields["finite"][i, j] = phase_defect(g, fp)
            fields["random"][i, j] = phase_defect(g, rp)
    return fields


def fit_alpha(field: np.ndarray) -> tuple[float, float]:
    lags = np.asarray([1, 2, 4, 8, 16, 32], dtype=int)
    msd = []
    for lag in lags:
        d = field[:, lag:] - field[:, :-lag]
        msd.append(float(np.mean(d * d)))
    msd_arr = np.asarray(msd, dtype=float)
    alpha = float(np.polyfit(np.log(lags), np.log(np.maximum(msd_arr, 1e-300)), 1)[0])
    curvature = float((np.log(msd_arr[-1]) - np.log(msd_arr[-2])) - (np.log(msd_arr[1]) - np.log(msd_arr[0])))
    return alpha, curvature


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=512)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    rng = np.random.default_rng(2606211616)
    primes = first_primes(args.prime_count)
    sigmas = [0.2, 0.3, 0.4, 0.5, 0.7, 0.9, 1.2]
    domains = {
        "left_boundary": [0, 1, 2],
        "critical_core": [1, 2, 3],
        "middle": [2, 3, 4],
        "right": [4, 5, 6],
        "wide": [0, 1, 2, 3, 4, 5, 6],
        "boundary_removed": [1, 2, 3, 4, 5],
    }
    print("STEP8/9 phase boundary-domain geometry")
    print(f"samples={args.samples} prime_count={args.prime_count} method=16 minimal_counterexample")
    print("kind window domain alpha curvature")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        fields = build_fields(sigmas, window, args.samples, primes, rng)
        domain_alphas: dict[str, list[float]] = {kind: [] for kind in fields}
        for kind, field in fields.items():
            for name, idxs in domains.items():
                alpha, curvature = fit_alpha(field[idxs, :])
                domain_alphas[kind].append(alpha)
                print(f"{kind:6s} [{window[0]:.0f},{window[1]:.0f}] {name:16s} {alpha:8.4f} {curvature:9.4f}")
        for kind, vals in domain_alphas.items():
            arr = np.asarray(vals, dtype=float)
            print(
                f"DOMAIN_RANGE {kind:6s} [{window[0]:.0f},{window[1]:.0f}] "
                f"range={float(np.max(arr)-np.min(arr)):.4f} sd={float(np.std(arr)):.4f}"
            )
    print("\nreduction gate")
    print("If true's alpha changes strongly under domain choice, or controls have comparable domain range, the boundary-domain transfer reduces to geometry-dependent phase statistics.")


if __name__ == "__main__":
    main()
