#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 transfer: phase initial entropy gate.

NODE:
    Initial measures must satisfy entropy or association conditions in many
    limit theorems.

STEP 8:
    Levenshtein-minimal HT transfer:
    - A_phase_initial_entropy_gate:     23 / 35 = 0.6571
    - B_zero_shadow_association_gate:   24 / 35 = 0.6857
    - C_prime_cutoff_initial_measure:   29 / 35 = 0.8286

    Replace an initial exclusion configuration by a sigma-lane occupation
    field of phase-defect events along a continuum vertical window. Test
    whether matching lane marginals is enough, or whether cross-lane
    association changes empirical-field fluctuations.

STEP 9 method #16:
    Use a minimal counterexample. Compare the empirical joint sigma-lane field
    with a productized surrogate having exactly the same lane marginals.
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


def fields(
    sigmas: list[float],
    window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> dict[str, np.ndarray]:
    out = {kind: np.zeros((samples, len(sigmas)), dtype=float) for kind in ["true", "finite", "random"]}
    for j, t in enumerate(np.linspace(window[0], window[1], samples)):
        for i, sigma in enumerate(sigmas):
            s = complex(float(sigma), float(t))
            g = gamma_part(s)
            zp = dlog_zeta(s)
            fp = dlog_finite(s, primes)
            theta = rng.uniform(-math.pi, math.pi)
            rp = abs(zp) * complex(math.cos(theta), math.sin(theta))
            out["true"][j, i] = phase_defect(g, zp)
            out["finite"][j, i] = phase_defect(g, fp)
            out["random"][j, i] = phase_defect(g, rp)
    return out


def association_metrics(events: np.ndarray) -> dict[str, float]:
    p = np.mean(events, axis=0)
    lane_count = events.shape[1]
    empirical_mean = np.mean(events, axis=1)
    joint_var = float(np.var(empirical_mean))
    product_var = float(np.sum(p * (1.0 - p)) / (lane_count * lane_count))
    centered = events - p[None, :]
    cov = centered.T @ centered / events.shape[0]
    off = cov[~np.eye(lane_count, dtype=bool)]
    assoc_excess = joint_var - product_var
    return {
        "occ": float(np.mean(events)),
        "joint_var": joint_var,
        "product_var": product_var,
        "assoc_excess": assoc_excess,
        "excess_ratio": float(assoc_excess / max(product_var, 1e-12)),
        "off_cov_mean": float(np.mean(off)),
        "off_cov_abs": float(np.mean(np.abs(off))),
        "marginal_min": float(np.min(p)),
        "marginal_max": float(np.max(p)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=640)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    rng = np.random.default_rng(2606211617)
    primes = first_primes(args.prime_count)
    sigmas = [0.2, 0.3, 0.4, 0.5, 0.7, 0.9, 1.2]
    print("STEP8/9 phase initial entropy/association gate")
    print(f"samples={args.samples} prime_count={args.prime_count} method=16 minimal_counterexample")
    print("kind window threshold_mode threshold occ joint_var product_var assoc_excess excess_ratio off_cov_mean off_cov_abs marginal_min marginal_max")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        data = fields(sigmas, window, args.samples, primes, rng)
        thresholds = {
            "zero": 0.0,
            "true_q70": float(np.quantile(data["true"], 0.70)),
            "true_q85": float(np.quantile(data["true"], 0.85)),
        }
        for mode, threshold in thresholds.items():
            for kind in ["true", "finite", "random"]:
                events = data[kind] > threshold
                row = association_metrics(events.astype(float))
                print(
                    f"{kind:6s} [{window[0]:.0f},{window[1]:.0f}] {mode:8s} {threshold:.6g} "
                    f"{row['occ']:.4f} {row['joint_var']:.6f} {row['product_var']:.6f} "
                    f"{row['assoc_excess']:.6f} {row['excess_ratio']:.4f} "
                    f"{row['off_cov_mean']:.6f} {row['off_cov_abs']:.6f} "
                    f"{row['marginal_min']:.4f} {row['marginal_max']:.4f}"
                )
    print("\nreduction gate")
    print("Promote nothing if association excess is matched by finite/random controls or if thresholding makes marginals degenerate.")


if __name__ == "__main__":
    main()
