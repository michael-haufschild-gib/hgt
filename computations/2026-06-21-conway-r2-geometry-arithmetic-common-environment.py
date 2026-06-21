#!/usr/bin/env python3
"""Run-2 finding 51: common-environment coupling for divisor geometry/arithmetic."""

from __future__ import annotations

import math

import mpmath as mp
import numpy as np


def node_metapopulation_correlation(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    reps = 3_000
    patches = 8
    years = 28
    threshold = -1.05

    print("NODE: spatially correlated environments erase metapopulation rescue")
    print("rho all_extinct any_survives mean_survivor_patches")
    for rho in [0.0, 0.35, 0.70, 0.92]:
        all_extinct = 0
        survivor_counts: list[int] = []
        for _ in range(reps):
            alive = np.ones(patches, dtype=bool)
            for _year in range(years):
                common = rng.normal()
                private = rng.normal(size=patches)
                environment = math.sqrt(rho) * common + math.sqrt(1.0 - rho) * private
                alive &= environment > threshold
            survivor_count = int(alive.sum())
            survivor_counts.append(survivor_count)
            all_extinct += survivor_count == 0
        print(
            f"{rho:.2f} {all_extinct / reps:.4f} "
            f"{1.0 - all_extinct / reps:.4f} {np.mean(survivor_counts):.3f}"
        )
    print(
        "constraint: patch replication only supplies rescue when failures are not "
        "driven by one common environment"
    )
    print()


def first_zeros(count: int) -> np.ndarray:
    mp.mp.dps = 40
    return np.array([float(mp.im(mp.zetazero(n))) for n in range(1, count + 1)])


def geometry_signature(ordinates: np.ndarray) -> np.ndarray:
    gaps = np.diff(ordinates)
    hist, _ = np.histogram(gaps / np.mean(gaps), bins=np.linspace(0.0, 4.0, 25), density=True)
    lag_means = np.array(
        [np.mean(ordinates[k:] - ordinates[:-k]) for k in range(1, 21)]
    )
    return np.r_[hist, lag_means / np.mean(gaps)]


def arithmetic_signature(ordinates: np.ndarray, eps: float = 0.015) -> np.ndarray:
    prime_logs = np.log([2, 3, 5, 7, 11, 13])
    parts: list[float] = []
    for ell in prime_logs:
        frac = (ordinates * ell / (2.0 * math.pi)) % 1.0
        dist_to_integer = np.minimum(frac, 1.0 - frac)
        parts.append(float(np.mean(dist_to_integer < eps)))
        parts.append(float(np.mean(np.cos(2.0 * math.pi * frac))))
        parts.append(float(np.quantile(dist_to_integer, 0.05)))
    return np.array(parts)


def transfer_divisor_axes() -> None:
    ordinates = first_zeros(220)
    base_geometry = geometry_signature(ordinates)
    base_arithmetic = arithmetic_signature(ordinates)

    print("TRANSFER: ResearchNode #6 two axes at the divisor")
    print(
        "same-geometry fake ladder: translate all zero ordinates by delta; "
        "gap and pair geometry are preserved, prime-log arithmetic changes"
    )
    print("delta geometry_l2 arithmetic_l2 resonance_rate_vector")
    for delta in [0.0, 0.1, 0.5, 1.0, 2.0, 3.0, 5.0, 8.0, 13.0]:
        shifted = ordinates + delta
        geometry_l2 = float(np.linalg.norm(geometry_signature(shifted) - base_geometry))
        arithmetic_l2 = float(np.linalg.norm(arithmetic_signature(shifted) - base_arithmetic))
        resonance_rates = arithmetic_signature(shifted)[0::3]
        print(
            f"{delta:04.1f} {geometry_l2:.3e} {arithmetic_l2:.6f} "
            f"{np.array2string(resonance_rates, precision=4, separator=',')}"
        )

    rng = np.random.default_rng(20260621)
    arithmetic_shifts = []
    for delta in rng.uniform(0.0, 20.0, size=200):
        arithmetic_shifts.append(
            np.linalg.norm(arithmetic_signature(ordinates + delta) - base_arithmetic)
        )
    quantiles = np.quantile(arithmetic_shifts, [0.0, 0.25, 0.5, 0.75, 0.95, 1.0])
    print("random_shift_arithmetic_l2_quantiles", np.array2string(quantiles, precision=6))
    print()
    print("GATE SUMMARY")
    print(
        "divisor-geometry tests are common-environment coupled: many windows can agree "
        "because they share the same zero geometry"
    )
    print(
        "a value-axis detector must include a same-geometry/different-arithmetic fake ladder; "
        "otherwise divisor geometry is being mistaken for divisor arithmetic"
    )


def main() -> None:
    node_metapopulation_correlation()
    transfer_divisor_axes()


if __name__ == "__main__":
    main()
