#!/usr/bin/env python3
"""Clean GPT-topic finding 55 candidate: reciprocal-coordinate sightline passport."""

from __future__ import annotations

import math

import mpmath as mp
import numpy as np


def node_observer_height() -> None:
    observer_heights = {"child": 1.15, "seated": 1.25, "adult": 1.70}
    partition_heights = [1.10, 1.30, 1.55, 1.80]
    print("NODE: observer-height assumptions privilege a sightline")
    print("observer visible_partitions blocked_partitions")
    for name, eye in observer_heights.items():
        visible = sum(eye > h for h in partition_heights)
        blocked = len(partition_heights) - visible
        print(f"{name:8s} {visible} {blocked}")
    print("constraint: visibility is correct only relative to the declared observer-height coordinate")


def first_zero_ordinates(n: int) -> np.ndarray:
    mp.mp.dps = 40
    return np.array([float(mp.im(mp.zetazero(i))) for i in range(1, n + 1)], dtype=float)


def sightline_metrics(gammas: np.ndarray, k: int) -> dict[str, float]:
    weights = gammas ** (-2 * k)
    weights = weights / float(np.sum(weights))
    cdf = np.cumsum(weights)
    idx90 = int(np.searchsorted(cdf, 0.90) + 1)
    idx99 = int(np.searchsorted(cdf, 0.99) + 1)
    eff = 1.0 / float(np.sum(weights**2))
    return {
        "first1": float(weights[0]),
        "first5": float(np.sum(weights[:5])),
        "first20": float(np.sum(weights[:20])),
        "n_eff": eff,
        "idx90": float(idx90),
        "idx99": float(idx99),
    }


def transfer_reciprocal_sightline() -> None:
    gammas = first_zero_ordinates(160)
    print()
    print("TRANSFER: ResearchNode #2 reciprocal seam coordinate")
    print("method #1 split subclaims: correct chart vs finite-computation sightline coverage")
    print("k first1_share first5_share first20_share effective_zero_count zeros_for_90pct zeros_for_99pct")
    for k in [1, 2, 3, 4, 6, 8]:
        m = sightline_metrics(gammas, k)
        print(
            f"{k:02d} {m['first1']:.4f} {m['first5']:.4f} {m['first20']:.4f} "
            f"{m['n_eff']:.2f} {int(m['idx90'])} {int(m['idx99'])}"
        )
    print()
    print("GATE SUMMARY")
    print(
        "the reciprocal seam chart is canonical for RH, but finite T_k evidence has a sightline: "
        "higher k mostly sees the lowest zeros"
    )
    print(
        "report a reciprocal-coordinate sightline passport: contribution shares by height band, "
        "effective zero count, and tail coverage before treating finite moments as global evidence"
    )


def main() -> None:
    node_observer_height()
    transfer_reciprocal_sightline()


if __name__ == "__main__":
    main()
