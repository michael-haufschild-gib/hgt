#!/usr/bin/env python3
"""
R38 STEP 8/9 transfer to G-C15: one object, two entrances.

NODE: independent filtering can destroy cross-asset covariance.
Target: the Jacobi/Krein and Jensen/LP routes should be coordinate presentations
of one completed object; independent route filtering can erase their common fake
response.

Method #13: find a monotone quantity.
"""

from __future__ import annotations

import numpy as np


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, start=1):
        row = [i]
        for j, cb in enumerate(b, start=1):
            row.append(min(prev[j] + 1, row[-1] + 1, prev[j - 1] + (0 if ca == cb else 1)))
        prev = row
    return prev[-1]


def quartet_curvature(tau: np.ndarray, a: float) -> np.ndarray:
    return 2.0 * (a * a - tau * tau) / ((a * a + tau * tau) ** 2)


def gaussian_filter(y: np.ndarray, dt: float, width: float) -> np.ndarray:
    radius = min(len(y) // 2 - 1, max(6, int(6 * width / dt)))
    x = np.arange(-radius, radius + 1) * dt
    k = np.exp(-0.5 * (x / width) ** 2)
    k /= k.sum()
    return np.convolve(y, k, mode="same")


def corr(x: np.ndarray, y: np.ndarray) -> float:
    x = x - x.mean()
    y = y - y.mean()
    return float(np.dot(x, y) / ((np.linalg.norm(x) * np.linalg.norm(y)) + 1e-12))


def main() -> None:
    source = "independent_filtering_destroys_cross_asset_covariance"
    attempts = [
        "independent_route_filtering_destroys_gc15_covariance",
        "one_object_two_entrances_joint_filter",
        "jacobi_jensen_cross_route_covariance",
    ]
    print("STEP 8 Levenshtein attempts")
    for a in attempts:
        print(f"{a:56s} distance={levenshtein(source, a)}")
    print(f"selected={min(attempts, key=lambda x: levenshtein(source, x))}")

    a = 0.10
    t = np.linspace(-12 * a, 12 * a, 6001)
    dt = t[1] - t[0]
    # Route A: signed curvature/localization proxy.
    route_a = quartet_curvature(t, a)
    # Route B: Jensen/LP-style defect-core proxy: same object, different coordinate.
    route_b = np.exp(-0.5 * (t / (0.42 * a)) ** 2) - 0.12 * np.exp(-0.5 * (t / (1.5 * a)) ** 2)

    print("\nSTEP 9 method 13: route covariance vs independent filter mismatch")
    print("width_A/a width_B/a mismatch_log_abs corr")
    width_a = 0.50 * a
    base = gaussian_filter(route_a, dt, width_a)
    rows = []
    for wb_mult in [0.08, 0.12, 0.18, 0.25, 0.35, 0.50, 0.75, 1.00, 1.50, 2.00, 3.00, 4.00, 6.00]:
        rb = gaussian_filter(route_b, dt, wb_mult * a)
        mismatch = abs(np.log(wb_mult / 0.50))
        c = corr(base, rb)
        rows.append((mismatch, c))
        print(f"{0.50:9.2f} {wb_mult:9.2f} {mismatch:16.6f} {c: .6f}")
    monotone = all(rows[i][1] >= rows[i + 1][1] - 1e-9 for i in range(5, len(rows) - 1))
    print(f"\nright_tail_monotone_decrease_from_match={int(monotone)}")
    print(
        "Interpretation: a shared off-line object can look decorrelated if the two G-C15 "
        "entrances are filtered at incompatible scales; joint scale selection is part of "
        "the conjecture's fake-family translation requirement."
    )


if __name__ == "__main__":
    main()
