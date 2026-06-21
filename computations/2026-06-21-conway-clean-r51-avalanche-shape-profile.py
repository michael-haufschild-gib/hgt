#!/usr/bin/env python3
"""Clean GPT-topic finding 51 candidate: avalanche-shape source profile gate."""

from __future__ import annotations

import math

import numpy as np


def normalize(y: np.ndarray, x: np.ndarray) -> np.ndarray:
    area = float(np.trapezoid(y, x))
    return y / (area + 1e-300)


def skewness(y: np.ndarray, x: np.ndarray) -> float:
    p = normalize(y, x)
    mu = float(np.trapezoid(x * p, x))
    var = float(np.trapezoid((x - mu) ** 2 * p, x))
    third = float(np.trapezoid((x - mu) ** 3 * p, x))
    return third / ((var + 1e-300) ** 1.5)


def count_peaks(y: np.ndarray, min_rel_height: float = 0.18) -> int:
    cutoff = min_rel_height * float(np.max(y))
    peaks = 0
    if len(y) > 1 and y[0] > cutoff and y[0] >= y[1]:
        peaks += 1
    for i in range(1, len(y) - 1):
        if y[i] > cutoff and y[i] >= y[i - 1] and y[i] >= y[i + 1]:
            peaks += 1
    if len(y) > 1 and y[-1] > cutoff and y[-1] >= y[-2]:
        peaks += 1
    return peaks


def node_avalanche_shapes() -> None:
    t = np.linspace(0.0, 1.0, 501)
    fast_rise_slow_decay = t**1.2 * (1.0 - t) ** 3.2
    slow_rise_fast_decay = t**3.2 * (1.0 - t) ** 1.2
    symmetric = t**2.2 * (1.0 - t) ** 2.2
    rows = []
    for name, y in [
        ("fast_rise_slow_decay", fast_rise_slow_decay),
        ("slow_rise_fast_decay", slow_rise_fast_decay),
        ("symmetric", symmetric),
    ]:
        y = normalize(y, t)
        rows.append((name, float(np.trapezoid(y, t)), float(np.argmax(y) / (len(y) - 1)), skewness(y, t)))

    print("NODE: avalanche shape asymmetry is invisible to duration/size totals")
    print("shape area peak_time skewness")
    for name, area, peak, skew in rows:
        print(f"{name:22s} {area:.6f} {peak:.3f} {skew:+.3f}")
    print("constraint: the action is not just counting released mass; it is the time-profile of release")


def gaussian_profile(widths: np.ndarray, centers: list[float], weights: list[float], eps: float) -> np.ndarray:
    out = np.zeros_like(widths)
    for c, w in zip(centers, weights):
        boundary_factor = 2.0 if abs(c) < 1e-15 else 1.0
        out += (
            boundary_factor
            * w
            * np.exp(-0.5 * ((widths - c) / eps) ** 2)
            / (eps * math.sqrt(2.0 * math.pi))
        )
    return out


def profile_metrics(widths: np.ndarray, profile: np.ndarray) -> dict[str, float]:
    p = normalize(profile, widths)
    mean = float(np.trapezoid(widths * p, widths))
    second = float(np.trapezoid(widths**2 * p, widths))
    return {
        "area": float(np.trapezoid(profile, widths)),
        "mean": mean,
        "second": second,
        "peak_width": float(widths[int(np.argmax(profile))]),
        "skew": skewness(profile, widths),
        "peaks": float(count_peaks(profile)),
        "tail_share": float(np.trapezoid(profile[widths > 0.20], widths[widths > 0.20]) / (np.trapezoid(profile, widths) + 1e-300)),
    }


def transfer_source_profile_gate() -> None:
    widths = np.linspace(0.0, 0.34, 1200)
    eps = 0.012
    # Both off-seam configurations are symmetric across the critical seam in the
    # actual source plane; here the profile records absolute distance from seam.
    single_a = 0.16
    single_centers = [single_a]
    single_weights = [2.0]

    split_centers = [0.13, 0.19]
    # Same exterior charge and same source-width second moment as the single pair:
    # w1 + w2 = 2 and w1*c1^2 + w2*c2^2 = 2*single_a^2.
    c1, c2 = split_centers
    target_second_mass = 2.0 * single_a**2
    w1 = (2.0 * c2**2 - target_second_mass) / (c2**2 - c1**2)
    w2 = 2.0 - w1
    split_weights = [w1, w2]

    seam_centers = [0.0]
    seam_weights = [2.0]

    cases = {
        "seam_confined": (seam_centers, seam_weights),
        "off_single_pair": (single_centers, single_weights),
        "off_split_same_D2": (split_centers, split_weights),
    }

    print()
    print("TRANSFER: ResearchNode #31 bridge confinement half")
    print("method #6 ask what action is happening: nested contours release source mass by a profile, not a total")
    print("case charge second_mass profile_area profile_mean peak_width skew peaks tail_share")
    for name, (centers, weights) in cases.items():
        profile = gaussian_profile(widths, centers, weights, eps)
        metrics = profile_metrics(widths, profile)
        charge = float(np.sum(weights))
        second_mass = float(np.sum([w * c * c for c, w in zip(centers, weights)]))
        print(
            f"{name:18s} {charge:.6f} {second_mass:.6f} "
            f"{metrics['area']:.6f} {metrics['mean']:.6f} {metrics['peak_width']:.6f} "
            f"{metrics['skew']:+.3f} {int(metrics['peaks'])} {metrics['tail_share']:.3f}"
        )
    print()
    print("GATE SUMMARY")
    print(
        "same exterior charge and same D2 can still carry different nested-contour release shapes"
    )
    print(
        "bridge-confinement experiments should report the normalized source-avalanche profile "
        "(peak, skew/bimodality, tail share), not only endpoint charge or one source-width moment"
    )


def main() -> None:
    node_avalanche_shapes()
    transfer_source_profile_gate()


if __name__ == "__main__":
    main()
