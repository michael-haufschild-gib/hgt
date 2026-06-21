#!/usr/bin/env python3
"""STEP 12 stress battery for finite-size rounding -> B2.

Candidate:
  One-scale smoothed source observables can misclassify symmetric off-seam
  source pairs as a single seam-confined defect. A B2 experiment needs an
  explicit multiscale/contour gate.
"""

from __future__ import annotations

import math

import numpy as np


def gaussian(x: np.ndarray, center: float, width: float) -> np.ndarray:
    return np.exp(-0.5 * ((x - center) / width) ** 2)


def laplace(x: np.ndarray, center: float, width: float) -> np.ndarray:
    return np.exp(-np.abs(x - center) / width)


def cauchy(x: np.ndarray, center: float, width: float) -> np.ndarray:
    return 1.0 / (1.0 + ((x - center) / width) ** 2)


KERNELS = {"gaussian": gaussian, "laplace": laplace, "cauchy": cauchy}


def count_peaks(y: np.ndarray, threshold_fraction: float = 0.10) -> int:
    threshold = float(np.max(y) * threshold_fraction)
    peaks: list[int] = []
    for i in range(1, len(y) - 1):
        if y[i] >= threshold and y[i] >= y[i - 1] and y[i] >= y[i + 1]:
            if peaks and i - peaks[-1] <= 2:
                if y[i] > y[peaks[-1]]:
                    peaks[-1] = i
            else:
                peaks.append(i)
    return len(peaks)


def density(grid: np.ndarray, delta: float, width: float, kernel_name: str, weight_ratio: float) -> np.ndarray:
    k = KERNELS[kernel_name]
    y = k(grid, 0.5 - delta, width) + weight_ratio * k(grid, 0.5 + delta, width)
    return y / (np.sum(y) + 1e-300)


def metrics(grid: np.ndarray, delta: float, width: float, kernel_name: str, weight_ratio: float) -> dict[str, float | int]:
    y = density(grid, delta, width, kernel_name, weight_ratio)
    peaks = count_peaks(y)
    mean = float(np.sum(grid * y))
    mode = float(grid[int(np.argmax(y))])
    seam_tolerance = 0.25 * width
    false_seam = int(peaks == 1 and abs(mode - 0.5) <= seam_tolerance)
    contour_small = int((0.5 - 0.5 * delta <= 0.5 - delta <= 0.5 + 0.5 * delta)) + int(
        (0.5 - 0.5 * delta <= 0.5 + delta <= 0.5 + 0.5 * delta)
    )
    contour_large = int((0.5 - 2.0 * delta <= 0.5 - delta <= 0.5 + 2.0 * delta)) + int(
        (0.5 - 2.0 * delta <= 0.5 + delta <= 0.5 + 2.0 * delta)
    )
    return {
        "peaks": peaks,
        "mean": mean,
        "mode": mode,
        "std": float(np.sqrt(np.sum((grid - mean) ** 2 * y))),
        "false_seam": false_seam,
        "contour_small": contour_small,
        "contour_large": contour_large,
    }


def true_seam_metrics(grid: np.ndarray, width: float, kernel_name: str) -> dict[str, float | int]:
    k = KERNELS[kernel_name]
    y = k(grid, 0.5, width)
    y = y / np.sum(y)
    return {
        "peaks": count_peaks(y),
        "mode": float(grid[int(np.argmax(y))]),
        "std": float(np.sqrt(np.sum((grid - 0.5) ** 2 * y))),
    }


def main() -> None:
    grid = np.linspace(0.0, 1.0, 4001)
    deltas = [0.003, 0.005, 0.010, 0.020, 0.050, 0.100]
    widths = [0.003, 0.005, 0.010, 0.020, 0.050, 0.100]
    ratios = [1.0, 1.25, 2.0, 4.0]
    print("STEP 12 B2 finite-size rounding battery")
    print("Question: can one-scale source smoothing distinguish true seam source from symmetric off-seam pair?")
    print("kernel weight_ratio false_seam_count total contour_small_zero_count resolved_count")
    for kernel in KERNELS:
        for ratio in ratios:
            false_count = 0
            resolved = 0
            contour_zero = 0
            total = 0
            for delta in deltas:
                for width in widths:
                    m = metrics(grid, delta, width, kernel, ratio)
                    false_count += int(m["false_seam"])
                    resolved += int(m["peaks"] >= 2)
                    contour_zero += int(m["contour_small"] == 0)
                    total += 1
            print(f"{kernel:8s} {ratio:4.2f} {false_count:3d} {total:3d} {contour_zero:3d} {resolved:3d}")

    print()
    print("TRUE SEAM CONTROL")
    print("kernel width peaks mode std")
    for kernel in KERNELS:
        for width in widths:
            m = true_seam_metrics(grid, width, kernel)
            print(f"{kernel:8s} {width:.3f} {int(m['peaks']):d} {float(m['mode']):.6f} {float(m['std']):.6f}")

    print()
    print("BOUNDARY ROWS FOR EQUAL PAIR")
    print("kernel delta width delta_over_width peaks mode std false_seam contour_small contour_large")
    for kernel in KERNELS:
        for delta in [0.005, 0.020, 0.050]:
            for width in [0.005, 0.020, 0.050]:
                m = metrics(grid, delta, width, kernel, 1.0)
                print(
                    f"{kernel:8s} {delta:.3f} {width:.3f} {delta / width:.2f} "
                    f"{int(m['peaks']):d} {float(m['mode']):.6f} {float(m['std']):.6f} "
                    f"{int(m['false_seam']):d} {int(m['contour_small']):d} {int(m['contour_large']):d}"
                )

    print()
    print(
        "Interpretation: equal-weight off-seam pairs have a stable false-seam "
        "regime across smoothing kernels when width is comparable to or larger "
        "than separation. Any contour with half-width below separation has "
        "zero charge, while a larger contour sees charge 2. Therefore one-scale "
        "B2 evidence is insufficient; B2 needs a multiscale contour/splitting gate."
    )


if __name__ == "__main__":
    main()
