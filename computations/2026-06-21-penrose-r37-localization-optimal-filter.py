#!/usr/bin/env python3
"""
R37 STEP 8/9 transfer to positivity/localization axis.

NODE: useful noise has a narrow optimum; more noise is not better.
Target transfer: localization filtering of an off-line quartet curvature core has
a scale-matched optimum; more smoothing is not better.

Method #3: reverse it.
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


def online_negative(tau: np.ndarray, a: float) -> np.ndarray:
    return -2.0 * a * a / ((a * a + tau * tau) ** 2)


def gaussian_kernel(x: np.ndarray, width: float) -> np.ndarray:
    k = np.exp(-0.5 * (x / width) ** 2)
    return k / k.sum()


def center_response(y: np.ndarray, k: np.ndarray) -> float:
    z = np.convolve(y, k[::-1], mode="same")
    return float(z[len(z) // 2])


def main() -> None:
    source = "narrow_optimal_noise_not_more_noise"
    attempts = [
        "narrow_optimal_smoothing_localization_axis",
        "more_regularization_erases_offline_core",
        "matched_noise_width_curvature_detector",
    ]
    print("STEP 8 Levenshtein attempts")
    for a in attempts:
        print(f"{a:48s} distance={levenshtein(source, a)}")
    print(f"selected={min(attempts, key=lambda x: levenshtein(source, x))}")

    a = 0.10
    t = np.linspace(-24 * a, 24 * a, 9601)
    dt = t[1] - t[0]
    off = quartet_curvature(t, a)
    on = online_negative(t, a)
    raw_peak = float(np.max(off))
    noise_sd = 0.35 * raw_peak

    print("\nSTEP 9 method 3: reverse 'more smoothing helps'")
    print("width/a  off_resp  on_resp   signal_gap  noise_after_filter  detection_z")
    best = (None, -1e9)
    for mult in [0.05, 0.08, 0.12, 0.18, 0.25, 0.35, 0.50, 0.75, 1.00, 1.50, 2.00, 3.00, 4.00, 6.00, 8.00]:
        x = np.arange(-max(6, int(6 * mult * a / dt)), max(6, int(6 * mult * a / dt)) + 1) * dt
        k = gaussian_kernel(x, mult * a)
        off_resp = center_response(off, k)
        on_resp = center_response(on, k)
        gap = off_resp - on_resp
        noise_after = noise_sd * float(np.sqrt(np.sum(k * k)))
        z = gap / (noise_after + 1e-12)
        if z > best[1]:
            best = (mult, z)
        print(f"{mult:7.2f} {off_resp:9.4f} {on_resp:8.4f} {gap:12.4f} {noise_after:19.6f} {z:12.4f}")
    print(f"\nTransfer verdict: best_width_over_a={best[0]:.2f}, best_detection_z={best[1]:.4f}; more smoothing is not better.")


if __name__ == "__main__":
    main()
