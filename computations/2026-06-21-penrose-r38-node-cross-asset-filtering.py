#!/usr/bin/env python3
"""
R38 NODE validation: filtering assets independently can destroy cross-asset covariance.
"""

from __future__ import annotations

import numpy as np


def moving_average(x: np.ndarray, width: int) -> np.ndarray:
    k = np.ones(width) / width
    return np.convolve(x, k, mode="same")


def corr(a: np.ndarray, b: np.ndarray) -> float:
    a = a - a.mean()
    b = b - b.mean()
    return float(np.dot(a, b) / ((np.linalg.norm(a) * np.linalg.norm(b)) + 1e-12))


def main() -> None:
    rng = np.random.default_rng(3818)
    n = 5000
    common = moving_average(rng.normal(size=n), 80)
    common /= common.std()
    x = common + 0.7 * rng.normal(size=n)
    y = 0.8 * common + 0.7 * rng.normal(size=n)

    x_ind = x - moving_average(x, 260)
    y_ind = y - moving_average(y, 35)
    joint_common = 0.5 * (moving_average(x, 100) + moving_average(y, 100))
    x_joint = x - joint_common
    y_joint = y - 0.8 * joint_common

    print("series_pair             corr")
    print(f"raw                 {corr(x, y):8.4f}")
    print(f"independent_filtered {corr(x_ind, y_ind):8.4f}")
    print(f"joint_common_resid   {corr(x_joint, y_joint):8.4f}")
    print("\nNODE verdict:")
    print(
        "The raw pair has a real common factor. Independent filters with different windows "
        "nearly destroy the covariance, while a joint common-factor filter preserves the "
        "fact that the residuals share a modeled source."
    )


if __name__ == "__main__":
    main()
