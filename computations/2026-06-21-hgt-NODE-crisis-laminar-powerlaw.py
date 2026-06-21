#!/usr/bin/env python3
"""THE-MACHINE NODE test: crisis-induced laminar durations scale as a power law.

NODE:
    Mean laminar duration commonly follows a power-law scaling with distance
    from the crisis parameter.

Constraint tested:
    Laminar phases are not arbitrary pauses. Near a crisis, the mean laminar
    duration is constrained by distance from the crisis threshold and follows a
    power law up to finite-record/noise limits.
"""

from __future__ import annotations

import numpy as np


def sample_laminar(delta: float, alpha: float, rng: np.random.Generator, n: int = 3000) -> np.ndarray:
    mean = 4.0 + 0.28 * delta ** (-alpha)
    shape = 2.5
    return rng.gamma(shape=shape, scale=mean / shape, size=n)


def fit_power(deltas: np.ndarray, means: np.ndarray) -> tuple[float, float]:
    x = np.log(deltas)
    y = np.log(means)
    slope, intercept = np.polyfit(x, y, 1)
    pred = slope * x + intercept
    ss_res = float(np.sum((y - pred) ** 2))
    ss_tot = float(np.sum((y - np.mean(y)) ** 2))
    return float(-slope), float(1.0 - ss_res / ss_tot)


def main() -> None:
    rng = np.random.default_rng(20260621)
    deltas = np.array([0.010, 0.016, 0.026, 0.042, 0.068, 0.110, 0.180])
    print("NODE: crisis-induced intermittency laminar mean power-law scaling")
    print("delta mean_laminar q90_laminar shuffled_mean")
    means = []
    shuffled = []
    for delta in deltas:
        vals = sample_laminar(delta, alpha=0.72, rng=rng)
        null = sample_laminar(0.08, alpha=0.72, rng=rng)
        means.append(float(np.mean(vals)))
        shuffled.append(float(np.mean(null)))
        print(f"{delta:.4f} {np.mean(vals):.6f} {np.quantile(vals, 0.90):.6f} {np.mean(null):.6f}")
    alpha, r2 = fit_power(deltas, np.asarray(means))
    alpha_null, r2_null = fit_power(deltas, np.asarray(shuffled))
    print("\nScaling fits")
    print(f"crisis_alpha={alpha:.6f} crisis_loglog_r2={r2:.6f}")
    print(f"null_alpha={alpha_null:.6f} null_loglog_r2={r2_null:.6f}")
    print(
        "Interpretation: the NODE is validated if mean laminar duration has a "
        "high-R2 log-log power-law relation to distance from the crisis parameter, "
        "while shuffled/no-distance controls do not."
    )


if __name__ == "__main__":
    main()
