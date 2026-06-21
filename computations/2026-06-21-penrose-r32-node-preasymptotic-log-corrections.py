#!/usr/bin/env python3
"""
R32 NODE test: pre-asymptotic logarithmic corrections.

Constraint tested:
  A fitted logarithmic correction at an upper critical dimension is meaningful
  only if it survives nested-window and holdout checks. Long finite windows can
  show apparently clean log scaling while still being pre-asymptotic.
"""

from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np


@dataclass
class Fit:
    name: str
    lo: float
    hi: float
    alpha: float
    beta: float
    rmse: float
    holdout_rmse: float


def fit_power_log(t: np.ndarray, y: np.ndarray, lo: float, hi: float) -> Fit:
    mask = (t >= lo) & (t <= hi)
    x = np.column_stack([np.ones(mask.sum()), np.log(t[mask]), np.log(np.log(t[mask]))])
    coef, *_ = np.linalg.lstsq(x, np.log(y[mask]), rcond=None)
    pred = x @ coef
    rmse = float(np.sqrt(np.mean((pred - np.log(y[mask])) ** 2)))

    hold = (t > hi) & (t <= min(t.max(), hi * hi / lo))
    if hold.sum() >= 5:
        hx = np.column_stack([np.ones(hold.sum()), np.log(t[hold]), np.log(np.log(t[hold]))])
        holdout_rmse = float(np.sqrt(np.mean((hx @ coef - np.log(y[hold])) ** 2)))
    else:
        holdout_rmse = float("nan")
    return Fit("power_log", lo, hi, float(coef[1]), float(coef[2]), rmse, holdout_rmse)


def report_case(name: str, t: np.ndarray, y: np.ndarray) -> None:
    print(f"\nCASE {name}")
    prev_beta = None
    for lo, hi in [(1e2, 1e4), (1e3, 1e5), (1e4, 1e6), (1e5, 1e7), (1e6, 1e9)]:
        fit = fit_power_log(t, y, lo, hi)
        drift = float("nan") if prev_beta is None else fit.beta - prev_beta
        print(
            f"window=[{lo:.0e},{hi:.0e}] "
            f"alpha={fit.alpha:+.4f} beta={fit.beta:+.4f} "
            f"beta_drift={drift:+.4f} rmse={fit.rmse:.5f} "
            f"holdout={fit.holdout_rmse:.5f}"
        )
        prev_beta = fit.beta


def main() -> None:
    rng = np.random.default_rng(3207)
    t = np.logspace(2, 10, 900)
    alpha = -1.0

    true_log = t**alpha * np.log(t) ** 0.75

    # No asymptotic log correction, but a slow crossover factor that mimics one.
    slow = t**alpha * np.exp(3.6 / (1.0 + (np.log(t) / 14.0) ** 1.7))

    # True log correction plus a weak critical-point offset term.
    offset = t**alpha * np.log(t) ** 0.75 * (1.0 + 0.22 * t ** -0.08)

    # Multiplicative measurement noise is small enough that fit quality alone
    # looks convincing on finite windows.
    noise = np.exp(0.006 * rng.normal(size=t.size))
    report_case("true_asymptotic_log_beta_0.75", t, true_log * noise)
    report_case("preasymptotic_slow_crossover_no_log", t, slow * noise)
    report_case("true_log_plus_slow_offset", t, offset * noise)

    print("\nNODE verdict:")
    print(
        "Finite windows can have small RMSE and stable-looking log fits while the "
        "estimated beta drifts across nested windows; the constraint is a "
        "nested-window/holdout stability gate, not a single good log-log fit."
    )


if __name__ == "__main__":
    main()
