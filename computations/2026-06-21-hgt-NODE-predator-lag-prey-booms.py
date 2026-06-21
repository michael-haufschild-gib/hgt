#!/usr/bin/env python3
"""THE-MACHINE NODE test: predator numerical response lags prey booms.

Constraint:
    Predator abundance is constrained by delayed reproduction/recruitment from
    earlier prey abundance.  If the lag matters, predator peaks should trail
    prey peaks and the prey crash depth should change with the delay.
"""

from __future__ import annotations

import math

import numpy as np


def simulate(tau: int, coupling: float, steps: int = 180) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    prey = np.zeros(steps)
    pred = np.zeros(steps)
    carrying = np.zeros(steps)
    prey[0] = 24.0
    pred[0] = 3.0
    for t in range(steps - 1):
        carrying[t] = 50.0 + 130.0 * math.exp(-((t - 45.0) / 18.0) ** 2)
        delayed = prey[max(0, t - tau)]
        attack = coupling * pred[t] * prey[t] / (35.0 + prey[t])
        prey_growth = 0.18 * (1.0 - prey[t] / carrying[t])
        pred_growth = -0.055 + 0.012 * delayed / (20.0 + delayed)
        prey[t + 1] = max(1e-9, prey[t] * math.exp(prey_growth) - attack)
        pred[t + 1] = max(1e-9, pred[t] * math.exp(pred_growth))
    carrying[-1] = 50.0 + 130.0 * math.exp(-((steps - 1 - 45.0) / 18.0) ** 2)
    return prey, pred, carrying


def best_corr_lag(prey: np.ndarray, pred: np.ndarray, max_lag: int = 30) -> tuple[int, float]:
    x = (prey - np.mean(prey)) / (np.std(prey) + 1e-12)
    y = (pred - np.mean(pred)) / (np.std(pred) + 1e-12)
    best_lag = 0
    best_score = -10.0
    for lag in range(max_lag + 1):
        score = float(np.mean(x[:-lag or None] * y[lag:]))
        if score > best_score:
            best_score = score
            best_lag = lag
    return best_lag, best_score


def main() -> None:
    print("NODE: predator numerical responses lagging behind prey booms")
    print("tau coupling prey_peak pred_peak peak_lag corr_lag corr_score crash_depth qualifies")
    for tau in [0, 2, 5, 8, 12, 18]:
        for coupling in [0.010, 0.018, 0.026]:
            prey, pred, _ = simulate(tau=tau, coupling=coupling)
            prey_peak = int(np.argmax(prey))
            pred_peak = int(np.argmax(pred))
            peak_lag = pred_peak - prey_peak
            corr_lag, corr_score = best_corr_lag(prey, pred)
            after_peak = prey[prey_peak : min(len(prey), prey_peak + 80)]
            crash_depth = 1.0 - float(np.min(after_peak) / (np.max(after_peak) + 1e-12))
            qualifies = int(tau > 0 and peak_lag > 0 and corr_lag > 0 and crash_depth > 0.35)
            print(
                f"{tau:2d} {coupling:.3f} {prey_peak:3d} {pred_peak:3d} {peak_lag:3d} "
                f"{corr_lag:3d} {corr_score:.6f} {crash_depth:.6f} {qualifies}"
            )
    print(
        "\nInterpretation key: qualifies=1 means the toy ecology exhibits a "
        "delayed numerical predator response trailing a prey boom, with a "
        "substantial post-boom prey crash."
    )


if __name__ == "__main__":
    main()
