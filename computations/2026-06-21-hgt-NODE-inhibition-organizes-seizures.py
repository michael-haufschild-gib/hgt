#!/usr/bin/env python3
"""THE-MACHINE NODE test: inhibition can organize seizure-like bursts.

NODE:
    Inhibition can help generate or organize seizures, rather than simply
    suppressing them.

Constraint tested:
    Inhibition is not a monotone brake. In a rebound-capable excitatory system,
    moderate inhibition can synchronize release and increase burst organization,
    while weak inhibition fails to organize and strong inhibition suppresses.
"""

from __future__ import annotations

import numpy as np


def simulate(g_inh: float, n: int = 80, steps: int = 1600, seed: int = 20260621) -> tuple[np.ndarray, np.ndarray]:
    rng = np.random.default_rng(seed)
    e = 0.35 + 0.08 * rng.normal(size=n)
    r = np.zeros(n)
    activity = []
    inhibition = []
    for k in range(steps):
        drive = 0.72 + 0.08 * np.sin(2 * np.pi * k / 210.0)
        common_inh = g_inh * np.mean(e > 0.62)
        local_noise = 0.015 * rng.normal(size=n)
        release = np.maximum(0.0, r - common_inh)
        de = 0.070 * (drive - e) - 0.82 * common_inh * e + 1.10 * release + local_noise
        e = np.clip(e + de, 0.0, 1.8)
        spikes = e > 0.72
        r = 0.975 * r + 1.8 * common_inh * (e < 0.44)
        e[spikes] *= 0.34
        activity.append(float(np.mean(spikes)))
        inhibition.append(float(common_inh))
    return np.asarray(activity), np.asarray(inhibition)


def burst_metrics(activity: np.ndarray) -> tuple[float, float, float]:
    burst = activity > 0.12
    runs = []
    current = 0
    for b in burst:
        if b:
            current += 1
        elif current:
            runs.append(current)
            current = 0
    if current:
        runs.append(current)
    burst_rate = float(np.mean(burst))
    mean_run = float(np.mean(runs)) if runs else 0.0
    peak = float(np.max(activity))
    return burst_rate, mean_run, peak


def main() -> None:
    print("NODE: inhibition can organize seizure-like rebound bursts")
    print("g_inh burst_rate mean_burst_run peak_activity mean_inhibition")
    rows = []
    for g in [0.0, 0.08, 0.16, 0.28, 0.42, 0.65, 0.90, 1.30, 1.90]:
        activity, inhibition = simulate(g)
        burst_rate, mean_run, peak = burst_metrics(activity)
        rows.append((g, burst_rate, mean_run, peak))
        print(f"{g:.2f} {burst_rate:.6f} {mean_run:.6f} {peak:.6f} {np.mean(inhibition):.6f}")
    best = max(rows, key=lambda row: row[1] * row[2])
    print(f"\norganized_burst_optimum_g={best[0]:.2f}")
    print(
        "Interpretation: the NODE is validated if organized burst output is "
        "nonmonotone in inhibition strength, with moderate inhibition organizing "
        "bursts more than zero or strong inhibition."
    )


if __name__ == "__main__":
    main()
