#!/usr/bin/env python3
"""NODE test: noise-induced premature bursts near a crisis.

NODE:
    Noise-induced premature bursts.

Constraint:
    In a near-crisis excitable/intermittent system, bursts can occur before
    the deterministic crisis threshold because stochastic kicks cross the
    effective boundary early. The premature-burst rate should increase with
    noise and with proximity to the crisis.
"""

from __future__ import annotations

import argparse

import numpy as np


def simulate(distance: float, noise: float, reps: int, steps: int, seed: int) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    deterministic_time = int(max(0, min(steps, round(distance * steps))))
    burst_times = []
    premature = []
    for _ in range(reps):
        x = 0.0
        burst = steps
        for t in range(steps):
            ramp = t / steps
            drift = -distance + ramp
            x = 0.90 * x + 0.45 * max(0.0, drift) + rng.normal(0.0, noise)
            if x > 1.0:
                burst = t
                break
        burst_times.append(burst)
        premature.append(burst < deterministic_time)
    burst_arr = np.asarray(burst_times)
    return {
        "distance": distance,
        "noise": noise,
        "deterministic_time": float(deterministic_time),
        "burst_frac": float(np.mean(burst_arr < steps)),
        "premature_frac": float(np.mean(premature)),
        "median_burst_time": float(np.median(burst_arr)),
        "q10_burst_time": float(np.quantile(burst_arr, 0.10)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--reps", type=int, default=2400)
    parser.add_argument("--steps", type=int, default=360)
    args = parser.parse_args()

    distances = [0.30, 0.45, 0.60, 0.75]
    noises = [0.00, 0.02, 0.05, 0.09, 0.14, 0.20]
    print("NODE: noise-induced premature bursts")
    print("distance noise deterministic_time burst_frac premature_frac median_burst_time q10_burst_time")
    for i, dist in enumerate(distances):
        for j, noise in enumerate(noises):
            out = simulate(dist, noise, args.reps, args.steps, seed=20260621 + 100 * i + j)
            print(
                f"{out['distance']:.2f} {out['noise']:.2f} {out['deterministic_time']:.0f} "
                f"{out['burst_frac']:.6f} {out['premature_frac']:.6f} "
                f"{out['median_burst_time']:.6f} {out['q10_burst_time']:.6f}"
            )
    print(
        "\nInterpretation key: premature_frac should be zero at noise=0 and "
        "increase when noise can cross the burst boundary before deterministic crisis."
    )


if __name__ == "__main__":
    main()
