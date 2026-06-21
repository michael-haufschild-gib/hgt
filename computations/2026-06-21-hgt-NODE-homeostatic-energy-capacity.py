#!/usr/bin/env python3
"""NODE test: homeostatic compensation constrained by energy capacity.

NODE:
    Homeostatic responses are constrained by energy metabolism and
    mitochondrial capacity.

The model is deliberately minimal. A homeostatic gain tries to restore a
target firing/activity level after input deprivation. The gain is not free:
gain expression and firing both draw from an ATP budget. If capacity is below
the demand required to restore the target, the compensator keeps upscaling but
the actual activity remains energy-limited.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def simulate(capacity: float, limited: bool, steps: int, seed: int) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    target = 1.0
    eta = 0.035
    decay = 0.0015
    gain = 1.0
    activity = []
    raw_activity = []
    stress = []
    gains = []
    drives = np.r_[
        np.full(steps // 3, 1.0),
        np.full(steps // 3, 0.34),
        np.full(steps - 2 * (steps // 3), 1.0),
    ]
    drives = drives + rng.normal(0.0, 0.012, size=steps)
    drives = np.clip(drives, 0.05, None)

    for drive in drives:
        raw = gain * drive
        demand = 0.18 + 0.19 * gain * gain + 0.52 * raw * raw
        if limited and demand > capacity:
            actual = raw * capacity / demand
            overload = demand / capacity - 1.0
        else:
            actual = raw
            overload = 0.0
        gain += eta * (target - actual) - decay * max(0.0, gain - 1.0) - 0.003 * overload
        gain = float(np.clip(gain, 0.15, 8.0))
        activity.append(actual)
        raw_activity.append(raw)
        stress.append(overload)
        gains.append(gain)

    one = steps // 3
    two = 2 * (steps // 3)
    dep = np.asarray(activity[one:two])
    reb = np.asarray(activity[two:])
    dep_raw = np.asarray(raw_activity[one:two])
    dep_g = np.asarray(gains[one:two])
    dep_stress = np.asarray(stress[one:two])
    required_gain = target / 0.34
    required_demand = 0.18 + 0.19 * required_gain**2 + 0.52 * target**2
    return {
        "capacity": capacity,
        "limited": float(limited),
        "required_demand": required_demand,
        "deprivation_mean": float(dep.mean()),
        "deprivation_error": float(np.mean(np.abs(target - dep))),
        "raw_deprivation_mean": float(dep_raw.mean()),
        "final_deprivation_gain": float(dep_g[-1]),
        "stress_frac": float(np.mean(dep_stress > 0.0)),
        "mean_overload": float(dep_stress.mean()),
        "rebound_peak": float(np.max(reb[:80])),
        "rebound_overshoot": float(max(0.0, np.max(reb[:80]) - target)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--steps", type=int, default=900)
    args = parser.parse_args()

    capacities = [0.55, 0.85, 1.15, 1.55, 2.15, 3.10, 4.40]
    print("NODE: homeostatic plasticity constrained by energy/mitochondrial capacity")
    print("capacity limited required_demand deprivation_mean deprivation_error raw_deprivation_mean final_gain stress_frac mean_overload rebound_peak rebound_overshoot")
    for i, cap in enumerate(capacities):
        for limited in (True, False):
            out = simulate(cap, limited, args.steps, seed=20260621 + i)
            print(
                f"{out['capacity']:.2f} {int(out['limited'])} {out['required_demand']:.6f} "
                f"{out['deprivation_mean']:.6f} {out['deprivation_error']:.6f} "
                f"{out['raw_deprivation_mean']:.6f} {out['final_deprivation_gain']:.6f} "
                f"{out['stress_frac']:.6f} {out['mean_overload']:.6f} "
                f"{out['rebound_peak']:.6f} {out['rebound_overshoot']:.6f}"
            )

    print(
        "\nInterpretation key: with no ATP limit, the compensator restores the "
        "target by increasing gain. With a limit, restoration appears only once "
        "capacity approaches the required demand; below that threshold the raw "
        "homeostatic command rises while actual activity remains constrained."
    )


if __name__ == "__main__":
    main()
