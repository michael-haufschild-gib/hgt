#!/usr/bin/env python3
import numpy as np


def simulate(active=True, steps=180):
    biomass = 0.15
    nutrient = 1.0
    detached = []
    rng = np.random.default_rng(20260621 + int(active))
    for t in range(steps):
        nutrient = 0.92 * nutrient + 0.10
        growth = 0.10 * biomass * nutrient / (0.2 + nutrient) * (1.0 - biomass)
        stress = max(0.0, biomass - nutrient)
        if active:
            det = biomass * (0.002 + 0.34 / (1.0 + np.exp(-16.0 * (stress - 0.22))))
        else:
            det = biomass * (0.025 + 0.01 * rng.random())
        biomass = max(0.0, min(1.0, biomass + growth - det))
        nutrient -= 0.25 * biomass
        detached.append(det)
    arr = np.array(detached)
    return {
        "final_biomass": float(biomass),
        "total_detached": float(arr.sum()),
        "burst_frac": float(np.mean(arr > np.quantile(arr, 0.9))),
        "detachment_cv": float(arr.std() / (arr.mean() + 1e-12)),
        "late_detach_frac": float(arr[steps // 2 :].sum() / (arr.sum() + 1e-12)),
    }


def main():
    print("NODE: biofilm detachment is active life-history process, not accidental sloughing")
    print("case final_biomass total_detached burst_frac detachment_cv late_detach_frac")
    for label, active in [("passive_slough", False), ("active_detach", True)]:
        row = simulate(active)
        print(
            f"{label:14s} {row['final_biomass']:.6f} {row['total_detached']:.6f} "
            f"{row['burst_frac']:.6f} {row['detachment_cv']:.6f} {row['late_detach_frac']:.6f}"
        )


if __name__ == "__main__":
    main()
