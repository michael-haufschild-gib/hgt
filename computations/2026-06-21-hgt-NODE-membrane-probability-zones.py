#!/usr/bin/env python3
import numpy as np


def simulate(dynamic=True, particles=900, steps=700, dt=0.04):
    rng = np.random.default_rng(20260621 + int(dynamic))
    x = rng.uniform(-3.0, 3.0, size=particles)
    occupancies = []
    boundary_cross = []
    for k in range(steps):
        t = k * dt
        center = 1.25 * np.sin(0.45 * t) if dynamic else 0.0
        width = 0.85 + (0.40 * np.sin(0.31 * t + 1.0) if dynamic else 0.0)
        # soft probability zone: attractive drift toward a moving, breathing domain
        drift = -0.55 * (x - center) * np.exp(-0.5 * ((x - center) / width) ** 2)
        x += drift * dt + rng.normal(0.0, np.sqrt(2 * 0.13 * dt), size=particles)
        x = np.clip(x, -3.5, 3.5)
        p_zone = 1.0 / (1.0 + np.exp((np.abs(x - center) - width) / 0.24))
        hard = np.abs(x) < 0.85
        occupancies.append([float(np.mean(p_zone)), float(np.mean(hard)), float(np.mean((p_zone > 0.25) & (p_zone < 0.75)))])
        if k > 0:
            boundary_cross.append(float(np.mean(hard != prev_hard)))
        prev_hard = hard
    arr = np.array(occupancies)
    return {
        "soft_occ_mean": float(arr[:, 0].mean()),
        "soft_occ_std": float(arr[:, 0].std()),
        "hard_occ_mean": float(arr[:, 1].mean()),
        "hard_occ_std": float(arr[:, 1].std()),
        "fuzzy_boundary_mean": float(arr[:, 2].mean()),
        "hard_crossing_mean": float(np.mean(boundary_cross)),
    }


def main():
    print("NODE: membrane compartments as dynamic probability zones, not fixed boxes")
    print("case soft_occ_mean soft_occ_std hard_occ_mean hard_occ_std fuzzy_boundary_mean hard_crossing_mean")
    for label, dynamic in [("fixed_box", False), ("dynamic_soft_zone", True)]:
        row = simulate(dynamic)
        print(
            f"{label:17s} {row['soft_occ_mean']:.6f} {row['soft_occ_std']:.6f} "
            f"{row['hard_occ_mean']:.6f} {row['hard_occ_std']:.6f} "
            f"{row['fuzzy_boundary_mean']:.6f} {row['hard_crossing_mean']:.6f}"
        )


if __name__ == "__main__":
    main()
