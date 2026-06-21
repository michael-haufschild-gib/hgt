#!/usr/bin/env python3
"""THE-MACHINE NODE test.

NODE: catalytic specificity is crucial; broad/promiscuous catalysis can make a
hypercycle vulnerable to parasites.

Method #16: minimal counterexample. Three cooperating templates plus one
parasite is enough.
"""

import numpy as np


def simulate(leak=0.0, parasite_seed=1e-4, steps=18000, dt=0.002):
    # Three cooperators x0,x1,x2; parasite y exploits catalysis but gives none.
    x = np.array([0.33, 0.33, 0.33, parasite_seed], dtype=float)
    x /= x.sum()
    rates = np.array([1.0, 1.0, 1.0, 2.8])
    decay = 0.03
    min_coop = 1.0
    peak_par = x[3]
    for _ in range(steps):
        catalysts = np.zeros(4)
        # Specific hypercycle: i is catalyzed by previous cooperator.
        catalysts[0] = x[2]
        catalysts[1] = x[0]
        catalysts[2] = x[1]
        # Parasite receives leaked/promiscuous support from all cooperators.
        catalysts[3] = leak * (x[0] + x[1] + x[2])
        growth = rates * x * catalysts
        dx = growth - decay * x
        x = np.maximum(0.0, x + dt * dx)
        total = x.sum()
        if total > 0:
            x /= total
        min_coop = min(min_coop, float(np.min(x[:3])))
        peak_par = max(peak_par, float(x[3]))
    return x, min_coop, peak_par


def main():
    print("NODE hypercycle catalytic specificity minimal counterexample")
    print("leak final_coop_sum final_parasite min_coop peak_parasite verdict")
    for leak in [0.0, 0.02, 0.04, 0.06, 0.08, 0.10, 0.14, 0.18, 0.24, 0.32, 0.45, 0.60]:
        x, min_coop, peak_par = simulate(leak=leak)
        verdict = "collapse" if x[3] > 0.5 or x[:3].sum() < 0.5 else "cycle"
        print(f"{leak:5.2f} {x[:3].sum():14.6f} {x[3]:14.6f} {min_coop:9.6f} {peak_par:13.6f} {verdict}")
    print("\nminimal counterexample: leak=0.00 preserves cooperation; sufficient broad leakage lets a tiny parasite dominate.")


if __name__ == "__main__":
    main()
