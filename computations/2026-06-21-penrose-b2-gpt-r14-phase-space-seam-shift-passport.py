#!/usr/bin/env python3
import numpy as np


def gap(x, y, env_shift=0.0, damping=1.0):
    return 2.0 * damping * np.sqrt((x - env_shift) ** 2 + y * y)


def min_gap_location(env_shift, damping=1.0):
    xs = np.linspace(-1.0, 1.0, 4001)
    vals = gap(xs, 0.0, env_shift=env_shift, damping=damping)
    return float(xs[np.argmin(vals)]), float(np.min(vals))


def main():
    print("NODE test: environment can shift a conical-intersection seam, not merely damp dynamics")
    print("Model gap=2*damping*sqrt((x-shift)^2+y^2).")
    print()
    print("env shift | true min x | damping-only min x | location error")
    print("----------|------------|--------------------|---------------")
    for shift in [-0.40, -0.15, 0.0, 0.25, 0.55]:
        true_x, _ = min_gap_location(shift, damping=1.0)
        damp_x, _ = min_gap_location(0.0, damping=0.5)
        print(f"{shift:9.2f} | {true_x:10.3f} | {damp_x:18.3f} | {abs(true_x-damp_x):13.3f}")
    print()
    print("Step-12 follow-up: damping sweep at fixed shifted seam x=0.35")
    print("damping | min x | min gap")
    print("--------|-------|--------")
    for damping in [1.0, 0.7, 0.4, 0.1]:
        x_min, gap_min = min_gap_location(0.35, damping=damping)
        print(f"{damping:7.2f} | {x_min:5.3f} | {gap_min:7.3e}")
    print()
    print("ResearchNode mutation: finite-prime phase as wrong momentum coordinate")
    print("Assume canonical momentum p_true = p_prime + k*(sigma-1/2).")
    print()
    k = 3.0
    print("sigma | required momentum shift | residual if p_prime used")
    print("------|-------------------------|-------------------------")
    for sigma in [0.50, 0.55, 0.65, 0.80, 1.00]:
        shift = k * (sigma - 0.5)
        print(f"{sigma:5.2f} | {shift:23.6f} | {abs(shift):23.6f}")
    print()
    print("Finding:")
    print("  The nearby false statement is 'environment only damps'. The seam-shift model")
    print("  separates damping from coordinate displacement. A phase-space lift needs a")
    print("  seam/momentum-shift passport across sigma lanes; otherwise finite-prime phase")
    print("  can be the wrong momentum coordinate even when its amplitude trend looks useful.")


if __name__ == "__main__":
    main()
