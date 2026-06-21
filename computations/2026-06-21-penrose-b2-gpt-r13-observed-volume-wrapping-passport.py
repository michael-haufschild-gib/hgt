#!/usr/bin/env python3
import math
import numpy as np


def cov(x, y):
    x = np.asarray(x, dtype=float)
    y = np.asarray(y, dtype=float)
    return float(np.mean((x - x.mean()) * (y - y.mean())))


def main():
    print("NODE test: Aharonov-Bohm phase is periodic in flux with period one flux quantum")
    print("flux | phase mod 2pi | fringe cos(phase)")
    print("-----|---------------|------------------")
    for flux in [0.0, 0.25, 0.5, 0.75, 1.0, 1.25, 2.0]:
        phase = (2 * math.pi * flux) % (2 * math.pi)
        print(f"{flux:4.2f} | {phase:13.6f} | {math.cos(phase):16.6f}")
    print()
    print("ResearchNode mutation: observed-volume covariance under periodic wrapping")
    print("t is trajectory order, volume=t*slope, observed volume is volume mod 1.")
    print()
    t = np.arange(40)
    print("slope | cov(t, true volume) | cov(t, wrapped volume) | cov(t, winding lift)")
    print("------|---------------------|------------------------|---------------------")
    for slope in [0.10, 0.25, 0.50, 0.75, 1.00, math.sqrt(2) / 5]:
        volume = slope * t
        wrapped = volume % 1.0
        winding = np.floor(volume)
        print(
            f"{slope:5.3f} | {cov(t, volume):19.6f} | "
            f"{cov(t, wrapped):22.6f} | {cov(t, winding):19.6f}"
        )
    print()
    print("Step-12 follow-up: boundary cases")
    print("  integer-slope wrapping makes observed covariance vanish while true covariance is large;")
    print("  irrational-ish slopes avoid exact lock-in but still show quotient distortion.")
    print()
    print("Finding:")
    print("  Observed-volume covariance needs a wrapping/lift passport. If the observed variable")
    print("  is periodic or quotient-valued, covariance on the wrapped representative can be a")
    print("  trajectory-order artifact. A monotone unwrapped lift or winding count must accompany")
    print("  any claim that the covariance is a genuine measure invariant.")


if __name__ == "__main__":
    main()
