#!/usr/bin/env python3
import numpy as np


def solve_profile(bulk, damkohler, n=180):
    # Steady 1D diffusion to a consuming interface at x=0, fixed bulk at x=1.
    # Boundary: -dc/dx = Da * c/(1+c) at interface.
    x = np.linspace(0.0, 1.0, n)
    c0 = bulk
    for _ in range(80):
        # linear profile for a guessed interface concentration
        c = c0 + (bulk - c0) * x
        flux = bulk - c0
        reaction = damkohler * c0 / (1.0 + c0)
        # Newton step on flux - reaction = 0
        f = flux - reaction
        df = -1.0 - damkohler / ((1.0 + c0) ** 2)
        c0 = max(0.0, c0 - f / df)
    c = c0 + (bulk - c0) * x
    return c0, c, damkohler * c0 / (1.0 + c0)


def main():
    print("NODE: interface supersaturation differs from measured bulk under depletion")
    print("bulk Da interface_c interface_to_bulk growth_rate depletion_gap")
    for bulk in [0.2, 0.5, 1.0, 2.0]:
        for da in [0.05, 0.25, 1.0, 4.0, 12.0]:
            c0, _, rate = solve_profile(bulk, da)
            print(f"{bulk:.2f} {da:5.2f} {c0:.6f} {c0/bulk:.6f} {rate:.6f} {bulk-c0:.6f}")


if __name__ == "__main__":
    main()
