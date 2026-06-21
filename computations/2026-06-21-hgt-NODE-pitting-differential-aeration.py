#!/usr/bin/env python3
import math

import numpy as np


def pit_profile(depth, mouth, consumption, n=140):
    x = np.linspace(0.0, depth, n)
    # oxygen supplied at mouth x=0, consumed toward occluded bottom x=depth
    length_scale = max(1e-9, math.sqrt(mouth / (consumption + 1e-12)))
    oxygen = np.exp(-x / length_scale)
    bottom = float(oxygen[-1])
    # Nernst-like differential aeration potential, arbitrary units
    potential = math.log((oxygen[0] + 1e-12) / (bottom + 1e-12))
    return bottom, potential


def main():
    print("NODE: oxygen depletion in pits creates differential aeration cell")
    print("depth mouth consumption bottom_oxygen potential driving_class")
    for depth in [0.5, 1.0, 2.0, 4.0]:
        for mouth in [0.25, 1.0, 4.0]:
            for consumption in [0.1, 0.5, 2.0]:
                bottom, pot = pit_profile(depth, mouth, consumption)
                cls = "weak" if pot < 1.0 else "moderate" if pot < 3.0 else "strong"
                print(f"{depth:.1f} {mouth:.2f} {consumption:.2f} {bottom:.6f} {pot:.6f} {cls}")


if __name__ == "__main__":
    main()
