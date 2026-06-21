#!/usr/bin/env python3
"""NODE test: inlet wall loss/chemistry biases measured radical concentrations."""

import argparse
import math

import numpy as np
from scipy.linalg import expm


SPECIES = ("OH", "HO2", "RO2", "NO3")


def inlet_matrix(wall_scale, convert_scale):
    # State order: OH, HO2, RO2, NO3.  The inlet loses radicals to walls and
    # converts some peroxy/radical reservoirs into other measured species.
    loss = np.diag([-8.0, -2.1, -1.4, -4.5]) * wall_scale
    conv = np.zeros((4, 4))
    conv[0, 1] = 1.2 * convert_scale  # HO2 -> OH artifact
    conv[1, 2] = 0.7 * convert_scale  # RO2 -> HO2 artifact
    conv[2, 3] = 0.35 * convert_scale # NO3 -> RO2-like artifact
    conv[1, 0] = 0.15 * convert_scale # OH -> HO2 after wall chemistry
    return loss + conv


def day_profile(t):
    light = max(0.0, math.sin(math.pi * t / 24.0))
    night = max(0.0, math.sin(math.pi * (t - 12.0) / 24.0))
    return np.array([
        1.00 * light**1.8 + 0.02,
        0.42 * light + 0.08,
        0.30 * light * (1.0 + 0.6 * math.sin(2.0 * math.pi * t / 24.0)) + 0.06,
        0.60 * night**2.2 + 0.01,
    ])


def measure(true, residence, wall_scale, convert_scale):
    return expm(inlet_matrix(wall_scale, convert_scale) * residence) @ true


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=97)
    args = parser.parse_args()
    ts = np.linspace(0.0, 24.0, args.samples)
    configs = [
        (0.02, 0.2, 0.0),
        (0.08, 0.2, 0.0),
        (0.20, 0.2, 0.0),
        (0.08, 0.2, 0.8),
        (0.20, 0.2, 0.8),
        (0.20, 0.6, 0.8),
    ]
    print("NODE: wall loss and inlet chemistry bias atmospheric radical measurements")
    print("columns: residence wall convert species median_ratio min_ratio max_ratio sign_flip_frac")
    for residence, wall, convert in configs:
        truth = np.array([day_profile(t) for t in ts])
        measured = np.array([measure(x, residence, wall, convert) for x in truth])
        ratio = measured / np.maximum(truth, 1e-12)
        for i, name in enumerate(SPECIES):
            sign_flip = float(np.mean((measured[:, i] - truth[:, i]) * (truth[:, i] - np.median(truth[:, i])) < 0.0))
            print(
                f"residence={residence:.2f} wall={wall:.2f} convert={convert:.2f} {name:3s} "
                f"median_ratio={np.median(ratio[:,i]):.4f} min_ratio={np.min(ratio[:,i]):.4f} "
                f"max_ratio={np.max(ratio[:,i]):.4f} sign_flip_frac={sign_flip:.3f}"
            )
        err = np.linalg.norm(measured - truth) / max(np.linalg.norm(truth), 1e-12)
        rank_cond = np.linalg.cond(expm(inlet_matrix(wall, convert) * residence))
        print(f"summary residence={residence:.2f} wall={wall:.2f} convert={convert:.2f} relative_error={err:.4f} inlet_condition={rank_cond:.4f}")

    print("\nInterpretation: the instrument reports exp(A*tau) applied to ambient radicals, not the ambient state itself.")


if __name__ == "__main__":
    main()
