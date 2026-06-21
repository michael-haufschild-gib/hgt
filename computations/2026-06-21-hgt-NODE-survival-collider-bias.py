#!/usr/bin/env python3
"""NODE test: hidden collider bias introduced by conditioning on survival."""

import argparse

import numpy as np


def sigmoid(x):
    return 1.0 / (1.0 + np.exp(-x))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=200000)
    parser.add_argument("--seed", type=int, default=20260621)
    args = parser.parse_args()
    rng = np.random.default_rng(args.seed)

    x = rng.normal(size=args.n)
    y = rng.normal(size=args.n)
    z = rng.normal(size=args.n)
    print("NODE: hidden collider bias from conditioning on survival")
    print("x and y are independent in the source population; survival depends on both.")
    print("columns: rule survival_frac corr_source corr_survivor mean_x_survivor mean_y_survivor")
    rules = [
        ("linear_x_plus_y", -0.25 + 1.10 * x + 1.10 * y),
        ("substitution_x_or_y", -0.65 + 1.75 * np.maximum(x, y)),
        ("opposition_x_minus_y", -0.25 + 1.35 * x - 1.35 * y),
        ("x_only_control", -0.25 + 1.60 * x),
        ("z_only_control", -0.25 + 1.60 * z),
    ]
    src_corr = float(np.corrcoef(x, y)[0, 1])
    for name, score in rules:
        p = sigmoid(score)
        survived = rng.random(args.n) < p
        xs = x[survived]
        ys = y[survived]
        corr = float(np.corrcoef(xs, ys)[0, 1]) if len(xs) > 2 else float("nan")
        print(
            f"rule={name:18s} survival_frac={float(np.mean(survived)):.5f} "
            f"corr_source={src_corr:+.5f} corr_survivor={corr:+.5f} "
            f"mean_x_survivor={float(np.mean(xs)):+.5f} mean_y_survivor={float(np.mean(ys)):+.5f}"
        )

    print("\nStrength sweep for linear_x_plus_y collider")
    for strength in [0.0, 0.4, 0.8, 1.2, 1.8, 2.4]:
        p = sigmoid(-0.25 + strength * x + strength * y)
        survived = rng.random(args.n) < p
        corr = float(np.corrcoef(x[survived], y[survived])[0, 1])
        print(
            f"strength={strength:.1f} survival_frac={float(np.mean(survived)):.5f} "
            f"corr_survivor={corr:+.5f}"
        )


if __name__ == "__main__":
    main()
