#!/usr/bin/env python3
import numpy as np


def regular(t):
    return t


def mixed(t):
    width = 0.02
    amp = 0.08
    return t + amp * (np.tanh((t - 0.25) / width) + np.tanh((t + 0.25) / width))


def diagnostics(name, values, t):
    dt = t[1] - t[0]
    d1 = np.gradient(values, dt)
    d2 = np.gradient(d1, dt)
    zero_idx = int(np.argmin(np.abs(t)))
    return {
        "name": name,
        "value_at_0": float(values[zero_idx]),
        "slope_at_0": float(d1[zero_idx]),
        "tv_derivative": float(np.sum(np.abs(d2)) * dt),
        "max_abs_curvature": float(np.max(np.abs(d2))),
    }


def main():
    print("NODE test: hysteresis has reversible and irreversible components")
    print("ResearchNode mutation: soft Delta=0 crossing needs decomposition, not only local smoothness")
    print()
    t = np.linspace(-1.0, 1.0, 20001)
    rows = [diagnostics("regular crossing", regular(t), t), diagnostics("mixed hidden-switch crossing", mixed(t), t)]
    print("signal | value at 0 | slope at 0 | TV(derivative) | max |curvature|")
    print("-------|------------|------------|----------------|----------------")
    for row in rows:
        print(
            f"{row['name']:27s} | {row['value_at_0']:10.3e} | {row['slope_at_0']:10.6f} | "
            f"{row['tv_derivative']:14.6f} | {row['max_abs_curvature']:14.3f}"
        )
    print()
    print("Finding:")
    print("  Two signals can have the same soft local zero crossing while one contains hidden")
    print("  switch-like components away from the crossing. A transition-softness claim needs")
    print("  a reversible/irreversible decomposition or a regularity functional controlling")
    print("  derivative variation across the lane, not just Delta=0 local smoothness.")


if __name__ == "__main__":
    main()
