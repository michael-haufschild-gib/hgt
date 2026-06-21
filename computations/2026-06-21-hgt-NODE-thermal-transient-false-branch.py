#!/usr/bin/env python3
"""THE-MACHINE NODE test: thermal transients mistaken for steady branches.

NODE:
    Transient regimes mistaken for steady branches.

Constraint tested:
    Near a thermally shifted saddle-node, a trajectory can pause in a ghost
    bottleneck. A short dwell/measurement window labels this plateau as a steady
    branch even though no stable equilibrium exists and a longer dwell escapes.
"""

from __future__ import annotations

import numpy as np


def simulate(mu: float, t_end: float, dt: float = 0.002, x0: float = 0.8) -> tuple[np.ndarray, np.ndarray]:
    n = int(t_end / dt) + 1
    t = np.linspace(0.0, t_end, n)
    x = np.empty(n)
    x[0] = x0
    for k in range(1, n):
        dx = mu - x[k - 1] ** 2
        x[k] = x[k - 1] + dt * dx
        if x[k] < -2.0:
            x[k:] = x[k]
            break
    return t, x


def classify_steady(t: np.ndarray, x: np.ndarray, tail_frac: float = 0.35, slope_tol: float = 0.035, span_tol: float = 0.14) -> int:
    if np.any(x < -0.45):
        return 0
    start = int((1.0 - tail_frac) * len(t))
    tt = t[start:]
    xx = x[start:]
    slope = float(np.polyfit(tt, xx, 1)[0])
    span = float(xx.max() - xx.min())
    return int(abs(slope) < slope_tol and span < span_tol)


def escape_time(t: np.ndarray, x: np.ndarray, threshold: float = -0.45) -> float:
    hits = np.flatnonzero(x < threshold)
    return float(t[hits[0]]) if hits.size else float("inf")


def main() -> None:
    print("NODE: transient regimes mistaken for steady branches under thermal forcing")
    print("normal form: dx/dt = mu(T) - x^2; true stable equilibrium exists only for mu>=0")
    print("mu true_equilibrium short_steady long_steady escape_time_short escape_time_long final_x_short final_x_long")
    false_short = 0
    for mu in [-0.080, -0.045, -0.025, -0.012, -0.006, 0.000, 0.010, 0.030, 0.080]:
        t_short, x_short = simulate(mu, 8.0)
        t_long, x_long = simulate(mu, 80.0)
        true_eq = int(mu >= 0.0)
        short = classify_steady(t_short, x_short)
        long = classify_steady(t_long, x_long)
        if short and not true_eq:
            false_short += 1
        print(
            f"{mu: .3f} {true_eq:d} {short:d} {long:d} "
            f"{escape_time(t_short, x_short):9.3f} {escape_time(t_long, x_long):9.3f} "
            f"{x_short[-1]: .6f} {x_long[-1]: .6f}"
        )
    print(f"\nfalse_short_steady_count={false_short}")
    print(
        "Interpretation: the NODE is validated if negative-mu ghost bottlenecks "
        "are classified steady in short windows but escape or fail under long "
        "dwell, while true branches occur only for mu>=0."
    )


if __name__ == "__main__":
    main()
