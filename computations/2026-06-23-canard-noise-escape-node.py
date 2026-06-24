#!/usr/bin/env python3
"""NODE experiment: noise-induced premature escape from a repelling slow manifold.

Workflow W3 selected:
  topic: canard explosions in slow-fast biochemical oscillators
  NODE: noise-induced premature escape from repelling slow manifolds

Canonical normal model:
  dy/dt = eps
  dX = y X dt + sigma dW_t

The slow manifold X=0 changes from attracting (y<0) to repelling (y>0).
Without noise and with X(0)=0 it is invariant. With noise, trajectories escape
once |X| crosses a threshold. A crude accumulated-repulsion estimate gives

  y_escape ~ sqrt(2 eps log(threshold / sigma))

for the post-fold repelling segment, so increasing sigma should move escape
earlier along the slow coordinate y.
"""

from __future__ import annotations

import argparse
import math
import random
from statistics import mean, median


def simulate_path(
    sigma: float,
    eps: float,
    dt: float,
    y0: float,
    y_max: float,
    threshold: float,
    rng: random.Random,
) -> float:
    x = 0.0
    y = y0
    sqrt_dt = math.sqrt(dt)
    while y < y_max:
        x += y * x * dt + sigma * sqrt_dt * rng.gauss(0.0, 1.0)
        y += eps * dt
        if abs(x) >= threshold:
            return y
    return y_max


def quantiles(xs: list[float]) -> tuple[float, float, float, float, float]:
    ys = sorted(xs)
    n = len(ys)
    def q(p: float) -> float:
        return ys[min(n - 1, max(0, round(p * (n - 1))))]
    return q(0.05), q(0.25), q(0.50), q(0.75), q(0.95)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--trials", type=int, default=2000)
    parser.add_argument("--eps", type=float, default=0.01)
    parser.add_argument("--dt", type=float, default=0.02)
    parser.add_argument("--y0", type=float, default=-0.7)
    parser.add_argument("--y-max", type=float, default=1.2)
    parser.add_argument("--threshold", type=float, default=0.15)
    parser.add_argument("--seed", type=int, default=2735874861708935950)
    args = parser.parse_args()

    sigmas = [1e-4, 3e-4, 1e-3, 3e-3, 1e-2, 3e-2]
    print("sigma,mean_escape_y,median_escape_y,q05,q25,q50,q75,q95,predicted_y")
    for idx, sigma in enumerate(sigmas):
        rng = random.Random(args.seed + 7919 * idx)
        escapes = [
            simulate_path(sigma, args.eps, args.dt, args.y0, args.y_max, args.threshold, rng)
            for _ in range(args.trials)
        ]
        q05, q25, q50, q75, q95 = quantiles(escapes)
        if sigma < args.threshold:
            predicted = math.sqrt(max(0.0, 2.0 * args.eps * math.log(args.threshold / sigma)))
        else:
            predicted = 0.0
        print(
            f"{sigma:.8g},{mean(escapes):.8g},{median(escapes):.8g},"
            f"{q05:.8g},{q25:.8g},{q50:.8g},{q75:.8g},{q95:.8g},{predicted:.8g}"
        )


if __name__ == "__main__":
    main()
