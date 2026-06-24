#!/usr/bin/env python3
"""NODE experiment: pre-crisis transients shadow post-crisis escape routes.

Workflow W2 selected:
  topic: basin-boundary crises in chaotic dynamical systems
  NODE: pre-crisis chaotic transients already shadow the post-crisis escape route

Toy model:
  Logistic map x -> r x (1-x). For r <= 4, [0,1] is invariant. For r > 4,
  the interval around x=1/2 whose image is >1 becomes an escape hole. The
  NODE constraint predicts that pre-crisis orbits at r<4 already make close
  approaches to the post-crisis hole, and those near-hits predict post-crisis
  escape times better than an unrelated interval of the same size.
"""

from __future__ import annotations

import argparse
import math
import random
from statistics import mean


def logistic(r: float, x: float) -> float:
    return r * x * (1.0 - x)


def escape_hole(r: float) -> tuple[float, float]:
    if r <= 4.0:
        raise ValueError("escape hole only exists for r > 4")
    root = math.sqrt(1.0 - 4.0 / r)
    return ((1.0 - root) / 2.0, (1.0 + root) / 2.0)


def dist_interval(x: float, interval: tuple[float, float]) -> float:
    lo, hi = interval
    if lo <= x <= hi:
        return 0.0
    return min(abs(x - lo), abs(x - hi))


def min_pre_distance(r_pre: float, x0: float, interval: tuple[float, float], horizon: int) -> float:
    x = x0
    best = dist_interval(x, interval)
    for _ in range(horizon):
        x = logistic(r_pre, x)
        best = min(best, dist_interval(x, interval))
    return best


def escape_time(r_post: float, x0: float, max_steps: int) -> int:
    x = x0
    for t in range(1, max_steps + 1):
        x = logistic(r_post, x)
        if not (0.0 <= x <= 1.0):
            return t
    return max_steps + 1


def ranks(xs: list[float]) -> list[float]:
    order = sorted(range(len(xs)), key=lambda i: xs[i])
    out = [0.0] * len(xs)
    i = 0
    while i < len(order):
        j = i + 1
        while j < len(order) and xs[order[j]] == xs[order[i]]:
            j += 1
        rank = 0.5 * (i + j - 1)
        for k in range(i, j):
            out[order[k]] = rank
        i = j
    return out


def pearson(xs: list[float], ys: list[float]) -> float:
    mx, my = mean(xs), mean(ys)
    vx = sum((x - mx) ** 2 for x in xs)
    vy = sum((y - my) ** 2 for y in ys)
    if vx == 0.0 or vy == 0.0:
        return 0.0
    return sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / math.sqrt(vx * vy)


def spearman(xs: list[float], ys: list[float]) -> float:
    return pearson(ranks(xs), ranks(ys))


def quantile_bins(ds: list[float], ts: list[int], bins: int) -> list[tuple[float, float, int, float, float]]:
    pairs = sorted(zip(ds, ts), key=lambda p: p[0])
    n = len(pairs)
    out = []
    for b in range(bins):
        lo = b * n // bins
        hi = (b + 1) * n // bins
        chunk = pairs[lo:hi]
        d_mean = mean(d for d, _ in chunk)
        t_vals = [t for _, t in chunk]
        out.append((chunk[0][0], chunk[-1][0], len(chunk), mean(t_vals), max(t_vals)))
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--r-pre", type=float, default=3.99)
    parser.add_argument("--r-post", type=float, default=4.01)
    parser.add_argument("--samples", type=int, default=8000)
    parser.add_argument("--burn", type=int, default=5000)
    parser.add_argument("--stride", type=int, default=7)
    parser.add_argument("--horizon", type=int, default=20)
    parser.add_argument("--max-escape", type=int, default=500)
    parser.add_argument("--seed", type=int, default=691829661222804965)
    args = parser.parse_args()

    rng = random.Random(args.seed)
    x = rng.random()
    for _ in range(args.burn):
        x = logistic(args.r_pre, x)

    samples = []
    for _ in range(args.samples):
        for _ in range(args.stride):
            x = logistic(args.r_pre, x)
        samples.append(x)

    hole = escape_hole(args.r_post)
    width = hole[1] - hole[0]
    control = (0.25 - width / 2.0, 0.25 + width / 2.0)

    d_hole = [min_pre_distance(args.r_pre, x0, hole, args.horizon) for x0 in samples]
    d_control = [min_pre_distance(args.r_pre, x0, control, args.horizon) for x0 in samples]
    t_escape = [escape_time(args.r_post, x0, args.max_escape) for x0 in samples]

    escaped = sum(1 for t in t_escape if t <= args.max_escape)
    print(f"r_pre={args.r_pre} r_post={args.r_post} samples={args.samples} horizon={args.horizon}")
    print(f"post_crisis_hole=({hole[0]:.12g},{hole[1]:.12g}) width={width:.12g}")
    print(f"control_interval=({control[0]:.12g},{control[1]:.12g})")
    print(f"escaped_within_max={escaped}/{len(t_escape)} mean_escape_time={mean(t_escape):.6g}")
    print(f"spearman_min_distance_to_hole_vs_escape={spearman(d_hole, t_escape):.6g}")
    print(f"spearman_min_distance_to_control_vs_escape={spearman(d_control, t_escape):.6g}")
    print("hole_distance_quantile_bins: min_d,max_d,count,mean_escape,max_escape")
    for row in quantile_bins(d_hole, t_escape, 8):
        print(f"{row[0]:.8g},{row[1]:.8g},{row[2]},{row[3]:.8g},{row[4]}")
    print("control_distance_quantile_bins: min_d,max_d,count,mean_escape,max_escape")
    for row in quantile_bins(d_control, t_escape, 8):
        print(f"{row[0]:.8g},{row[1]:.8g},{row[2]},{row[3]:.8g},{row[4]}")


if __name__ == "__main__":
    main()
