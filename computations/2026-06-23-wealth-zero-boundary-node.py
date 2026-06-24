#!/usr/bin/env python3
"""NODE experiment: zero-wealth absorbing boundary in wealth condensation.

This follows logs/experiments/workflow-general.md: test the random NODE on its own
before any transfer. The model is a yard-sale exchange process where the stake is a
fraction of the poorer agent's wealth. At exact zero, an agent cannot stake and the
boundary is absorbing unless a rule explicitly injects/recycles wealth.
"""

from __future__ import annotations

import argparse
import random
from dataclasses import dataclass


@dataclass
class Metrics:
    variant: str
    beta: float
    redistribution: float
    floor: float
    zero_revival_trials: int
    zero_revivals: int
    near_zero_frac: float
    max_share: float
    gini: float
    bottom_half_share: float


def gini(xs: list[float]) -> float:
    n = len(xs)
    total = sum(xs)
    if total <= 0:
        return 0.0
    ys = sorted(xs)
    weighted = sum((i + 1) * x for i, x in enumerate(ys))
    return (2 * weighted) / (n * total) - (n + 1) / n


def step_yard_sale(
    w: list[float],
    beta: float,
    rng: random.Random,
    redistribution: float,
    floor: float,
) -> None:
    n = len(w)
    i = rng.randrange(n)
    j = rng.randrange(n - 1)
    if j >= i:
        j += 1

    stake = beta * min(w[i], w[j])
    if stake > 0.0:
        if rng.random() < 0.5:
            w[i] += stake
            w[j] -= stake
        else:
            w[i] -= stake
            w[j] += stake

    if floor > 0.0:
        # A minimal welfare/floor rule: agents below floor are topped up by a
        # proportional levy from agents above average. This makes zero nonabsorbing.
        deficit = 0.0
        for k, x in enumerate(w):
            if x < floor:
                deficit += floor - x
                w[k] = floor
        if deficit > 0.0:
            rich = [k for k, x in enumerate(w) if x > 1.0]
            rich_total = sum(w[k] - 1.0 for k in rich)
            if rich_total > 0.0:
                for k in rich:
                    w[k] -= deficit * ((w[k] - 1.0) / rich_total)

    if redistribution > 0.0:
        # Flat tax toward the conserved mean wealth 1. This also makes zero nonabsorbing.
        for k, x in enumerate(w):
            w[k] = (1.0 - redistribution) * x + redistribution


def run_variant(
    variant: str,
    n: int,
    steps: int,
    beta: float,
    redistribution: float,
    floor: float,
    seed: int,
) -> Metrics:
    rng = random.Random(seed)
    w = [1.0] * n
    # Seed a small exactly-zero population to test whether the boundary is absorbing.
    zero_trials = max(1, n // 50)
    for k in range(zero_trials):
        w[k] = 0.0
    # Keep total wealth normalized by spreading removed wealth over the rest.
    bump = zero_trials / (n - zero_trials)
    for k in range(zero_trials, n):
        w[k] += bump

    for _ in range(steps):
        step_yard_sale(w, beta, rng, redistribution, floor)

    zero_revivals = sum(1 for x in w[:zero_trials] if x > 1e-12)
    total = sum(w)
    w_sorted = sorted(w)
    return Metrics(
        variant=variant,
        beta=beta,
        redistribution=redistribution,
        floor=floor,
        zero_revival_trials=zero_trials,
        zero_revivals=zero_revivals,
        near_zero_frac=sum(1 for x in w if x < 1e-6) / n,
        max_share=max(w) / total,
        gini=gini(w),
        bottom_half_share=sum(w_sorted[: n // 2]) / total,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=1200)
    parser.add_argument("--steps", type=int, default=300_000)
    parser.add_argument("--seed", type=int, default=3845766000613800379)
    parser.add_argument("--extremes", action="store_true")
    args = parser.parse_args()

    if args.extremes:
        configs = [
            ("absorbing_no_exchange", 0.0, 0.0, 0.0),
            ("absorbing_aggressive_exchange", 0.8, 0.0, 0.0),
            ("floor_1e-2", 0.2, 0.0, 1e-2),
            ("redistribution_1e-2", 0.2, 1e-2, 0.0),
        ]
    else:
        configs = [
            ("absorbing", 0.2, 0.0, 0.0),
            ("tiny_floor", 0.2, 0.0, 1e-4),
            ("redistribution_1e-4", 0.2, 1e-4, 0.0),
            ("redistribution_1e-3", 0.2, 1e-3, 0.0),
        ]
    print("variant,beta,redistribution,floor,zero_revivals/trials,near_zero_frac,max_share,gini,bottom_half_share")
    for idx, (name, beta, redistribution, floor) in enumerate(configs):
        m = run_variant(
            name,
            n=args.n,
            steps=args.steps,
            beta=beta,
            redistribution=redistribution,
            floor=floor,
            seed=args.seed + idx * 1009,
        )
        print(
            f"{m.variant},{m.beta:.6g},{m.redistribution:.6g},{m.floor:.6g},"
            f"{m.zero_revivals}/{m.zero_revival_trials},"
            f"{m.near_zero_frac:.6g},{m.max_share:.6g},{m.gini:.6g},{m.bottom_half_share:.6g}"
        )


if __name__ == "__main__":
    main()
