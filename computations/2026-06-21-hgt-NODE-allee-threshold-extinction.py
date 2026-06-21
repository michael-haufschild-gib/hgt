#!/usr/bin/env python3
"""THE-MACHINE NODE test: Allee thresholds make extinction risk cliff-like.

NODE:
    The effect of Allee thresholds on making extinction risk discontinuous or
    sharply nonlinear.

Constraint tested:
    With a strong Allee term, low abundance is not just "less growth"; it is on
    the wrong side of an attracting/absorbing boundary. Small changes in initial
    abundance or threshold location can therefore create large changes in
    finite-horizon extinction risk.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass

import numpy as np


@dataclass(frozen=True)
class Result:
    extinct_frac: float
    median_extinction_time: float
    q10_extinction_time: float
    final_median: float
    final_q90: float


def simulate(
    *,
    reps: int,
    steps: int,
    initial: float,
    allee: bool,
    threshold: float,
    carrying: float,
    growth_rate: float,
    env_sigma: float,
    demo_sigma: float,
    seed: int,
) -> Result:
    rng = np.random.default_rng(seed)
    n = np.full(reps, float(initial))
    extinct = np.zeros(reps, dtype=bool)
    t_ext = np.full(reps, np.nan)

    for t in range(1, steps + 1):
        alive = ~extinct
        if not np.any(alive):
            break
        x = n[alive]
        if allee:
            drift = growth_rate * x * (1.0 - x / carrying) * (x / threshold - 1.0)
        else:
            drift = growth_rate * x * (1.0 - x / carrying)
        env = env_sigma * x * rng.normal(size=x.size)
        demo = demo_sigma * np.sqrt(np.maximum(x, 0.0)) * rng.normal(size=x.size)
        x_next = x + drift + env + demo
        x_next = np.clip(x_next, 0.0, 4.0 * carrying)
        died_local = x_next < 1.0

        alive_idx = np.flatnonzero(alive)
        died_idx = alive_idx[died_local]
        extinct[died_idx] = True
        t_ext[died_idx] = t
        x_next[died_local] = 0.0
        n[alive_idx] = x_next

    extinct_times = t_ext[extinct]
    if extinct_times.size:
        median_ext = float(np.median(extinct_times))
        q10_ext = float(np.quantile(extinct_times, 0.10))
    else:
        median_ext = float("inf")
        q10_ext = float("inf")
    return Result(
        extinct_frac=float(np.mean(extinct)),
        median_extinction_time=median_ext,
        q10_extinction_time=q10_ext,
        final_median=float(np.median(n)),
        final_q90=float(np.quantile(n, 0.90)),
    )


def cliff_slope(values: list[float]) -> float:
    return max(abs(b - a) for a, b in zip(values, values[1:])) if len(values) > 1 else 0.0


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--reps", type=int, default=7000)
    parser.add_argument("--steps", type=int, default=160)
    args = parser.parse_args()

    base = dict(
        reps=args.reps,
        steps=args.steps,
        threshold=30.0,
        carrying=120.0,
        growth_rate=0.26,
        env_sigma=0.055,
        demo_sigma=1.30,
    )
    print("NODE: Allee threshold extinction-risk cliff")
    print(f"reps={args.reps} steps={args.steps}")
    print("\nInitial-abundance sweep; same mean growth scale, with vs without Allee threshold")
    print("initial allee_extinct noallee_extinct allee_med_t noallee_med_t allee_final_median noallee_final_median")
    allee_ext = []
    noallee_ext = []
    for i, initial in enumerate([18, 22, 25, 27, 29, 30, 31, 33, 36, 42]):
        a = simulate(initial=initial, allee=True, seed=1000 + i, **base)
        b = simulate(initial=initial, allee=False, seed=2000 + i, **base)
        allee_ext.append(a.extinct_frac)
        noallee_ext.append(b.extinct_frac)
        print(
            f"{initial:7.1f} {a.extinct_frac:13.5f} {b.extinct_frac:15.5f} "
            f"{a.median_extinction_time:11.3g} {b.median_extinction_time:13.3g} "
            f"{a.final_median:18.5f} {b.final_median:21.5f}"
        )
    print(f"max_adjacent_extinction_jump_allee={cliff_slope(allee_ext):.5f}")
    print(f"max_adjacent_extinction_jump_noallee={cliff_slope(noallee_ext):.5f}")

    print("\nThreshold-location sweep at fixed initial abundance")
    print("threshold extinct_frac median_extinction_time final_median")
    threshold_ext = []
    for j, threshold in enumerate([22, 25, 28, 30, 32, 34, 36, 38]):
        res = simulate(initial=32.0, allee=True, seed=3000 + j, **{**base, "threshold": float(threshold)})
        threshold_ext.append(res.extinct_frac)
        print(
            f"{threshold:9.1f} {res.extinct_frac:12.5f} "
            f"{res.median_extinction_time:22.3g} {res.final_median:13.5f}"
        )
    print(f"max_adjacent_threshold_jump={cliff_slope(threshold_ext):.5f}")

    print("\nNoise-strength boundary cases")
    print("env_sigma extinct_below_A extinct_at_A extinct_above_A cliff_jump")
    for k, env_sigma in enumerate([0.0, 0.025, 0.055, 0.10]):
        vals = []
        for initial in [27.0, 30.0, 33.0]:
            res = simulate(
                initial=initial,
                allee=True,
                seed=4000 + 10 * k + int(initial),
                **{**base, "env_sigma": env_sigma},
            )
            vals.append(res.extinct_frac)
        print(f"{env_sigma:9.3f} {vals[0]:15.5f} {vals[1]:12.5f} {vals[2]:14.5f} {cliff_slope(vals):10.5f}")

    print(
        "\nInterpretation: the constraint is validated if the Allee model has a much sharper "
        "adjacent extinction-risk jump than the no-Allee control, and if moving the "
        "threshold across the same initial abundance flips risk."
    )


if __name__ == "__main__":
    main()
