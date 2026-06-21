#!/usr/bin/env python3
"""THE-MACHINE NODE test: repeated small boundary exceptions.

NODE:
    Repeated small exceptions usually matter more than one dramatic violation.

Constraint tested:
    A boundary is not only an event-size threshold. It also has a precedent
    state: unenforced small exceptions accumulate and alter future access
    expectations. A single dramatic violation is easier to identify and can
    trigger immediate consequence/reset, while small exceptions can stay below
    the enforcement trigger until the boundary is already eroded.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass

import numpy as np


@dataclass(frozen=True)
class Summary:
    collapse_frac: float
    mean_collapse_step: float
    mean_final_debt: float
    mean_max_debt: float
    mean_access_expectation: float
    mean_consequences: float


def sigmoid(x: np.ndarray) -> np.ndarray:
    return 1.0 / (1.0 + np.exp(-x))


def simulate_sequence(
    events: list[float],
    *,
    reps: int,
    seed: int,
    individual_trigger: float = 0.72,
    cumulative_trigger: float = 1.05,
    decay: float = 0.94,
    enforcement_slope: float = 14.0,
    ambiguity: float = 0.42,
    reset_factor: float = 0.18,
) -> Summary:
    rng = np.random.default_rng(seed)
    debt = np.zeros(reps, dtype=float)
    max_debt = np.zeros(reps, dtype=float)
    access = np.zeros(reps, dtype=float)
    collapsed = np.zeros(reps, dtype=bool)
    collapse_step = np.full(reps, np.nan)
    consequences = np.zeros(reps, dtype=float)

    # Trial-level heterogeneity: some relationships/institutions tolerate more
    # ambiguity before enforcement becomes socially cheap.
    trigger_jitter = rng.normal(0.0, 0.045, size=reps)
    cumulative_jitter = rng.normal(0.0, 0.06, size=reps)

    for step, severity in enumerate(events, 1):
        visible = severity + ambiguity * debt
        p_enforce = sigmoid(enforcement_slope * (visible - individual_trigger - trigger_jitter))
        enforced = rng.random(reps) < p_enforce
        consequences += enforced

        # Enforced large violations produce a consequence and reset precedent.
        debt = np.where(enforced, reset_factor * debt, decay * debt + severity)
        access = np.where(enforced, 0.55 * access, access + severity * (1.0 + debt))
        max_debt = np.maximum(max_debt, debt)

        now_collapsed = (~collapsed) & (debt > cumulative_trigger + cumulative_jitter)
        collapse_step[now_collapsed] = step
        collapsed |= now_collapsed

    return Summary(
        collapse_frac=float(np.mean(collapsed)),
        mean_collapse_step=float(np.nanmean(collapse_step)) if np.any(collapsed) else float("inf"),
        mean_final_debt=float(np.mean(debt)),
        mean_max_debt=float(np.mean(max_debt)),
        mean_access_expectation=float(np.mean(access)),
        mean_consequences=float(np.mean(consequences)),
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--reps", type=int, default=12000)
    args = parser.parse_args()

    sequences = {
        "one_dramatic_1x1.0": [1.0],
        "five_medium_5x0.2": [0.2] * 5,
        "twenty_small_20x0.05": [0.05] * 20,
        "forty_tiny_40x0.025": [0.025] * 40,
        "two_dramatic_repaired": [0.85, 0.85],
        "mixed_small_then_large": [0.05] * 14 + [0.50],
    }

    print("NODE: repeated small boundary exceptions versus one dramatic violation")
    print(f"reps={args.reps}")
    print("sequence total_severity collapse_frac mean_collapse_step final_debt max_debt access_expectation consequences")
    for i, (name, events) in enumerate(sequences.items()):
        row = simulate_sequence(events, reps=args.reps, seed=20260621 + i)
        print(
            f"{name:24s} {sum(events):14.3f} {row.collapse_frac:13.5f} "
            f"{row.mean_collapse_step:18.3f} {row.mean_final_debt:10.5f} "
            f"{row.mean_max_debt:8.5f} {row.mean_access_expectation:18.5f} "
            f"{row.mean_consequences:12.5f}"
        )

    print("\nOperational-definition control: lower trigger so even small exceptions are consistently enforced")
    print("sequence collapse_frac final_debt max_debt access_expectation consequences")
    for j, (name, events) in enumerate(
        {
            "twenty_small_20x0.05": [0.05] * 20,
            "forty_tiny_40x0.025": [0.025] * 40,
        }.items()
    ):
        row = simulate_sequence(
            events,
            reps=args.reps,
            seed=20260700 + j,
            individual_trigger=0.18,
            cumulative_trigger=1.05,
            ambiguity=0.55,
        )
        print(
            f"{name:24s} {row.collapse_frac:13.5f} {row.mean_final_debt:10.5f} "
            f"{row.mean_max_debt:8.5f} {row.mean_access_expectation:18.5f} "
            f"{row.mean_consequences:12.5f}"
        )

    print(
        "\nInterpretation: the NODE constraint is validated if repeated below-trigger "
        "exceptions create more precedent debt/access expectation and more collapse "
        "than a single dramatic violation with comparable total severity, and if "
        "operationally enforcing small exceptions removes the effect."
    )


if __name__ == "__main__":
    main()
