#!/usr/bin/env python3
"""NODE test: frailty as visible failure of coupled reserves.

NODE:
    Frailty can be understood as a visible failure of reserve across multiple
    coupled systems.

Constraint:
    A single reserve level is insufficient. Visible frailty appears when
    several coupled reserves are near threshold, because a perturbation in one
    system drains support from the others and creates a cascade.
"""

from __future__ import annotations

import argparse

import numpy as np


def run_case(initial: np.ndarray, coupling: float, shock: np.ndarray, steps: int = 120) -> dict[str, float]:
    reserve = initial.astype(float).copy()
    capacity = initial.astype(float).copy()
    failed_counts = []
    min_reserves = []
    for t in range(steps):
        pulse = shock if t == 8 else 0.02 * np.ones_like(reserve)
        deficit = np.maximum(0.0, 0.42 - reserve)
        support_load = coupling * (np.roll(deficit, 1) + np.roll(deficit, -1)) / 2.0
        recovery = 0.045 * np.maximum(0.0, capacity - reserve)
        reserve = reserve + recovery - pulse - support_load
        reserve = np.clip(reserve, 0.0, 1.0)
        failed_counts.append(float(np.sum(reserve < 0.42)))
        min_reserves.append(float(np.min(reserve)))
    failed = np.asarray(failed_counts)
    min_r = np.asarray(min_reserves)
    first_visible = np.argmax(failed >= 3) if np.any(failed >= 3) else -1
    recovery_time = -1
    if first_visible >= 0:
        later = np.where(failed[first_visible:] == 0)[0]
        recovery_time = int(later[0]) if len(later) else -1
    return {
        "mean_initial": float(np.mean(initial)),
        "min_initial": float(np.min(initial)),
        "coupling": float(coupling),
        "peak_failed": float(np.max(failed)),
        "visible_frailty": float(np.max(failed) >= 3),
        "first_visible": float(first_visible),
        "recovery_time": float(recovery_time),
        "min_reserve": float(np.min(min_r)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--steps", type=int, default=120)
    args = parser.parse_args()

    cases = {
        "young_high_reserve": np.array([0.88, 0.86, 0.91, 0.87, 0.89]),
        "single_weak_system": np.array([0.88, 0.86, 0.49, 0.87, 0.89]),
        "aged_even_loss": np.array([0.58, 0.56, 0.59, 0.55, 0.57]),
        "aged_hidden_multiweak": np.array([0.62, 0.50, 0.53, 0.49, 0.61]),
    }
    shock = np.array([0.12, 0.18, 0.22, 0.18, 0.12])
    print("NODE: frailty as coupled reserve failure")
    print("case coupling mean_initial min_initial peak_failed visible_frailty first_visible recovery_time min_reserve")
    for name, initial in cases.items():
        for coupling in [0.0, 0.25, 0.55, 0.85]:
            out = run_case(initial, coupling, shock, args.steps)
            print(
                f"{name:22s} {coupling:.2f} {out['mean_initial']:.6f} {out['min_initial']:.6f} "
                f"{out['peak_failed']:.0f} {out['visible_frailty']:.0f} {out['first_visible']:.0f} "
                f"{out['recovery_time']:.0f} {out['min_reserve']:.6f}"
            )
    print(
        "\nInterpretation key: visible frailty should appear at similar resting "
        "means only when several reserves are marginal and coupling transmits "
        "support load across systems."
    )


if __name__ == "__main__":
    main()
