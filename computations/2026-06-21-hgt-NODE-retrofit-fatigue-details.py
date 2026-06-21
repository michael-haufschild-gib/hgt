#!/usr/bin/env python3
"""THE-MACHINE NODE test: retrofit details introduce fatigue hot spots.

NODE:
    Fatigue-prone details introduced by later retrofits, drilled holes, service
    penetrations, or equipment mounts.

Constraint tested:
    Fatigue life is controlled by local stress concentration and load history,
    not only by nominal design stress. A late drilled hole/mount can multiply
    local stress enough that Miner's damage after the retrofit dominates the
    earlier low-stress history.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass

import numpy as np


@dataclass(frozen=True)
class Case:
    name: str
    kt: float
    installed_at_frac: float
    endurance: float
    cycles: int


def variable_load(cycles: int, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    base = rng.lognormal(mean=np.log(42.0), sigma=0.14, size=cycles)
    gusts = rng.random(cycles) < 0.015
    base[gusts] *= rng.uniform(1.35, 1.75, size=np.sum(gusts))
    return base


def miner_damage(loads: np.ndarray, *, kt: float, endurance: float, m: float = 5.0, c: float = 2.8e13) -> float:
    local = kt * loads
    active = local > endurance
    if not np.any(active):
        return 0.0
    # S-N damage: each active cycle consumes 1/Nf, with Nf=C/S^m.
    return float(np.sum((local[active] ** m) / c))


def simulate(case: Case, loads: np.ndarray) -> dict[str, float]:
    cut = int(case.installed_at_frac * len(loads))
    before = miner_damage(loads[:cut], kt=1.0, endurance=case.endurance)
    after_nominal = miner_damage(loads[cut:], kt=1.0, endurance=case.endurance)
    after_retrofit = miner_damage(loads[cut:], kt=case.kt, endurance=case.endurance)
    total = before + after_retrofit
    return {
        "before": before,
        "after_nominal": after_nominal,
        "after_retrofit": after_retrofit,
        "total": total,
        "retrofit_share": after_retrofit / max(total, 1e-300),
        "amplification": after_retrofit / max(after_nominal, 1e-300),
        "local_peak": float(case.kt * np.max(loads[cut:])),
        "active_frac": float(np.mean(case.kt * loads[cut:] > case.endurance)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cycles", type=int, default=90000)
    args = parser.parse_args()

    loads = variable_load(args.cycles, seed=20260621)
    cases = [
        Case("original_no_retrofit", kt=1.0, installed_at_frac=0.55, endurance=58.0, cycles=args.cycles),
        Case("rounded_service_hole", kt=1.55, installed_at_frac=0.55, endurance=58.0, cycles=args.cycles),
        Case("sharp_drilled_hole", kt=2.35, installed_at_frac=0.55, endurance=58.0, cycles=args.cycles),
        Case("equipment_mount_cluster", kt=3.10, installed_at_frac=0.55, endurance=58.0, cycles=args.cycles),
        Case("early_bad_retrofit", kt=2.35, installed_at_frac=0.10, endurance=58.0, cycles=args.cycles),
        Case("late_bad_retrofit", kt=2.35, installed_at_frac=0.85, endurance=58.0, cycles=args.cycles),
    ]

    print("NODE: fatigue-prone retrofit details as local stress concentrators")
    print(f"cycles={args.cycles} nominal_load_median={np.median(loads):.5f} nominal_load_q99={np.quantile(loads,0.99):.5f}")
    print(
        "case kt installed_at before_damage after_nominal after_retrofit total_damage "
        "retrofit_share amplification active_frac local_peak"
    )
    for case in cases:
        row = simulate(case, loads)
        print(
            f"{case.name:24s} {case.kt:.2f} {case.installed_at_frac:.2f} "
            f"{row['before']:.6e} {row['after_nominal']:.6e} {row['after_retrofit']:.6e} "
            f"{row['total']:.6e} {row['retrofit_share']:.5f} {row['amplification']:.3e} "
            f"{row['active_frac']:.5f} {row['local_peak']:.5f}"
        )

    print("\nEndurance-limit boundary sweep for a sharp drilled hole")
    print("endurance original_active retrofit_active original_damage retrofit_damage amplification")
    for endurance in [50.0, 55.0, 58.0, 62.0, 68.0]:
        original = miner_damage(loads, kt=1.0, endurance=endurance)
        retrofit = miner_damage(loads, kt=2.35, endurance=endurance)
        print(
            f"{endurance:9.2f} {np.mean(loads > endurance):15.5f} "
            f"{np.mean(2.35 * loads > endurance):15.5f} {original:.6e} "
            f"{retrofit:.6e} {retrofit / max(original, 1e-300):.3e}"
        )

    print(
        "\nInterpretation: the constraint is validated if the retrofit's local Kt "
        "multiplication makes post-retrofit damage dominate nominal history, especially "
        "near the endurance-limit boundary."
    )


if __name__ == "__main__":
    main()
