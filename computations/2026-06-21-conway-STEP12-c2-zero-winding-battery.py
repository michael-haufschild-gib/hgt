#!/usr/bin/env python3
"""STEP 12 battery for canalization -> C2 holonomy.

Filter to zero-winding loops and test whether centered holonomy still separates
true from finite/random in the critical strip and collapses on the right.
"""

from __future__ import annotations

import runpy

import numpy as np


BASE = runpy.run_path("computations/2026-06-21-conway-canalization-c2-holonomy.py")

first_primes = BASE["first_primes"]
rectangle_points = BASE["rectangle_points"]
centered_holonomy = BASE["centered_holonomy"]


def summarize_family(name, specs, primes, rng):
    rows = {}
    for kind in ["true", "finite", "random"]:
        vals = []
        winds = []
        zero_vals = []
        for spec in specs:
            pts = rectangle_points(*spec, per_edge=34)
            val, wind = centered_holonomy(kind, pts, primes, rng)
            vals.append(abs(val))
            winds.append(wind)
            if abs(wind) < 0.5:
                zero_vals.append(abs(val))
        rows[kind] = {
            "all_mean": float(np.mean(vals)),
            "zero_mean": float(np.mean(zero_vals)) if zero_vals else float("nan"),
            "zero_count": len(zero_vals),
            "winding_frac": float(np.mean(np.abs(winds) >= 0.5)),
        }
    return rows


def main() -> None:
    rng = np.random.default_rng(2606217201)
    primes = first_primes(160)
    families = {
        "critical_small": [(0.50, t, 0.05, 2.0) for t in np.linspace(24, 165, 24)],
        "critical_medium": [(0.50, t, 0.10, 4.0) for t in np.linspace(24, 165, 24)],
        "critical_offseam": [(s, t, 0.10, 4.0) for s in [0.42, 0.58] for t in np.linspace(30, 160, 12)],
        "right_medium": [(1.25, t, 0.10, 4.0) for t in np.linspace(30, 160, 24)],
    }
    print("STEP 12 C2 zero-winding centered-holonomy battery")
    print(
        "family kind all_mean_abs zero_winding_mean_abs zero_winding_count winding_nonzero_frac "
        "true_finite_zero_gap true_random_zero_gap verdict"
    )
    critical_pass = 0
    critical_total = 0
    right_pass = 0
    right_total = 0
    for family, specs in families.items():
        rows = summarize_family(family, specs, primes, rng)
        true_zero = rows["true"]["zero_mean"]
        finite_zero = rows["finite"]["zero_mean"]
        random_zero = rows["random"]["zero_mean"]
        finite_gap = true_zero - finite_zero
        random_gap = true_zero - random_zero
        for kind in ["true", "finite", "random"]:
            if family.startswith("critical"):
                ok = (
                    rows["true"]["zero_count"] >= 6
                    and finite_gap > 2.0
                    and random_gap > 2.0
                )
                critical_pass += int(ok and kind == "true")
                critical_total += int(kind == "true")
            else:
                ok = (
                    rows["true"]["zero_count"] >= 6
                    and abs(finite_gap) < 0.5
                    and abs(random_gap) < 1.0
                )
                right_pass += int(ok and kind == "true")
                right_total += int(kind == "true")
            print(
                f"{family:17s} {kind:6s} {rows[kind]['all_mean']:.6f} {rows[kind]['zero_mean']:.6f} "
                f"{rows[kind]['zero_count']:02d} {rows[kind]['winding_frac']:.3f} "
                f"{finite_gap:+.6f} {random_gap:+.6f} {int(ok)}"
            )
    print()
    print(f"CRITICAL_ZERO_WINDING_TRUE_SEPARATES {critical_pass}/{critical_total}")
    print(f"RIGHT_ZERO_WINDING_COLLAPSE {right_pass}/{right_total}")
    print(
        "Interpretation: zero-winding centered holonomy is the non-argument-principle gate. "
        "If it separates in critical loops and collapses on the right, C2 loop tests should "
        "include this centered/zero-winding battery."
    )


if __name__ == "__main__":
    main()
