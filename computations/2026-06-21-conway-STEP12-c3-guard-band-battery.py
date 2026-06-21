#!/usr/bin/env python3
"""STEP 12 battery for Hawkes edge correction -> C3.

Stress result:
  The C3 phase-Sobolev true-vs-finite gap should not be an observation-edge
  artifact. Delete guard bands of increasing width and check whether the gap
  survives in critical lanes while true/finite collapse on the right.
"""

from __future__ import annotations

import runpy

import numpy as np


BASE = runpy.run_path("computations/2026-06-21-conway-hawkes-edge-c3.py")
phase_series = BASE["phase_series"]
phase_stats = BASE["phase_stats"]


def main() -> None:
    rng = np.random.default_rng(2606215719)
    crops = [0.05, 0.10, 0.20, 0.30]
    cases = []
    for label, window in [
        ("zero_strip", (14.0, 84.0)),
        ("critical_low", (100.0, 170.0)),
        ("critical_high", (500.0, 570.0)),
    ]:
        for sigma in [0.40, 0.50, 0.60, 0.70]:
            cases.append((label, sigma, window, "critical"))
    for label, window in [
        ("right_low", (100.0, 170.0)),
        ("right_high", (500.0, 570.0)),
    ]:
        for sigma in [1.15, 1.30, 1.50]:
            cases.append((label, sigma, window, "right"))

    print("STEP 12 C3 guard-band invariance battery")
    print("samples=650 crops=0.05,0.10,0.20,0.30")
    print(
        "case sigma region full_gap gaps_by_crop retentions_by_crop "
        "min_gap min_retention verdict"
    )
    critical_ok = 0
    critical_total = 0
    right_ok = 0
    right_total = 0
    for label, sigma, window, region in cases:
        t_true, th_true = phase_series("true", sigma, window, 650, rng)
        t_fin, th_fin = phase_series("finite", sigma, window, 650, rng)
        full_true = phase_stats(t_true, th_true, 0.001)
        full_fin = phase_stats(t_fin, th_fin, 0.001)
        full_gap = abs(full_true["h1_interior"] - full_fin["h1_interior"])
        gaps = []
        rets = []
        for crop in crops:
            st_true = phase_stats(t_true, th_true, crop)
            st_fin = phase_stats(t_fin, th_fin, crop)
            gap = abs(st_true["h1_interior"] - st_fin["h1_interior"])
            gaps.append(gap)
            rets.append(gap / (full_gap + 1e-300))
        min_gap = min(gaps)
        min_ret = min(rets)
        if region == "critical":
            ok = min_gap > 0.15 and min_ret > 0.50
            critical_ok += int(ok)
            critical_total += 1
        else:
            ok = max(gaps) < 0.04
            right_ok += int(ok)
            right_total += 1
        gap_str = ",".join(f"{g:.3f}" for g in gaps)
        ret_str = ",".join(f"{r:.2f}" for r in rets)
        print(
            f"{label:13s} {sigma:.2f} {region:8s} {full_gap:.4f} [{gap_str}] "
            f"[{ret_str}] {min_gap:.4f} {min_ret:.3f} {int(ok)}"
        )
    print()
    print(f"CRITICAL_GUARD_BAND_STABLE {critical_ok}/{critical_total}")
    print(f"RIGHT_GUARD_BAND_COLLAPSE {right_ok}/{right_total}")
    print(
        "Interpretation: guard-band stability is a prerequisite for C3. Passing this battery "
        "does not prove the phase-Sobolev conjecture; it says the measured true-vs-finite gap "
        "is not explained by Hawkes-style missing-history energy at the observation edges."
    )


if __name__ == "__main__":
    main()
