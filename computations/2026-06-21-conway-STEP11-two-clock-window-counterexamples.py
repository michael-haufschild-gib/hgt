#!/usr/bin/env python3
"""STEP 11 subwindow counterexample search for two-clock observation sequence.

Wild metaphor:
  An agent can decide which part of an interactive stream to observe. Search
  contiguous subwindows for sign flips relative to the full two-clock sign.
"""

from __future__ import annotations

import runpy

import numpy as np


BASE = runpy.run_path("computations/2026-06-21-conway-observation-sequence-two-clock.py")
two_clock_series = BASE["two_clock_series"]
signed_metrics = BASE["signed_metrics"]


def main() -> None:
    q = 0.50
    cases = [
        ("critical_low_s03", 0.30, (100.0, 170.0), "critical"),
        ("critical_low_s05", 0.50, (100.0, 170.0), "critical"),
        ("critical_low_s07", 0.70, (100.0, 170.0), "critical"),
        ("critical_high_s03", 0.30, (500.0, 570.0), "critical"),
        ("critical_high_s05", 0.50, (500.0, 570.0), "critical"),
        ("right_low_s12", 1.20, (100.0, 170.0), "right"),
        ("right_high_s12", 1.20, (500.0, 570.0), "right"),
    ]
    lengths = [120, 180, 240]
    print("STEP 11 two-clock sliding-window counterexamples")
    print("q=0.50 samples=720")
    print("case region full_corr win_len flip_count total min_corr max_corr verdict")
    robust_rows = 0
    total_rows = 0
    for label, sigma, window, region in cases:
        errors, tension = two_clock_series(sigma, window, 720, 160)
        full = signed_metrics(errors, tension, q)["uniform_corr"]
        for win_len in lengths:
            vals = []
            step = max(10, win_len // 6)
            for start in range(0, len(errors) - win_len + 1, step):
                vals.append(signed_metrics(errors[start : start + win_len], tension[start : start + win_len], q)["uniform_corr"])
            arr = np.asarray(vals, dtype=float)
            if region == "critical":
                flips = int(np.sum(arr >= 0.0))
            else:
                flips = int(np.sum(arr <= 0.0))
            ok = flips == 0
            robust_rows += int(ok)
            total_rows += 1
            print(
                f"{label:17s} {region:8s} {full:+.4f} {win_len:03d} {flips:02d} {len(arr):02d} "
                f"{float(np.min(arr)):+.4f} {float(np.max(arr)):+.4f} {int(ok)}"
            )
    print()
    print(f"SLIDING_WINDOW_SIGN_NO_FLIP {robust_rows}/{total_rows}")
    print(
        "Interpretation: subwindow sign flips are minimal observation-window counterexamples. "
        "The two-clock layer should be stated with window length/sequence requirements, not as "
        "a pointwise sign law."
    )


if __name__ == "__main__":
    main()
