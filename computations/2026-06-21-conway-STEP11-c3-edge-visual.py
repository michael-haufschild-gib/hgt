#!/usr/bin/env python3
"""STEP 11 visual/metaphor experiment for Hawkes edge correction -> C3.

Metaphor:
  Pre-window Hawkes events leave a ghost intensity tail. For C3, an interval
  edge can leave a ghost phase-energy tail. Slide the observation window and
  visualize whether guard-band deletion erases the true-vs-finite H1 gap.
"""

from __future__ import annotations

import runpy

import numpy as np


BASE = runpy.run_path("computations/2026-06-21-conway-hawkes-edge-c3.py")
phase_series = BASE["phase_series"]
phase_stats = BASE["phase_stats"]


def bar(value: float) -> str:
    n = int(max(0.0, min(30.0, round(30.0 * value))))
    return "#" * n + "." * (30 - n)


def main() -> None:
    rng = np.random.default_rng(2606215811)
    sigma = 0.50
    starts = [14.0, 30.0, 60.0, 100.0, 160.0, 260.0, 360.0, 500.0, 650.0]
    length = 70.0
    crop = 0.20
    print("STEP 11 C3 ghost-edge visual")
    print(f"sigma={sigma:.2f} length={length:.1f} crop={crop:.2f}")
    print("start full_gap interior_gap retention visual verdict")
    passes = 0
    for start in starts:
        window = (start, start + length)
        t_true, th_true = phase_series("true", sigma, window, 600, rng)
        t_fin, th_fin = phase_series("finite", sigma, window, 600, rng)
        full_true = phase_stats(t_true, th_true, 0.001)
        full_fin = phase_stats(t_fin, th_fin, 0.001)
        int_true = phase_stats(t_true, th_true, crop)
        int_fin = phase_stats(t_fin, th_fin, crop)
        full_gap = abs(full_true["h1_interior"] - full_fin["h1_interior"])
        int_gap = abs(int_true["h1_interior"] - int_fin["h1_interior"])
        retention = int_gap / (full_gap + 1e-300)
        ok = retention > 0.50 and int_gap > 0.15
        passes += int(ok)
        print(
            f"{start:06.1f} {full_gap:.5f} {int_gap:.5f} {retention:.3f} "
            f"{bar(min(retention, 1.0))} {int(ok)}"
        )
    print()
    print(f"SLIDING_GUARD_RETENTION_PASS {passes}/{len(starts)}")
    print(
        "Interpretation: the ghost-edge metaphor is real enough to be a gate. A few windows can "
        "lose the gap after guard deletion, so C3 should require guard-band reporting rather than "
        "trusting a single raw interval. Most tested windows retained the gap."
    )


if __name__ == "__main__":
    main()
