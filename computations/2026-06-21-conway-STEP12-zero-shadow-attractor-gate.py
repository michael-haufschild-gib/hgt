#!/usr/bin/env python3
"""Step 12 sweep for zero-shadow attractor-recurrence gate."""

from __future__ import annotations

import importlib.util
import pathlib
import sys

import numpy as np


BASE = pathlib.Path(__file__).with_name("2026-06-21-conway-zero-shadow-attractor-recurrence.py")
spec = importlib.util.spec_from_file_location("attractor_recurrence", BASE)
mod = importlib.util.module_from_spec(spec)
sys.modules["attractor_recurrence"] = mod
spec.loader.exec_module(mod)


def summarize() -> None:
    print("STEP12: zero-shadow profile recurrence + connectivity gate")
    print(
        "threshold kind mean_recurrence min_recurrence mean_components span_windows "
        "conn_recur_windows dependency_positive_windows"
    )
    for threshold in np.linspace(0.70, 1.25, 12):
        for kind in ["true", "finite", "random"]:
            rows = []
            for window in [(100.0, 170.0), (500.0, 570.0), (900.0, 970.0)]:
                seed = 20260621 + int(window[0]) + int(100 * threshold) + {"true": 1, "finite": 2, "random": 3}[kind]
                mask = mod.mask_for(kind, window, float(threshold), seed)
                rows.append(mod.profile_metrics(mask, seed + 71))
            rec = np.array([r.recurrence for r in rows])
            comps = np.array([r.components for r in rows])
            span = np.array([r.span_t for r in rows])
            dep = np.array([r.dependency_gain for r in rows])
            conn_recur = np.array(
                [
                    (r.recurrence >= 0.88 and r.components <= 2 and r.span_t >= 1.0)
                    for r in rows
                ],
                dtype=bool,
            )
            print(
                f"{threshold:.2f} {kind:6s} "
                f"{float(np.mean(rec)):.3f} {float(np.min(rec)):.3f} "
                f"{float(np.mean(comps)):.1f} {int(np.sum(span))}/3 "
                f"{int(np.sum(conn_recur))}/3 {int(np.sum(dep > 0.02))}/3"
            )


if __name__ == "__main__":
    summarize()
