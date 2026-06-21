#!/usr/bin/env python3
"""Step 12 guard-band sweep for holonomy refinement history."""

from __future__ import annotations

import importlib.util
import pathlib
import sys

import numpy as np


BASE = pathlib.Path(__file__).with_name("2026-06-21-conway-holonomy-refinement-history.py")
spec = importlib.util.spec_from_file_location("holonomy_refinement", BASE)
mod = importlib.util.module_from_spec(spec)
sys.modules["holonomy_refinement"] = mod
spec.loader.exec_module(mod)


def guarded_budget(seed: int, side: int, floor: int, total: int = 720) -> list[int]:
    rng = np.random.default_rng(seed)
    counts = np.full(4, floor, dtype=int)
    counts[side] += 2
    while counts.sum() < total:
        j = int(rng.choice(4, p=counts / counts.sum()))
        counts[j] += 1
    return counts.tolist()


def main() -> None:
    print("STEP12: per-side refinement floor for Master-1 holonomy candidates")
    print("window floor max_winding_imag_error max_raw_L1 max_mean_L1")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        ref = mod.contour_measure([180, 180, 180, 180], window)
        ref_w = ref["winding_like"]
        for floor in [2, 20, 60, 100, 140, 180]:
            imag_errors = []
            raw_l1 = []
            mean_l1 = []
            for side in range(4):
                budget = guarded_budget(9000 + int(window[0]) + 10 * floor + side, side, floor)
                m = mod.contour_measure(budget, window)
                imag_errors.append(abs((m["winding_like"] - ref_w).imag))
                raw_l1.append(mod.l1(m["raw_shape"], ref["raw_shape"]))
                mean_l1.append(mod.l1(m["mean_shape"], ref["mean_shape"]))
            print(
                f"[{window[0]:.0f},{window[1]:.0f}] {floor:03d} "
                f"{max(imag_errors):.4f} {max(raw_l1):.3f} {max(mean_l1):.3f}"
            )


if __name__ == "__main__":
    main()
