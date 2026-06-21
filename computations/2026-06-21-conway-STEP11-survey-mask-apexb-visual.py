#!/usr/bin/env python3
"""STEP 11 visual mask sweep for survey-mask -> APEX-B."""

from __future__ import annotations

import runpy

import numpy as np


BASE = runpy.run_path("computations/2026-06-21-conway-survey-mask-apexb.py")
quartet_curvature = BASE["quartet_curvature"]


def bar(value: float, lo: float, hi: float) -> str:
    x = 0.0 if hi <= lo else (value - lo) / (hi - lo)
    n = int(max(0.0, min(28.0, round(28.0 * x))))
    return "#" * n + "." * (28 - n)


def main() -> None:
    a = 0.10
    L = 8.0 * a
    grid = np.linspace(-L, L, 4001)
    curv = quartet_curvature(grid, a)
    mask_half = a
    centers = np.linspace(-2.0 * a, 2.0 * a, 17)
    maxes = []
    rows = []
    for c in centers:
        keep = ~((grid >= c - mask_half) & (grid <= c + mask_half))
        obsmax = float(np.max(curv[keep]))
        maxes.append(obsmax)
        rows.append((c / a, obsmax, int(obsmax > 0.0)))
    lo = min(maxes)
    hi = max(maxes)
    print("STEP 11 APEX-B mask sweep visual")
    print("a=0.10 domain=[-8a,8a] mask_half=a removed_fraction=0.125")
    print("mask_center/a observed_max visual positive_visible")
    for c, obsmax, visible in rows:
        print(f"{c:+.2f} {obsmax:+.6f} {bar(obsmax, lo, hi)} {visible}")
    hidden = sum(1 for _c, _m, v in rows if v == 0)
    print()
    print(f"CENTER_SWEEP_HIDES_CORE {hidden}/{len(rows)}")
    print(
        "Interpretation: the same high-coverage mask is harmless when off-center and fatal when "
        "it covers the sparse positive core. This is the survey-mask analogue of no-margin "
        "coverage risk."
    )


if __name__ == "__main__":
    main()
