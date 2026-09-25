#!/usr/bin/env python3
"""Pointwise sign map behind the modular-cell finite-part sign."""

from __future__ import annotations

import json
import math
import os
import time
from concurrent.futures import ProcessPoolExecutor

import mpmath as mp

from horizon_pair import angular_pair_terms


def run(task):
    label, gamma = task
    counts = {"difference_positive": 0, "difference_negative": 0, "full_positive": 0, "full_negative": 0}
    extrema = {"difference_min": [float("inf"), None], "difference_max": [-float("inf"), None]}
    start = time.monotonic()
    for ix in range(33):
        x = -0.5 + ix / 32
        lower = math.sqrt(1 - x * x)
        for iy in range(33):
            y = lower * (4.0 / lower) ** (iy / 32)
            full = float(angular_pair_terms(gamma, x, y, False, 45, 38)[2].real)
            principal = float(angular_pair_terms(gamma, x, y, True, 45, 38)[2].real)
            difference = full - principal
            counts["difference_positive" if difference > 0 else "difference_negative"] += 1
            counts["full_positive" if full > 0 else "full_negative"] += 1
            if difference < extrema["difference_min"][0]:
                extrema["difference_min"] = [difference, [x, y]]
            if difference > extrema["difference_max"][0]:
                extrema["difference_max"] = [difference, [x, y]]
    return {"label": label, "gamma": gamma, "seconds": time.monotonic() - start, "counts": counts, "extrema": extrema}


if __name__ == "__main__":
    with mp.workdps(50):
        z1 = float(mp.im(mp.zetazero(1)))
        z2 = float(mp.im(mp.zetazero(2)))
        z4 = float(mp.im(mp.zetazero(4)))
        z5 = float(mp.im(mp.zetazero(5)))
    tasks = (("zeta1", z1), ("mid1", (z1 + z2) / 2), ("zeta4", z4), ("mid4", (z4 + z5) / 2))
    with ProcessPoolExecutor(max_workers=4) as pool:
        rows = list(pool.map(run, tasks))
    with open("point-map.json.tmp", "w") as handle:
        json.dump(rows, handle, indent=2)
    os.replace("point-map.json.tmp", "point-map.json")
