#!/usr/bin/env python3
"""Actual-zero and midpoint-control modular-cell finite parts."""

from __future__ import annotations

import json
import os
import statistics
import time
from concurrent.futures import ProcessPoolExecutor

import mpmath as mp

from horizon_pair import cell_remainder


def run(task):
    kind, n, gamma = task
    start = time.monotonic()
    result = cell_remainder(gamma, 4.0, 14, 14, 42, 38)
    return {"kind": kind, "n": n, "gamma": gamma, "seconds": time.monotonic() - start, **result}


if __name__ == "__main__":
    with mp.workdps(50):
        zeros = [float(mp.im(mp.zetazero(n))) for n in range(1, 14)]
    tasks = []
    for n in range(1, 13):
        tasks.append(("actual", n, zeros[n - 1]))
        tasks.append(("midpoint", n, (zeros[n - 1] + zeros[n]) / 2))
    with ProcessPoolExecutor(max_workers=min(16, os.cpu_count() or 1)) as pool:
        rows = list(pool.map(run, tasks, chunksize=1))
    summary = {}
    for kind in ("actual", "midpoint"):
        group = [row for row in rows if row["kind"] == kind]
        summary[kind] = {
            "median_abs_total": statistics.median(abs(row["total_remainder"]) for row in group),
            "median_relative": statistics.median(row["relative_to_source_budget"] for row in group),
            "median_component_cancellation": statistics.median(row["component_cancellation"] for row in group),
            "signs": [1 if row["total_remainder"] > 0 else -1 for row in group],
        }
    payload = {"settings": {"ymax": 4.0, "x_order": 14, "y_order": 14, "margin": 42, "dps": 38}, "rows": rows, "summary": summary}
    with open("cell-landscape.json.tmp", "w") as handle:
        json.dump(payload, handle, indent=2)
    os.replace("cell-landscape.json.tmp", "cell-landscape.json")

