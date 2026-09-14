#!/usr/bin/env python3
"""Crossed cutoff/order validation of selected finite parts."""

from __future__ import annotations

import json
import os
import time
from concurrent.futures import ProcessPoolExecutor

import mpmath as mp

from horizon_pair import cell_remainder


def run(task):
    label, gamma, ymax, order = task
    start = time.monotonic()
    result = cell_remainder(gamma, ymax, order, order, 50, 42)
    return {"label": label, "gamma": gamma, "ymax": ymax, "order": order, "seconds": time.monotonic() - start, **result}


if __name__ == "__main__":
    with mp.workdps(50):
        z1 = float(mp.im(mp.zetazero(1)))
        z2 = float(mp.im(mp.zetazero(2)))
        z4 = float(mp.im(mp.zetazero(4)))
        z5 = float(mp.im(mp.zetazero(5)))
    samples = (("zeta1", z1), ("mid1", (z1 + z2) / 2), ("zeta4", z4), ("mid4", (z4 + z5) / 2))
    tasks = [(label, gamma, ymax, order) for label, gamma in samples for ymax, order in ((3.0, 14), (4.0, 18), (5.0, 22))]
    with ProcessPoolExecutor(max_workers=min(12, os.cpu_count() or 1)) as pool:
        rows = list(pool.map(run, tasks, chunksize=1))
    with open("cutoff-validation.json.tmp", "w") as handle:
        json.dump(rows, handle, indent=2)
    os.replace("cutoff-validation.json.tmp", "cutoff-validation.json")

