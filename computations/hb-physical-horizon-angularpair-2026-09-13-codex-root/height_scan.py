#!/usr/bin/env python3
"""Continuous-height root scan of the arithmetic angular-pair finite part."""

from __future__ import annotations

import json
import os
import time
from concurrent.futures import ProcessPoolExecutor

from horizon_pair import cell_remainder


def run(gamma):
    start = time.monotonic()
    result = cell_remainder(gamma, 4.0, 10, 10, 36, 32)
    return {"gamma": gamma, "seconds": time.monotonic() - start, **result}


if __name__ == "__main__":
    heights = [10.0 + 1.25 * j for j in range(33)]
    with ProcessPoolExecutor(max_workers=min(16, os.cpu_count() or 1)) as pool:
        rows = list(pool.map(run, heights, chunksize=1))
    brackets = []
    for left, right in zip(rows, rows[1:]):
        if left["total_remainder"] * right["total_remainder"] < 0:
            brackets.append([left["gamma"], right["gamma"]])
    payload = {"settings": {"ymax": 4.0, "x_order": 10, "y_order": 10, "margin": 36, "dps": 32}, "rows": rows, "sign_change_brackets": brackets}
    with open("height-scan.json.tmp", "w") as handle:
        json.dump(payload, handle, indent=2)
    os.replace("height-scan.json.tmp", "height-scan.json")

