#!/usr/bin/env python3
"""Resolution challenge for the zero4 image-short near-hit."""

from __future__ import annotations

import json
import os
import time
from concurrent.futures import ProcessPoolExecutor

from native_delay import signed_action


GAMMA = 30.424876125859512
SECTION = {"x": -0.2, "y": -0.8, "X": 0.13, "k": 1.5, "V": 2.0}
SETTINGS = (
    ("medium", 72, 18, 24, 45, 40),
    ("strong", 88, 22, 28, 55, 45),
)


def run(setting):
    label, h_order, clock_order, theta_order, margin, dps = setting
    start = time.monotonic()
    result = signed_action(
        GAMMA, SECTION, h_order, clock_order, theta_order, margin, dps
    )
    full, principal = result["ordered"]
    return {
        "label": label,
        "orders": [h_order, clock_order, theta_order],
        "margin": margin,
        "dps": dps,
        "seconds": time.monotonic() - start,
        "ordered_imag": float(full.imag),
        "relative": float(result["relative"][0]),
        "principal_relative": float(result["relative"][1]),
        "tail_leverage": float(
            abs(full - principal) / max(abs(full) + abs(principal), 1e-300)
        ),
        "sheet_cancellation": float(
            abs(result["signed"][0, 0])
            / max(abs(result["direct"][0, 0]) + abs(result["image"][0, 0]), 1e-300)
        ),
        "conjugacy_error": float(
            abs(result["signed"][1, 0] - result["signed"][0, 0].conjugate())
            / max(abs(result["signed"][0, 0]) + abs(result["signed"][1, 0]), 1e-300)
        ),
    }


if __name__ == "__main__":
    with ProcessPoolExecutor(max_workers=2) as pool:
        rows = list(pool.map(run, SETTINGS))
    payload = {"gamma": GAMMA, "section": SECTION, "rows": rows}
    with open("image-short-validation.json.tmp", "w") as handle:
        json.dump(payload, handle, indent=2)
    os.replace("image-short-validation.json.tmp", "image-short-validation.json")
