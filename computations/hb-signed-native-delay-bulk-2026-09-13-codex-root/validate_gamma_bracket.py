#!/usr/bin/env python3
"""Cross-resolution and cross-section challenge for a non-zeta height root."""

from __future__ import annotations

import json
import os
import time
from concurrent.futures import ProcessPoolExecutor

from native_delay import signed_action


GAMMAS = (15.075, 15.1125)
SECTIONS = {
    "base": {"x": -0.4, "y": -0.6, "X": 0.13, "k": 1.5, "V": 2.0},
    "diagonal": {"x": -0.5, "y": -0.5, "X": 0.13, "k": 1.5, "V": 2.0},
    "horizontal_shift": {"x": -0.4, "y": -0.6, "X": 0.31, "k": 1.5, "V": 2.0},
}


def run(task):
    gamma, label, section = task
    start = time.monotonic()
    result = signed_action(gamma, section, 52, 20, 26, 50, 42)
    full, principal = result["ordered"]
    return {
        "gamma": gamma,
        "label": label,
        "section": section,
        "orders": [52, 20, 26],
        "margin": 50,
        "dps": 42,
        "seconds": time.monotonic() - start,
        "ordered_imag": float(full.imag),
        "relative": float(result["relative"][0]),
        "principal_relative": float(result["relative"][1]),
        "tail_leverage": float(
            abs(full - principal) / max(abs(full) + abs(principal), 1e-300)
        ),
        "conjugacy_error": float(
            abs(result["signed"][1, 0] - result["signed"][0, 0].conjugate())
            / max(abs(result["signed"][0, 0]) + abs(result["signed"][1, 0]), 1e-300)
        ),
    }


if __name__ == "__main__":
    tasks = [
        (gamma, label, dict(section))
        for label, section in SECTIONS.items()
        for gamma in GAMMAS
    ]
    with ProcessPoolExecutor(max_workers=6) as pool:
        rows = list(pool.map(run, tasks))
    payload = {"base_bracket": list(GAMMAS), "rows": rows}
    with open("gamma-bracket-validation.json.tmp", "w") as handle:
        json.dump(payload, handle, indent=2)
    os.replace("gamma-bracket-validation.json.tmp", "gamma-bracket-validation.json")
