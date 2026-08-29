#!/usr/bin/env python3
"""Independent artifact checks for reflected-fibre PD hostile test."""

from __future__ import annotations

import json
import sys
from pathlib import Path

import mpmath as mp


folder = Path(sys.argv[1] if len(sys.argv) > 1 else ".")
data = json.loads((folder / "results.json").read_text())
survivor = json.loads((folder / "survivor-results.json").read_text())
center_survivor = json.loads((folder / "survivor-center-results.json").read_text())
assert data["centers"] == len(data["float_records"])
assert data["strongest_transform_candidate"] == min(
    data["float_records"], key=lambda item: item["minimum_transform_ratio"])
assert data["strongest_toeplitz_candidate"] == min(
    data["float_records"], key=lambda item: item["minimum_toeplitz_eigenvalue"])
transform = mp.mpf(data["high_precision_transform"]["value"])
toeplitz = mp.mpf(data["high_precision_toeplitz_min_eigenvalue"])
assert mp.sign(transform) == data["high_precision_transform"]["sign"]
assert mp.sign(toeplitz) == data["high_precision_toeplitz_sign"]
assert data["rational_step_witnesses"][-1]["size"] == 6
assert data["rational_step_witnesses"][-1]["sign"] < 0
assert all(item["high_precision_sign"] > 0 for item in survivor["cases"])
assert center_survivor["total_packets"] == 10_880_000
assert all(item["high_precision_sign"] > 0 for item in center_survivor["cases"])
print("verified: full-PD kill and finite-order survivor signs are internally consistent")
