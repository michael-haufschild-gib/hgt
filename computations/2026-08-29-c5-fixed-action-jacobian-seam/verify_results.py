#!/usr/bin/env python3
"""Structural verification of downloaded fixed-action C5 seam results."""

from __future__ import annotations

import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
RESULTS = json.loads((HERE / "results.json").read_text())

assert RESULTS["scope"] == "diagnostic only; forbidden as input to Lean proofs"
assert RESULTS["parameters"]["workers"] == 128
assert RESULTS["parameters"]["dps"] == 240
assert RESULTS["symbolic_seam_series"]["nonzero_coefficients"] == {
    "5": "-(18*L2**3*L6 - 36*L2**2*L4**2 + L2**2*L8 - 5*L2*L4*L6 + 4*L4**3)/(18*L2**2)"
}

scan = RESULTS["scan"]
assert scan["count"] == 633_332
assert scan["negative_count"] == 0
assert scan["zero_count"] == 0
assert scan["positive_count"] == scan["count"]

checkpoints = {record["dps"]: record["values"] for record in RESULTS["precision_checkpoints"]}
assert set(checkpoints) == {80, 160, 240, 480}
for dps in (160, 240, 480):
    assert all(record["sign"] == 1 for record in checkpoints[dps])
t50 = {dps: next(record for record in values if record["t"] == "50")
       for dps, values in checkpoints.items()}
assert t50[80]["sign"] == -1
assert t50[160]["sign"] == t50[240]["sign"] == t50[480]["sign"] == 1
assert t50[160]["margin"] == t50[240]["margin"] == t50[480]["margin"]

for record in RESULTS["derivative_consistency"]:
    errors = {item["u"]: float(item["relative_error"]) for item in record["ratios"]}
    assert errors["1e-18"] < 1e-25

shape = next(record for record in RESULTS["desingularized_shape_attack"]
             if record["t"] == "0.001")
assert ["0.1", "0.5"] in shape["nondecreasing_violations"]
assert ["0.5", "1"] in shape["nonincreasing_violations"]
assert ["1", "2"] in shape["nonincreasing_violations"]

print("verified: symbolic coefficient, positive scan, precision stabilization, derivative limit, shape no-go")
