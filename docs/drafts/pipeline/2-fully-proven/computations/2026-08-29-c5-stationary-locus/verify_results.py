#!/usr/bin/env python3
"""Independent spot verification for C5 stationary-locus artifacts."""

from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

import mpmath as mp


folder = Path(sys.argv[1] if len(sys.argv) > 1 else ".")
spec = importlib.util.spec_from_file_location("experiment", folder / "run_experiments.py")
experiment = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(experiment)
data = json.loads((folder / "results.json").read_text())
experiment.initialize(max(160, data["parameters"]["dps"]))

assert data["points"] == data["numerator_sign_counts"]["positive"]
assert data["numerator_sign_counts"]["negative"] == 0
assert len(data["velocity_sign_change_brackets"]) == len(data["stationary_roots"])
for record in data["stationary_roots"]:
    left, right = map(mp.mpf, record["bracket"])
    vl = experiment.c5_stationary_data(left)[1]
    vr = experiment.c5_stationary_data(right)[1]
    assert mp.sign(vl) * mp.sign(vr) <= 0
    middle = mp.mpf(record["root_midpoint"])
    n, v, a = experiment.c5_stationary_data(middle)
    assert n > 0
    assert abs(v) < mp.mpf("1e-60")
    assert mp.sign(a) == mp.sign(mp.mpf(record["normalized_acceleration"]))

for t in (mp.mpf("1e-8"), mp.mpf("0.001"), mp.mpf("0.1"), mp.mpf("1"),
          mp.mpf("10"), mp.mpf("100")):
    n, _, _ = experiment.c5_stationary_data(t)
    assert n > 0

print("verified: sampled C5 positive; every reported stationary root has positive C5")
