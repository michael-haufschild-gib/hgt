#!/usr/bin/env python3
"""Structural checks for CLG curvature-topology output."""

from __future__ import annotations

import json
import sys
from pathlib import Path

root = Path(sys.argv[1] if len(sys.argv) > 1 else ".")
data = json.loads((root / "results.json").read_text())
assert data["scope"] == "diagnostic only; forbidden as Lean input"
for campaign in (data["deterministic"], data["randomized"]):
    assert campaign["pairs"] > 0
    assert campaign["lambda_evaluations"] >= campaign["pairs"]
    assert (campaign["third_all_positive"] + campaign["third_all_negative"] +
            campaign["third_mixed"] + campaign["third_unresolved"] == campaign["pairs"])
    assert len(campaign["first_negative_second"]) == min(
        20, campaign["robust_negative_second"])
print("verified: curvature topology counts and route-kill witnesses")
