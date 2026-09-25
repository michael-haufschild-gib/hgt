#!/usr/bin/env python3
"""Artifact checks for the exact S6F Jacobi/Loewner hostile test."""

from __future__ import annotations

import json
import sys
from pathlib import Path


folder = Path(sys.argv[1] if len(sys.argv) > 1 else ".")
rank_two = json.loads((folder / "rank-two-results.json").read_text())
determinant = json.loads((folder / "determinant-results.json").read_text())
seam = json.loads((folder / "seam-results.json").read_text())
outer = json.loads((folder / "outer-results.json").read_text())

assert rank_two["loewner_rank_two_necessary_conditions_survive"]
assert len(rank_two["records"]) == 6
assert all(record["bernstein"]["negative"] == 0 for record in rank_two["records"].values())
assert determinant["records"]["dH_det"]["bernstein"]["count"] == 10_375
assert determinant["records"]["dH_det"]["bernstein"]["negative"] == 0
assert determinant["records"]["dH_det"]["bernstein"]["zero"] == 0
assert seam["records"]["dH_det"]["bernstein"]["negative"] == 0
assert outer["records"]["dH_det"]["bernstein"]["negative"] == 0
print("verified: every principal-minor certificate is strictly positive")
