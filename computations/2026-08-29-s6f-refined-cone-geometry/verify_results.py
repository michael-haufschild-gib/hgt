#!/usr/bin/env python3
"""Structural checks for refined-cone exact coefficient output."""

from __future__ import annotations

import json
import sys
from pathlib import Path


folder = Path(sys.argv[1] if len(sys.argv) > 1 else ".")
data = json.loads((folder / "results.json").read_text())
records = data["records"]
assert records["value"]["bernstein"]["negative"] == 0
assert records["value"]["bernstein"]["zero"] == 0
assert records["dS"]["bernstein"]["negative"] == 0
assert records["dS"]["bernstein"]["zero"] == 0
assert records["d2W"]["bernstein"]["positive"] == 0
assert data["faces"]["outer_negative_derivative"]["bernstein"]["negative"] == 0
assert data["faces"]["outer_negative_derivative"]["bernstein"]["zero"] == 0
assert data["seam_independent_of_eta"]
assert data["seam_sign"] == "positive"
print("verified: refined D1 direct signs and boundary records are internally consistent")
