#!/usr/bin/env python3
"""Verify route conclusions of the CLG first-atom base computation."""

from __future__ import annotations

import json
import sys
from pathlib import Path


def main() -> None:
    root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(".")
    result = json.loads((root / "results.json").read_text())
    structure = result["structure"]
    assert structure["P0_factor_identity_exact"] is True
    assert structure["P2_mixed_sign"] is True
    assert structure["seam_first_nonzero_order"] == 7
    assert structure["seam_polynomial_shift_A6_all_positive"] is True
    assert not result["deterministic"]["negative_margin"]
    assert not result["randomized"]["negative_margin"]
    assert not result["deterministic"]["nonnegative_center_numerator"]
    assert not result["randomized"]["nonnegative_center_numerator"]
    print("verified: seam order-seven coefficient is positive; P2 termwise sign route is killed; no base-margin counterexample found")


if __name__ == "__main__":
    main()
