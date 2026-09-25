#!/usr/bin/env python3
"""Verify route-level conclusions of the S6F structural computation."""

from __future__ import annotations

import json
import sys
from pathlib import Path


def main() -> None:
    root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(".")
    result = json.loads((root / "results.json").read_text())
    assert result["chain_rule_identity_exact"] is True
    assert all(result["sl2_relations_exact"].values())
    layers = result["coefficientwise_matrix_bernstein"]["layers"]
    assert sorted(map(int, layers)) == list(range(6))
    assert layers["2"]["negative_leading_pivots"][1:] == [286, 286]
    assert layers["3"]["negative_leading_pivots"][2] == 273
    assert result["coefficientwise_matrix_bernstein"]["survives"] is False
    print("verified: exact sl2 structure survives; coefficientwise matrix-Bernstein Gram is killed")


if __name__ == "__main__":
    main()
