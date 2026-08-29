#!/usr/bin/env python3
"""Independent structural verifier for the fixed-action C5 Jacobian scan."""

from __future__ import annotations

import json
from pathlib import Path


HERE = Path(__file__).resolve().parent


def main() -> None:
    result = json.loads((HERE / "results.json").read_text())
    assert result["scope"] == "diagnostic only; forbidden as input to Lean proofs"
    assert result["parameters"] == {
        "dps": 160,
        "output": "results",
        "random_points": 200_000,
        "seed": 20_260_829,
        "t_points": 900,
        "u_points": 400,
        "workers": 128,
    }
    assert result["grid_shape"] == [579, 1200]
    assert result["grid"]["count"] == 694_800
    assert result["random"]["count"] == 200_000
    for name in ("grid", "random"):
        summary = result[name]
        assert summary["negative_count"] == 0
        assert summary["negative_first_100"] == []
        assert summary["zero_count"] == 0
        assert summary["positive_count"] == summary["count"]
        assert summary["smallest_point"][2] == 1
    print("verified: parameters and 894,800 strictly positive reported Jacobian signs")


if __name__ == "__main__":
    main()
