#!/usr/bin/env python3
"""Verify route-level conclusions of likelihood interpolation computation."""

from __future__ import annotations

import json
import sys
from pathlib import Path


def main() -> None:
    root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(".")
    result = json.loads((root / "results.json").read_text())
    for name in ("deterministic", "randomized"):
        record = result[name]
        assert not record["negative_margin"]
        assert record["robust_negative_derivative"] > 0
        assert record["robust_positive_derivative"] > 0
        assert record["robust_negative_second"] == 0
        assert record["robust_positive_second"] > 0
    assert result["deterministic"]["interior_below_both_endpoints"] > 0
    print("verified: interpolation margin survived; monotone likelihood improvement is killed")


if __name__ == "__main__":
    main()
