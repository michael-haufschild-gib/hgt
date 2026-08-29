#!/usr/bin/env python3
"""Independent consistency checks for the C5 tangent-reserve artifact."""

from __future__ import annotations

import json
import sys
from pathlib import Path


def main(folder: Path) -> None:
    data = json.loads((folder / "results.json").read_text())
    for name in ("deterministic", "randomized"):
        summary = data[name]
        assert not summary["nonpositive_atom_margin"]
        assert not summary["nonpositive_tangent_reserve"]
        assert not summary["nonpositive_full_margin"]
        assert not summary["robust_negative_convexity_gap"]
        assert float(summary["minimum_reserve_ratio"]) > 0
        assert float(summary["maximum_tax_ratio"]) < 1
    print("verified: atom-tangent reserve survived; convex tangent bridge remains open")


if __name__ == "__main__":
    main(Path(sys.argv[1]) if len(sys.argv) > 1 else Path("."))
