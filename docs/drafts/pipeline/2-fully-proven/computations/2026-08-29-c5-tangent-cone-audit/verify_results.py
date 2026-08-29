#!/usr/bin/env python3
"""Structural verifier for downloaded tangent-cone audit artifacts."""

from __future__ import annotations

import json
import sys
from pathlib import Path


def main(folder: Path) -> None:
    data = json.loads((folder / "results.json").read_text())
    summary = data["summary"]
    assert summary["count"] > 100000
    assert summary["sign_failures"] == 0
    assert summary["actual_tangent_failures"] == 0
    assert set(summary["vertex_counts"]).issubset(set(data["formal_cone"]["extreme_rays"]))
    assert float(summary["min_actual_tangent_ratio"]["value"]) > 0
    print("verification passed")


if __name__ == "__main__":
    main(Path(sys.argv[1] if len(sys.argv) > 1 else "."))
