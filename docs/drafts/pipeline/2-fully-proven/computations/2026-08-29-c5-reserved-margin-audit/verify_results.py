#!/usr/bin/env python3
"""Structural verifier for downloaded reserved-margin audit artifacts."""

from __future__ import annotations

import json
import sys
from pathlib import Path


def main(folder: Path) -> None:
    data = json.loads((folder / "results.json").read_text())
    summary = data["summary"]
    assert summary["count"] > 100000
    assert summary["structural_failures"] == 0
    assert summary["robust_negative"]["full"] == 0
    assert float(summary["max_identity_relative_error"]["value"]) < 1e-35
    print("verification passed")


if __name__ == "__main__":
    main(Path(sys.argv[1] if len(sys.argv) > 1 else "."))
