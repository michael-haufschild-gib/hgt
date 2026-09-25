#!/usr/bin/env python3
"""Independent consistency checks for frontier hostile-computation output."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("result_dir")
    args = parser.parse_args()
    result_dir = Path(args.result_dir)
    result_path = result_dir / "results.json"
    boxes_path = result_dir / "s6f_arb_boxes.jsonl"
    result = json.loads(result_path.read_text())

    s6f = result["s6f_tcd"]
    arb = s6f["arb"]
    assert result["scope"].startswith("diagnostic-only")
    assert s6f["negative_count"] == 0
    assert float(s6f["minimum"][1]) > 0.0
    assert arb["all_positive"]
    assert arb["unresolved_count"] == 0
    assert float(arb["minimum_lower_box"]["lower"]) > 0.0
    assert result["c5"]["negative_count"] == 0
    assert not result["c5"]["errors"]

    records = [json.loads(line) for line in boxes_path.read_text().splitlines()]
    assert len(records) == arb["boxes"]
    assert all(record["positive"] and record["lower"] > 0.0 for record in records)
    assert [record["index"] for record in records] == list(range(arb["boxes"]))

    print("verified: S6F/TCD dense and Arb positivity outputs; C5 scan integrity")
    print("results.json sha256", sha256(result_path))
    print("s6f_arb_boxes.jsonl sha256", sha256(boxes_path))


if __name__ == "__main__":
    main()
