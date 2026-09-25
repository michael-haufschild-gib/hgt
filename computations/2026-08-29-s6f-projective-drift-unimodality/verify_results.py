#!/usr/bin/env python3
"""Independent structural verifier for downloaded S6F follow-up artifacts."""

from __future__ import annotations

import json
from pathlib import Path


HERE = Path(__file__).resolve().parent


def main() -> None:
    result = json.loads((HERE / "results.json").read_text())
    assert result["scope"] == "diagnostic only; forbidden as input to Lean proofs"
    assert result["parameters"] == {
        "bits": 256,
        "boxes": 27_400,
        "output": "results",
        "points": 2_000_001,
        "workers": 128,
    }
    assert result["dense"]["projective_negative_count"] == 0
    assert result["dense"]["projective_sign_changes"] == []
    assert len(result["dense"]["raw_derivative_sign_changes"]) == 1
    assert len(result["dense"]["raw_second_sign_changes"]) == 1
    assert result["arb"]["source_nonpositive_ranges"] == []
    assert result["arb"]["projective_negative_count"] == 0
    assert result["arb"]["projective_positive_count"] == 26_556
    assert result["arb"]["projective_unresolved_ranges"] == [[0.0, 0.0021100000000000003, 844]]

    records = [json.loads(line) for line in (HERE / "arb_boxes.jsonl").read_text().splitlines()]
    assert len(records) == 27_400
    assert [record["index"] for record in records] == list(range(27_400))
    assert sum(record["projective_sign"] == 1 for record in records) == 26_556
    assert sum(record["projective_sign"] == 0 for record in records) == 844
    assert not any(record["projective_sign"] == -1 for record in records)
    assert not any(record["source_sign"] != 1 for record in records)
    assert all(records[i]["hi"] == records[i + 1]["lo"] for i in range(27_399))
    assert records[0]["lo"] == 0.0
    assert records[-1]["hi"] == 137 / 2000
    print("verified: parameters, summaries, 27,400 ordered Arb boxes, and reported sign counts")


if __name__ == "__main__":
    main()
