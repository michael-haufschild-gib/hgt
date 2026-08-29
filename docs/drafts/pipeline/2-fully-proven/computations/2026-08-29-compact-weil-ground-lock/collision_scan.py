#!/usr/bin/env python3
"""Hostile close-pair scan for compact-Weil ground locking."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp
from flint import arb

from ground_lock import (
    compute_ground,
    load_zeros,
    midpoint_text,
    root_lock_statistics,
    tail_for_vector,
)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--zeros", type=Path, required=True)
    parser.add_argument("--L", default="1.4")
    parser.add_argument("--modes", type=int, default=119)
    parser.add_argument("--ground-zeros", type=int, default=800)
    parser.add_argument("--tail-zeros", type=int, default=200)
    parser.add_argument("--pair-left", type=int, default=27,
                        help="one-based index of left member")
    parser.add_argument("--digits", type=int, default=180)
    parser.add_argument("--threads", type=int, default=32)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    original = load_zeros(args.zeros, args.ground_zeros + args.tail_zeros)
    mp.mp.dps = args.digits
    left_index = args.pair_left - 1
    left = mp.mpf(original[left_index])
    original_right = mp.mpf(original[left_index + 1])
    original_gap = original_right - left
    deltas = [
        ("original", original_gap),
        ("1", mp.mpf("1")),
        ("1e-1", mp.mpf("1e-1")),
        ("1e-2", mp.mpf("1e-2")),
        ("1e-4", mp.mpf("1e-4")),
        ("1e-8", mp.mpf("1e-8")),
        ("1e-9", mp.mpf("1e-9")),
        ("3e-10", mp.mpf("3e-10")),
        ("1e-10", mp.mpf("1e-10")),
        ("3e-11", mp.mpf("3e-11")),
        ("1e-11", mp.mpf("1e-11")),
        ("3e-12", mp.mpf("3e-12")),
        ("1e-12", mp.mpf("1e-12")),
        ("1e-14", mp.mpf("1e-14")),
        ("1e-16", mp.mpf("1e-16")),
        ("1e-32", mp.mpf("1e-32")),
        ("1e-64", mp.mpf("1e-64")),
    ]
    results: list[dict[str, object]] = []
    for label, delta in deltas:
        modified = list(original)
        modified[left_index + 1] = mp.nstr(left + delta, args.digits)
        rayleigh, vector, _, timings = compute_ground(
            args.L,
            args.modes,
            modified[: args.ground_zeros],
            args.digits,
            args.threads,
        )
        tail = tail_for_vector(args.L, vector, modified[args.ground_zeros :])
        total = rayleigh + tail
        vector_text = [midpoint_text(entry, args.digits - 10) for entry in vector]
        locking = root_lock_statistics(
            args.L, vector_text, modified, min(args.digits - 10, 170)
        )
        pair_records = locking["records"][left_index : left_index + 2]
        results.append({
            "delta_label": label,
            "delta": mp.nstr(delta, 50),
            "fixed_vector_total": midpoint_text(total, args.digits - 10),
            "minus_log_fixed_vector_total": midpoint_text(-total.log(), 40),
            "matched_root_count": locking["matched_root_count"],
            "max_gap_normalized_offset": locking["max_gap_normalized_offset"],
            "pair_records": pair_records,
            "timings": timings,
        })
        print(label, results[-1]["minus_log_fixed_vector_total"],
              results[-1]["matched_root_count"],
              [(record["root_found"], record["gap_normalized_offset"])
               for record in pair_records], flush=True)

    payload = {
        "L": args.L,
        "modes": args.modes,
        "pair_left_index": args.pair_left,
        "left_ordinate": mp.nstr(left, 50),
        "original_gap": mp.nstr(original_gap, 50),
        "results": results,
    }
    args.out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
