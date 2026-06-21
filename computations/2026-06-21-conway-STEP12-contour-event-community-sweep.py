#!/usr/bin/env python3
"""Step 12 sweep for contour event-community diagnostics."""

from __future__ import annotations

import importlib.util
import pathlib
import sys


BASE = pathlib.Path(__file__).with_name("2026-06-21-conway-contour-event-community.py")
spec = importlib.util.spec_from_file_location("event_community", BASE)
mod = importlib.util.module_from_spec(spec)
sys.modules["event_community"] = mod
spec.loader.exec_module(mod)


def main() -> None:
    zero1 = 14.134725141734693790457251983562
    rects = {
        "contains_zero": (0.45, 0.55, zero1 - 0.11, zero1 + 0.11),
        "near_right_nozero": (0.5005, 0.62, zero1 - 0.11, zero1 + 0.11),
        "far_right_nozero": (0.62, 0.82, zero1 - 0.11, zero1 + 0.11),
        "wide_contains": (0.2, 0.8, zero1 - 0.11, zero1 + 0.11),
    }
    print("STEP12: contour event-community boundary sweep")
    print("k rect winding side_entropy largest_side_share clusters longest_cluster side_counts")
    for k in [8, 16, 28, 40, 64]:
        for name, rect in rects.items():
            row = mod.contour_events(rect, k_events=k)
            print(
                f"{k:02d} {name:17s} {row['winding']:+.3f} {row['side_entropy']:.3f} "
                f"{row['largest_side_share']:.3f} {row['clusters']:02d} "
                f"{row['longest_cluster']:02d} {row['side_counts']}"
            )
        print()


if __name__ == "__main__":
    main()
