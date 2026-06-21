#!/usr/bin/env python3
"""STEP 11: strengthen the SOC/C4 timescale-separation conjecture."""

from __future__ import annotations


def main() -> None:
    rows = []
    with open("computations/2026-06-21-conway-STEP12-soc-c4-resolution-battery.txt", "r", encoding="utf-8") as fh:
        for line in fh:
            if not line.startswith("["):
                continue
            parts = line.split()
            window = parts[0]
            q = float(parts[1])
            gap = int(parts[2])
            true_span = int(parts[3])
            finite_span = int(parts[4])
            random_span = int(parts[5])
            true_area = int(parts[6])
            finite_area = int(parts[7])
            random_area = int(parts[8])
            rows.append((window, q, gap, true_span, finite_span, random_span, true_area, finite_area, random_area))

    print("STEP 11 METHOD 15: STRENGTHEN THE CONJECTURE")
    print("Strengthened gate: at gap=0, every q in {0.70,0.78,0.85} and every window must have true_span=7 and true_area > 1.5*finite_area and > 5*random_area.")
    failures = []
    passes = 0
    total = 0
    for row in rows:
        window, q, gap, ts, fs, rs, ta, fa, ra = row
        if gap != 0:
            continue
        total += 1
        ok = ts == 7 and ta > 1.5 * max(fa, 1) and ta > 5.0 * max(ra, 1)
        passes += int(ok)
        if not ok:
            failures.append((window, q, ts, fs, rs, ta, fa, ra))
    print(f"passes={passes}/{total}")
    print("failures:")
    for f in failures:
        print(
            f"window={f[0]} q={f[1]:.2f} true_span={f[2]} finite_span={f[3]} random_span={f[4]} "
            f"true_area={f[5]} finite_area={f[6]} random_area={f[7]}"
        )
    print()
    print("Verdict: strengthened threshold-uniform C4 avalanche gate fails. The observed event-sheet signal is threshold-sensitive and cannot be promoted as a new C4 result.")


if __name__ == "__main__":
    main()
