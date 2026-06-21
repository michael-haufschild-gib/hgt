"""PA9 Turan ratio: split universal Newton floor from source residual.

This script consumes the existing validated PA9 ratio artifact rather than
recomputing Xi Taylor coefficients. The proof card supplies the theorem; this
file only prints the floor-divided interpretation of the prior numbers.
"""

from __future__ import annotations

import re
from pathlib import Path


SOURCE = Path("computations/2026-06-21-connes-turan-normalized-margin.txt")


def load_ratios() -> list[tuple[int, float]]:
    ratios: list[tuple[int, float]] = []
    pattern = re.compile(r"^\s*(\d+)\s+([0-9.]+)\s+")
    for line in SOURCE.read_text().splitlines():
        match = pattern.match(line)
        if match:
            ratios.append((int(match.group(1)), float(match.group(2))))
    if not ratios:
        raise RuntimeError(f"no ratios parsed from {SOURCE}")
    return ratios


def main() -> None:
    print("FORMULA: PA9 from formulas-graph node 34")
    print("  g(n)=a_n^2/(a_{n-1}a_{n+1}) -> 1, with g(n)-1 ~ c/n")
    print("  Newton floor for elementary-symmetric / LP coefficients: (n+1)/n")
    print(f"  source ratios: {SOURCE}")
    print()
    print("n g(n) floor g/floor-1 n*(g-1)-1")
    for n, g in load_ratios():
        floor = (n + 1) / n
        residual = g / floor - 1
        debiased_constant = n * (g - 1) - 1
        print(
            f"{n:2d} {g:16.9f} {floor:14.9f} "
            f"{residual:16.9f} {debiased_constant:16.9f}"
        )

    print()
    print("VERDICT")
    print("  The leading 1/n in PA9 is not source-specific; it is the Newton/binomial floor.")
    print("  Source-specific Turan evidence starts at g(n)/((n+1)/n)-1, equivalently n*(g-1)-1 at first order.")


if __name__ == "__main__":
    main()
