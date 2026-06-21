#!/usr/bin/env python3
"""
R35 STEP 11: right theorem check.

The transfer appears to be exactly the finite orbit-balance / augmentation
kernel theorem: a divisor is balanced iff each orbit degree is zero.
"""

from __future__ import annotations

from collections import defaultdict

import numpy as np


def profile(divisor: list[tuple[int, int]]) -> dict[int, int]:
    out: dict[int, int] = defaultdict(int)
    for orbit, coeff in divisor:
        out[orbit] += coeff
    return {k: v for k, v in sorted(out.items()) if v}


def main() -> None:
    rng = np.random.default_rng(3511)
    print("trial total_degree profile_zero scalar_zero classification")
    misses = 0
    for trial in range(20):
        divisor = [(int(rng.integers(0, 5)), int(rng.choice([-2, -1, 1, 2]))) for _ in range(8)]
        total = sum(c for _, c in divisor)
        prof_zero = not profile(divisor)
        scalar_zero = total == 0
        if scalar_zero and not prof_zero:
            misses += 1
        cls = "balanced" if prof_zero else "unbalanced"
        print(f"{trial:5d} {total:12d} {int(prof_zero):12d} {int(scalar_zero):11d} {cls}")
    print(f"\nscalar_zero_but_profile_unbalanced={misses}/20")
    print(
        "Right theorem: the augmentation kernel is per orbit, not global. "
        "This is already the target theorem, so the analogy adds no new result."
    )


if __name__ == "__main__":
    main()
