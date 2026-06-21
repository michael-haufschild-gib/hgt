#!/usr/bin/env python3
"""
R39 STEP 11: visual dust-index warning.
"""

from __future__ import annotations

import numpy as np


def spark(vals: np.ndarray) -> str:
    chars = []
    for v in vals:
        chars.append("!" if v < 0 else ".")
    return "".join(chars)


def main() -> None:
    n = 80
    for eps in [1e-1, 1e-3, 1e-8]:
        eigs = np.ones(n)
        eigs[-1] = -eps
        print(f"eps={eps:.0e} faithful_index=1 spectrum={spark(eigs)} trace_avg={eigs.mean():.8f}")
    print(
        "\nVisual verdict: the faithful index is a one-pixel global sign, while trace-scale "
        "views look almost unchanged. This is the already-stated G-C18 dust obstruction."
    )


if __name__ == "__main__":
    main()
