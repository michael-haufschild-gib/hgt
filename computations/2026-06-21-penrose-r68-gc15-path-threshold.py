#!/usr/bin/env python3
"""R68: path-dependent thresholds are not G-C15 equivalence.

NODE: sol-gel transition may be gradual/path-dependent, not a sharp boundary.

Target: G-C15 one object, two entrances.  Right theorem required: two entrance
coordinates must read the same intrinsic object/index, not merely show similar
thresholds under one path.
"""

from __future__ import annotations

import numpy as np


def lev(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_validation() -> None:
    print("\nNODE validation: path-dependent apparent gel point")
    xs = np.linspace(0, 1, 11)
    up = 1 / (1 + np.exp(-14 * (xs - 0.58)))
    down = 1 / (1 + np.exp(-14 * (xs - 0.42)))
    up_cross = xs[np.argmax(up > 0.5)]
    down_cross = xs[np.argmax(down > 0.5)]
    print(f"  up-ramp apparent transition    x={up_cross:.2f}")
    print(f"  down-ramp apparent transition  x={down_cross:.2f}")


def target_test() -> None:
    print("\nTarget test: same intrinsic index, path-dependent readout thresholds")
    print("  path   parameter  intrinsic_neg  entrance_A  entrance_B")
    for path, lag_a, lag_b in [("up", 0.08, -0.03), ("down", -0.05, 0.07)]:
        for x in [0.35, 0.45, 0.50, 0.55, 0.65]:
            eig = x - 0.5
            intrinsic = int(eig < 0)
            # Two noisy/lagged entrance readouts.
            entrance_a = int((x - 0.5 + lag_a) < 0)
            entrance_b = int((x - 0.5 + lag_b) < 0)
            print(f"  {path:4s}    {x:6.2f}        {intrinsic:2d}          {entrance_a:2d}          {entrance_b:2d}")


def main() -> None:
    node = "the sol-gel transition may be gradual and path-dependent rather than a sharp thermodynamic phase boundary"
    attempts = [
        "G-C15 needs object-level equivalence not matching gradual thresholds",
        "two entrances can have path-dependent transition lags",
        "right theorem is shared index not synchronized route onset",
    ]
    print("R68 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    node_validation()
    target_test()

    print("\nInterpretation:")
    print("  The right G-C15 theorem must identify a shared intrinsic carrier/index.")
    print("  Path-dependent threshold agreement between entrances is not evidence.")


if __name__ == "__main__":
    main()
