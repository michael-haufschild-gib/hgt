#!/usr/bin/env python3
"""R67: transient lubrication as a faithful-index warning.

NODE: slime/EPS layers can act as transient lubricants.

Target: G-C10 source-built faithful-index object.  Representation change:
model lubrication as a transient positive regularizer Q -> Q + eps(t) I.
If the negative index disappears only while eps is present, the source object
has not forced faithful positivity.
"""

from __future__ import annotations

from math import exp

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
    print("\nNODE validation: transient lubrication lowers effective drag")
    base_drag = 1.0
    for t in [0, 1, 2, 4, 8, 12]:
        eps = 0.8 * exp(-t / 4.0)
        drag = base_drag / (1.0 + eps)
        print(f"  t={t:2d}: lubricant={eps:.4f}, effective_drag={drag:.4f}")


def neg_index(vals: np.ndarray, tol: float = 1e-10) -> int:
    return int(np.sum(vals < -tol))


def target_test() -> None:
    base = np.diag([-0.08, 0.04, 0.25, 0.70, 1.10])
    print("\nTarget test: transient regularizer hides faithful index")
    print("  eps      neg_index  min_eig   trace")
    for eps in [0.20, 0.10, 0.08, 0.05, 0.02, 0.00]:
        vals = np.linalg.eigvalsh(base + eps * np.eye(base.shape[0]))
        print(f"  {eps:5.2f}       {neg_index(vals):2d}      {vals[0]: .4f}  {np.trace(base + eps*np.eye(5)): .4f}")


def main() -> None:
    node = "slime or EPS layers acting as transient lubricants"
    attempts = [
        "transient regularization can hide a faithful index defect",
        "lubricated source positivity is not source-built rigidity",
        "changing representation exposes index hidden by smoothing layer",
    ]
    print("R67 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    node_validation()
    target_test()

    print("\nInterpretation:")
    print("  A temporary positive layer can erase the measured negative direction")
    print("  without changing the underlying faithful index. This is the known")
    print("  trace/regularization warning for G-C10/G-C18.")


if __name__ == "__main__":
    main()
