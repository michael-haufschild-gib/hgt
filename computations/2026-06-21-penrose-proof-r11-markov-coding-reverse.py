#!/usr/bin/env python3
"""Reverse-method NODE check for Markov coding in dynamical zeta functions.

This is expected to be a dead-end overlap unless it produces more than the
known faithful-index warning: admissible invertible recoding preserves index,
non-generating projection/merging can change counts.
"""

from __future__ import annotations

import numpy as np


def trace_counts(A: np.ndarray, nmax: int = 8) -> list[int]:
    return [int(round(np.trace(np.linalg.matrix_power(A, n)))) for n in range(1, nmax + 1)]


def main() -> None:
    # Full 2-state golden mean shift.
    A = np.array([[1, 1], [1, 0]], dtype=int)

    # Edge shift coding: states are allowed directed edges of A.
    edges = [(i, j) for i in range(2) for j in range(2) if A[i, j]]
    B = np.zeros((len(edges), len(edges)), dtype=int)
    for e, (_, j) in enumerate(edges):
        for f, (j2, _) in enumerate(edges):
            if j == j2:
                B[e, f] = 1

    # Non-generating one-state merge: forget which state was occupied and keep
    # only total outgoing multiplicity.  This is not conjugate to the shift.
    C = np.array([[2]], dtype=int)

    print("NODE reverse check: admissible recoding versus non-generating merge")
    print(f"A={A.tolist()}, trace_counts={trace_counts(A)}")
    print(f"edge_shift_B={B.tolist()}, trace_counts={trace_counts(B)}")
    print(f"bad_merge_C={C.tolist()}, trace_counts={trace_counts(C)}")
    print(f"A_and_B_same_counts={trace_counts(A) == trace_counts(B)}")
    print(f"A_and_C_same_counts={trace_counts(A) == trace_counts(C)}")

    print()
    print("Proof-route transfer audit:")
    print(
        "The reverse transfer is the known one: faithful index data may be "
        "changed by non-injective coding/projection but is invariant under "
        "invertible recoding/congruence. This overlaps existing Sylvester and "
        "reporter-projection warnings, so it should not be counted."
    )


if __name__ == "__main__":
    main()
