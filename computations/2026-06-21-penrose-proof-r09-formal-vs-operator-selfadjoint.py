#!/usr/bin/env python3
"""NODE validation: formal self-adjointness is not operator self-adjointness.

For -d^2/dx^2 on [0,1], use boundary maps
Gamma0(f)=(f(0),f(1)) and Gamma1(f)=(f'(0),-f'(1)).
Self-adjoint boundary conditions can be encoded by
A Gamma0(f) + B Gamma1(f) = 0.  The boundary subspace is self-adjoint only
when rank(A,B)=2 and A B* = B A*.

This is used here only as a dead-end overlap check for the proof-route
boundary-extension node.
"""

from __future__ import annotations

import numpy as np


def criterion(A: np.ndarray, B: np.ndarray) -> dict[str, object]:
    rank = int(np.linalg.matrix_rank(np.column_stack([A, B])))
    defect = A @ B.T - B @ A.T
    return {
        "rank_AB": rank,
        "ABt_minus_BAt": defect.astype(int).tolist(),
        "self_adjoint_boundary": bool(rank == 2 and np.allclose(defect, 0)),
    }


def main() -> None:
    cases = {
        "dirichlet": (
            np.array([[1, 0], [0, 1]]),
            np.array([[0, 0], [0, 0]]),
        ),
        "neumann": (
            np.array([[0, 0], [0, 0]]),
            np.array([[1, 0], [0, 1]]),
        ),
        "periodic": (
            np.array([[1, -1], [0, 0]]),
            np.array([[0, 0], [1, 1]]),
        ),
        "overfixed_left_endpoint": (
            np.array([[1, 0], [0, 0]]),
            np.array([[0, 0], [1, 0]]),
        ),
    }
    print("NODE experiment: boundary equations for the same formal expression -d^2/dx^2")
    for name, (A, B) in cases.items():
        print(name, criterion(A, B))

    print()
    print("Interpretation:")
    print(
        "The same formally self-adjoint differential expression supports both "
        "self-adjoint and non-self-adjoint operator domains. The missing datum is "
        "not another scalar detector; it is the boundary subspace satisfying the "
        "Green/Lagrange boundary-form condition. For the proof route this restates "
        "the existing boundary-extension/domain obligation for kappa_-."
    )


if __name__ == "__main__":
    main()
