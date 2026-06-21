#!/usr/bin/env python3
"""Extreme-case audit for hidden support versus source-built positivity.

Random NODE: architectural tensegrity, where a visible tensegrity-like object
may actually be stabilized by hidden continuous supports.

Proof-route transfer under test: a completed square-test form must not become
positive only because an unaccounted external PSD support term was added.
"""

from __future__ import annotations

import numpy as np


def inertia(mat: np.ndarray, tol: float = 1e-10) -> tuple[int, int, int]:
    eig = np.linalg.eigvalsh(mat)
    neg = int(np.sum(eig < -tol))
    zero = int(np.sum(np.abs(eig) <= tol))
    pos = int(np.sum(eig > tol))
    return neg, zero, pos


def fmt(name: str, mat: np.ndarray) -> str:
    eig = np.linalg.eigvalsh(mat)
    return (
        f"{name}\n"
        f"matrix=\n{mat}\n"
        f"eigenvalues={np.array2string(eig, precision=6)}\n"
        f"inertia(neg,zero,pos)={inertia(mat)}\n"
    )


def main() -> None:
    # Extreme 1: visible/source form is indefinite.
    source = np.diag([-1.0, 2.0])

    # Extreme 2: uncoupled hidden support cannot repair the visible principal
    # subform; the negative visible direction survives in the direct sum.
    uncoupled_hidden = np.block(
        [
            [source, np.zeros((2, 1))],
            [np.zeros((1, 2)), np.array([[100.0]])],
        ]
    )

    # Extreme 3: coupled/added support on the same visible coordinate can mask
    # the negative source direction.
    support = np.diag([2.0, 0.0])
    completed = source + support

    print("Hidden-support extreme-case audit")
    print("=" * 40)
    print(fmt("source A", source))
    print(fmt("uncoupled A direct-sum hidden support", uncoupled_hidden))
    print(fmt("coupled completed A+R", completed))
    print(fmt("hidden support R", support))

    print("Arbitrary PSD support can force any finite symmetric form PSD:")
    rng = np.random.default_rng(20260621)
    for idx in range(5):
        raw = rng.normal(size=(4, 4))
        a = (raw + raw.T) / 2.0
        lam_min = float(np.linalg.eigvalsh(a)[0])
        alpha = max(0.0, -lam_min) + 1e-6
        r = alpha * np.eye(4)
        c = a + r
        print(
            f"sample {idx}: lambda_min(A)={lam_min:+.6f}, "
            f"alpha={alpha:.6f}, inertia(A)={inertia(a)}, "
            f"inertia(A+alpha I)={inertia(c)}"
        )

    print()
    print("Transfer check:")
    print(
        "PSD of A+R gives no PSD information about A unless R is canonical "
        "source data. Uncoupled hidden support preserves the negative visible "
        "principal subform; coupled support changes the source form itself."
    )


if __name__ == "__main__":
    main()
