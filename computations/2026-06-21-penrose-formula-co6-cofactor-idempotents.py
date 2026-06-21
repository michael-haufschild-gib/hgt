#!/usr/bin/env python3
"""Workflow test for CO6 through ligand/cofactor-stabilized symmetry.

ResearchNode formula:
    g_p = g_p^{-1} implies g_p = ±1

Random NODE:
    Metal ions, cofactors, or ligands can stabilize symmetry that the apo
    protein does not maintain.
"""

from __future__ import annotations

import itertools
import numpy as np


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, start=1):
        cur = [i]
        for j, cb in enumerate(b, start=1):
            cur.append(
                min(
                    prev[j] + 1,
                    cur[-1] + 1,
                    prev[j - 1] + (ca != cb),
                )
            )
        prev = cur
    return prev[-1]


def apo_holo_minimizer(a: float, k: float) -> tuple[float, float]:
    """Minimize (x-a)^2+(y+a)^2+k(x-y)^2."""
    mat = np.array([[1 + k, -k], [-k, 1 + k]], dtype=float)
    rhs = np.array([a, -a], dtype=float)
    x, y = np.linalg.solve(mat, rhs)
    return float(x), float(y)


def product_ring_involutions(n: int) -> list[tuple[int, ...]]:
    return list(itertools.product([-1, 1], repeat=n))


def idempotent_to_involution(e: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(2 * x - 1 for x in e)


def matrix_involution_from_projector(theta: float) -> tuple[np.ndarray, np.ndarray]:
    v = np.array([np.cos(theta), np.sin(theta)])
    p = np.outer(v, v)
    g = 2 * p - np.eye(2)
    return p, g


def main() -> None:
    base_test = "test ligand cofactor stabilizes symmetry missing in apo protein"
    attempts = [
        (
            "A",
            "test coefficient idempotent cofactor stabilizes selfinverse signs",
        ),
        (
            "B",
            "test matrix projector cofactor stabilizes involution symmetry",
        ),
        (
            "C",
            "test product-sector cofactor changes scalar plusminus solutions",
        ),
    ]
    print("STEP 8 Levenshtein transfer attempts")
    print("=" * 42)
    scored = [(tag, levenshtein(base_test, text), text) for tag, text in attempts]
    for tag, score, text in scored:
        print(f"{tag}: distance={score}, attempt={text}")
    chosen = min(scored, key=lambda row: row[1])
    print(f"chosen={chosen[0]} by minimum distance")
    print()

    print("NODE test: cofactor strength restores near-symmetry")
    print("=" * 52)
    for k in [0, 0.1, 1, 10, 1_000_000]:
        x, y = apo_holo_minimizer(a=1.0, k=k)
        print(
            f"k={k:>9g}: x={x:+.9f}, y={y:+.9f}, "
            f"|x-y|={abs(x-y):.9e}"
        )

    print()
    print("STEP 9 method 10: matrix-projector cofactor extremes")
    print("=" * 58)
    for theta in [0.0, np.pi / 8, np.pi / 4]:
        proj, g = matrix_involution_from_projector(theta)
        err = np.linalg.norm(g @ g - np.eye(2))
        scalar_pm_err = min(np.linalg.norm(g - np.eye(2)), np.linalg.norm(g + np.eye(2)))
        print(
            f"theta={theta:.6f}: ||g^2-I||={err:.3e}, "
            f"distance_to_±I={scalar_pm_err:.6f}"
        )
        print(f"  projector=\n{proj}")
        print(f"  g=2P-I=\n{g}")

    print()
    print("Commutative boundary case: product coefficient hosts")
    print("=" * 56)
    for n in [1, 2, 3, 4]:
        invs = product_ring_involutions(n)
        global_pm = [tuple([1] * n), tuple([-1] * n)]
        non_global = [g for g in invs if g not in global_pm]
        print(
            f"R=C^{n}: #{{g:g^2=1}}={len(invs)}, "
            f"non-global ±1 solutions={len(non_global)}"
        )
        if non_global:
            print(f"  example non-global involution: {non_global[0]}")

    print()
    print("Idempotent parametrization in characteristic not 2:")
    for e in [(0, 0), (1, 1), (1, 0), (0, 1)]:
        g = idempotent_to_involution(e)
        print(f"e={e} -> g=2e-1={g}, g^2={tuple(x*x for x in g)}")

    print()
    print("Interpretation:")
    print(
        "The scalar implication g=g^{-1} => g=±1 requires a connected/"
        "idempotent-free coefficient host. After a product-sector cofactor "
        "extension, self-inverse units are sectorwise signs, not only global ±1."
    )


if __name__ == "__main__":
    main()
