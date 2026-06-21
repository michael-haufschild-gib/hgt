#!/usr/bin/env python3
"""
Follow-up to the hard-edge boundary-extension obstruction.

Finite-rank boundary theorem for a positive bulk B:

    H = B + V C V*

where B > 0, C is an invertible Hermitian boundary matrix, and V contains
boundary channel vectors.  The block Schur complement gives

    inertia(H) = inertia(B) + inertia(-C^{-1} - V*B^{-1}V) - inertia(-C^{-1}).

When C is negative definite (a destabilizing hard-edge boundary extension),
-C^{-1} is positive definite, so

    kappa_-(H) = kappa_-(-C^{-1} - V*B^{-1}V).

Thus the faithful negative index is carried by the small boundary Weyl matrix,
not by the already-positive bulk.
"""

from __future__ import annotations

import numpy as np


def hard_edge_bulk(n: int, bessel_g: float) -> np.ndarray:
    h = 1.0 / (n + 1)
    main = np.full(n, 2.0 / (h * h))
    off = np.full(n - 1, -1.0 / (h * h))
    mat = np.diag(main) + np.diag(off, 1) + np.diag(off, -1)
    x = h * np.arange(1, n + 1)
    mat += np.diag(bessel_g / (x * x))
    return mat


def inertia(a: np.ndarray, tol: float = 1e-8) -> tuple[int, int, int]:
    vals = np.linalg.eigvalsh((a + a.T) / 2.0)
    return (
        int(np.sum(vals < -tol)),
        int(np.sum(np.abs(vals) <= tol)),
        int(np.sum(vals > tol)),
    )


def inertia_sub(x: tuple[int, int, int], y: tuple[int, int, int]) -> tuple[int, int, int]:
    return (x[0] - y[0], x[1] - y[1], x[2] - y[2])


def inertia_add(x: tuple[int, int, int], y: tuple[int, int, int]) -> tuple[int, int, int]:
    return (x[0] + y[0], x[1] + y[1], x[2] + y[2])


def main() -> None:
    rng = np.random.default_rng(20260621)
    n = 70
    m = 4
    bulk = hard_edge_bulk(n, bessel_g=0.75)

    # Boundary channels concentrated near the hard edge, then orthonormalized.
    raw = np.zeros((n, m))
    for j in range(m):
        raw[: 8 + 2 * j, j] = rng.normal(size=8 + 2 * j)
        raw[:, j] *= np.exp(-np.arange(n) / (2.0 + j))
    v, _ = np.linalg.qr(raw)
    v = v[:, :m]

    q = v.T @ np.linalg.solve(bulk, v)
    q = (q + q.T) / 2.0

    print("=== finite-rank boundary Schur reduction for kappa_- ===")
    print(f"bulk inertia: {inertia(bulk)}")
    print(f"boundary channel count m={m}")
    print()
    eig, u = np.linalg.eigh(q)
    factors = np.array([0.45, 0.75, 1.15, 1.80])

    print("q eigenvalues:", ", ".join(f"{x:.3e}" for x in eig))
    print("boundary factors:", ", ".join(f"{x:.2f}" for x in factors))
    print()
    print("scale   inertia(H)    predicted by Schur      neg(boundary Weyl)")

    # C is negative definite.  The scale moves the boundary through several
    # Schur eigenvalue crossings while B and V stay fixed.
    for scale in [0.40, 0.60, 0.80, 1.00, 1.20, 1.40, 1.80, 2.40]:
        # In the q-eigenbasis, the ith boundary channel crosses when
        # scale * factors[i] = 1.
        c_diag = -(scale * factors) / eig
        c = u @ np.diag(c_diag) @ u.T
        h = bulk + v @ c @ v.T
        t = -np.linalg.inv(c)
        boundary_weyl = t - q
        predicted = inertia_sub(
            inertia_add(inertia(bulk), inertia(boundary_weyl)),
            inertia(t),
        )
        print(
            f"{scale:4.2f}    {inertia(h)!s:14s} {predicted!s:22s}"
            f"{inertia(boundary_weyl)[0]}"
        )

    print()
    print("interpretation:")
    print("- With positive bulk and negative boundary matrix, kappa_-(H) is exactly")
    print("  the negative index of the finite boundary Weyl matrix -C^-1 - V*B^-1V.")
    print("- For source-built kappa_-, a proof can target the completed boundary")
    print("  Weyl inequality instead of treating the whole bulk form as mysterious.")


if __name__ == "__main__":
    main()
