#!/usr/bin/env python3
"""
R41 STEP 11: weaken FID volume positivity to projected-tail positivity.

Raw Hankel determinants collapse because kappa_n=zeta(2n+1)->1, giving a
rank-one bulk. Remove the all-ones direction and inspect the tail cone.
"""

from __future__ import annotations

import mpmath as mp
import numpy as np

mp.mp.dps = 80


def kappa(n: int) -> float:
    return float(mp.zeta(2 * n + 1))


def hankel(size: int) -> np.ndarray:
    return np.array([[kappa(i + j + 1) for j in range(size)] for i in range(size)], dtype=float)


def orth_complement_ones(size: int) -> np.ndarray:
    one = np.ones((size, 1))
    q, _ = np.linalg.qr(np.eye(size) - one @ one.T / size)
    # QR includes one near-null column; keep columns with nonzero projection.
    cols = []
    for j in range(size):
        v = q[:, j]
        if np.linalg.norm(v) > 1e-8 and abs(np.dot(v, np.ones(size))) < 1e-8:
            cols.append(v)
    return np.column_stack(cols[: size - 1])


def main() -> None:
    print("size raw_min_eig projected_min_eig projected_max_eig projected_cond")
    for size in range(3, 9):
        h = hankel(size)
        raw = np.linalg.eigvalsh(h)
        q = orth_complement_ones(size)
        p = q.T @ h @ q
        eig = np.linalg.eigvalsh(p)
        cond = eig[-1] / eig[0] if eig[0] > 0 else np.inf
        print(f"{size:4d} {raw[0]:12.4g} {eig[0]:17.6g} {eig[-1]:17.6g} {cond:14.3e}")
    print(
        "\nInterpretation: weakening to the nontrivial tail removes the rank-one bulk but "
        "does not remove the thin-cone problem; the projected tail is still rapidly ill-conditioned."
    )


if __name__ == "__main__":
    main()
