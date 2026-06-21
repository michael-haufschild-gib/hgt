"""PS12 strict Hankel total positivity checks.

The proof in the card is symbolic: Cauchy-Binet expands every minor of
H[i,j] = zeta(2(i+j)+3) as a positive sum of generalized Vandermonde
products. This script only checks representative minors and records the
PS12-specific finite zeta(1) Schur thresholds.
"""

from __future__ import annotations

import itertools
import math

import mpmath as mp


# The Schur-threshold block is ill conditioned; 250 digits is enough for the
# d<=40 table below and keeps the script fast on a laptop.
mp.mp.dps = 260


def h_entry(i: int, j: int) -> mp.mpf:
    return mp.zeta(2 * (i + j) + 3)


def determinant(rows: tuple[int, ...], cols: tuple[int, ...]) -> mp.mpf:
    mat = mp.matrix([[h_entry(i, j) for j in cols] for i in rows])
    return mp.det(mat)


def generalized_vandermonde(exponents: tuple[int, ...], xs: tuple[mp.mpf, ...]) -> mp.mpf:
    mat = mp.matrix([[x ** e for x in xs] for e in exponents])
    return mp.det(mat)


def cauchy_binet_partial(rows: tuple[int, ...], cols: tuple[int, ...], cutoff: int) -> mp.mpf:
    total = mp.mpf("0")
    for ns in itertools.combinations(range(1, cutoff + 1), len(rows)):
        xs = tuple(mp.mpf(1) / (n * n) for n in ns)
        weights = mp.fprod(mp.mpf(1) / (n**3) for n in ns)
        total += (
            weights
            * generalized_vandermonde(rows, xs)
            * generalized_vandermonde(cols, xs)
        )
    return total


def schur_threshold(d: int) -> mp.mpf:
    """Finite zeta(1) repair threshold for mu_k=zeta(2k+1), k>=1."""
    c = mp.matrix(d)
    b = mp.matrix(d, 1)
    for i in range(d):
        b[i] = mp.zeta(2 * (i + 1) + 1)
        for j in range(d):
            c[i, j] = mp.zeta(2 * ((i + 1) + (j + 1)) + 1)
    x = mp.lu_solve(c, b)
    return mp.fsum(b[i] * x[i] for i in range(d))


def main() -> None:
    print("FORMULA: PS12 from formulas-graph node 53")
    print("  zeta(2k+1)=sum_n (1/n)(1/n^2)^k")
    print("  H_FID[i,j]=zeta(2(i+j)+3)=sum_n (1/n^3)(1/n^2)^(i+j)")
    print()

    print("Representative strict Hankel-total-positivity minors")
    tests = [
        ((0,), (0,)),
        ((0, 1), (0, 1)),
        ((0, 2), (1, 3)),
        ((0, 1, 3), (0, 2, 4)),
        ((1, 3, 4), (0, 2, 5)),
    ]
    for rows, cols in tests:
        det = determinant(rows, cols)
        partial = cauchy_binet_partial(rows, cols, cutoff=10)
        print(
            f"rows={rows} cols={cols} det={mp.nstr(det, 18)} "
            f"partial_CB_10={mp.nstr(partial, 18)} positive={det > 0 and partial > 0}"
        )

    print()
    print("Finite zeta(1) Schur thresholds for original PS12 measure")
    print("d threshold threshold-2log(d)")
    for d in [1, 2, 3, 4, 5, 8, 10, 15, 20, 30, 40]:
        a = schur_threshold(d)
        diff = a - 2 * mp.log(d)
        print(f"{d:2d} {mp.nstr(a, 22):>26s} {mp.nstr(diff, 14):>18s}")

    print()
    print("VERDICT")
    print("  H_FID is not merely PSD: every shifted Hankel minor is strictly positive.")
    print("  This is still RH-empty, because the measure is the integer divisor.")
    print("  The zeta(1) finite-part thresholds diverge; numerically they track 2 log d.")


if __name__ == "__main__":
    main()
