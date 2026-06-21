#!/usr/bin/env python3
"""PS4 inverse transform applied to an HD3 Li gauge shift.

PS4 uses

    lambda_n = sum_{j=1}^n (-1)^(j+1) binom(n,j) P_j

with inverse

    P_j = sum_{n=1}^j (-1)^(n+1) binom(j,n) lambda_n.

The HD3 gauge F_c=exp(c(s-1/2)^2) xi shifts log-defined Li coefficients
by c n^2.  This script records the resulting ghost power sums.
"""

from __future__ import annotations

from math import comb


def ghost_power(j: int) -> int:
    """Coefficient of c in the inverse PS4 image of n^2."""

    return sum(((-1) ** (n + 1)) * comb(j, n) * n * n for n in range(1, j + 1))


def forward_lambda(n: int, ghosts: dict[int, int]) -> int:
    """Recover lambda_n/c from finite ghost P_j coefficients."""

    return sum(((-1) ** (j + 1)) * comb(n, j) * ghosts.get(j, 0) for j in range(1, n + 1))


def main() -> None:
    print("PS4 inverse of the HD3 Li gauge shift delta lambda_n = c n^2")
    print("=" * 70)
    print("j   delta P_j / c")
    ghosts: dict[int, int] = {}
    for j in range(1, 11):
        value = ghost_power(j)
        ghosts[j] = value
        print(f"{j:2d}  {value:4d}")

    print()
    print("Nonzero ghost support:")
    for j, value in ghosts.items():
        if value:
            print(f"  delta P_{j} = ({value}) c")

    print()
    print("Forward check using only delta P_1=c and delta P_2=-2c:")
    finite_ghosts = {1: 1, 2: -2}
    print("n   recovered delta lambda_n / c   n^2")
    for n in range(1, 11):
        recovered = forward_lambda(n, finite_ghosts)
        print(f"{n:2d}  {recovered:6d}                    {n*n:3d}")

    print()
    print(
        "Interpretation: a zero-free HD3 gauge produces no divisor change, "
        "but blind PS4 inversion reads its Li shift as ghost ordinary "
        "power sums P_1 and P_2."
    )


if __name__ == "__main__":
    main()
