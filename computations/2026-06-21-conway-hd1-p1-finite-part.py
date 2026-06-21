#!/usr/bin/env python3
"""HD1 audit: P_1 is a Hadamard finite part.

The ordinary power sums over zeros are absolutely convergent for k >= 2.
For k = 1, the unpaired absolute series diverges; the coefficient P_1 of
-xi'/xi at s=0 is the Hadamard/genus-one finite part -b.
"""

from __future__ import annotations

import mpmath as mp


mp.mp.dps = 50


def p1_closed() -> mp.mpf:
    # From xi'/xi at s=0:
    # xi'/xi(0) = -1 - gamma/2 + log(2*sqrt(pi)).
    return 1 + mp.euler / 2 - mp.log(2 * mp.sqrt(mp.pi))


def main() -> None:
    target = p1_closed()
    print("HD1 P_1 finite-part audit")
    print("=" * 44)
    print(f"P_1^Had = -b = 1 + gamma/2 - log(2 sqrt(pi))")
    print(f"           {mp.nstr(target, 30)}")
    print()
    print("N   paired partial sum 2 Re(1/rho_n)      abs partial sum 2|1/rho_n|")
    paired = mp.mpf("0")
    abs_sum = mp.mpf("0")
    checkpoints = {5, 10, 20, 50, 100}
    for n in range(1, max(checkpoints) + 1):
        rho = mp.zetazero(n)
        paired += 2 * mp.re(1 / rho)
        abs_sum += 2 * abs(1 / rho)
        if n in checkpoints:
            print(
                f"{n:3d} {mp.nstr(paired, 28):>34} "
                f"{mp.nstr(abs_sum, 28):>34}"
            )

    print()
    print("Read:")
    print("  The paired symmetric sum drifts toward the finite part.")
    print("  The unpaired absolute sum keeps growing, so P_1 is not an")
    print("  ordinary absolutely convergent zero sum.")
    print("  For k >= 2, dyadic zero counting gives absolute convergence.")


if __name__ == "__main__":
    main()
