#!/usr/bin/env python3
"""
Height-tail exponents for reciprocal seam square tests.

For Q_r[p] with r=1 (Q0) or r=2 (Q1), and p(y)=y^j q(y),
the high-zero tail is governed by gamma^(-alpha), alpha=2r+4j.
The Riemann-von Mangoldt density contributes the extra log(G).
"""

import math


def model_tail(alpha: int, G: float) -> float:
    """Integral of t^(-alpha) log(t) from G to infinity."""
    return G ** (1 - alpha) * (math.log(G) / (alpha - 1) + 1 / (alpha - 1) ** 2)


def main():
    print("gamma_tail_square_tests")
    print("model density: dN(t) ~ const * log(t) dt")
    print()
    for r, name in [(1, "Q0"), (2, "Q1")]:
        for j in range(3):
            alpha = 2 * r + 4 * j
            exponent = 1 - alpha
            print(f"{name}, ord_0(p)=j={j}:")
            print(f"  alpha = 2*r + 4*j = {alpha}")
            print(f"  tail = O(G^{exponent} log G)")
            for G in [10.0, 100.0, 1000.0]:
                print(f"    smooth integral at G={G:g}: {model_tail(alpha, G):.6e}")
            print()
    print("Route consequence:")
    print("  The slowest convergent square-test tail is Q0 with p(0) != 0:")
    print("  O(G^-1 log G).  Q1 with p(0) != 0 is already O(G^-3 log G),")
    print("  and each hard-edge zero of p improves the exponent by four powers of G.")


if __name__ == "__main__":
    main()
