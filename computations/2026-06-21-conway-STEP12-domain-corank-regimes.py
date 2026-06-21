#!/usr/bin/env python3
"""STEP 12 stress for domain-invariance corank leakage.

The exact finite-window formula is:
  internal_existing_prime(N,T) = T / (N + T)
for total-degree <= T monomials in N prime-log variables. This script checks
asymptotic regimes and the bigraded extension.
"""

from __future__ import annotations

import math


def internal(n: float, t: float) -> float:
    return t / (n + t) if t > 0 else 0.0


def main() -> None:
    print("STEP 12 domain-invariance corank regimes")
    print("Formula: internal_existing_prime(N,T)=T/(N+T); leak=1-internal.")
    print()
    print("REGULAR AXIS REGIMES")
    print("N T_rule T internal leak verdict")
    for n in [10, 100, 1000, 10000]:
        rules = [
            ("fixed_2", 2.0),
            ("sqrtN", math.sqrt(n)),
            ("N", float(n)),
            ("NlogN", float(n) * math.log(n)),
            ("N2", float(n * n)),
        ]
        for label, t in rules:
            inn = internal(n, t)
            leak = 1.0 - inn
            if leak > 0.9:
                verdict = "anti-invariant"
            elif leak > 0.4:
                verdict = "boundary-heavy"
            else:
                verdict = "degree-rich"
            print(f"{n:05d} {label:8s} {t:.3f} {inn:.6f} {leak:.6f} {verdict}")

    print()
    print("BIGRADED AXIS CHECK")
    print("N T M U prime_internal exp_internal prime_leak exp_leak")
    for n, t, m, u in [
        (20, 2, 20, 2),
        (100, 2, 20, 2),
        (100, 10, 20, 2),
        (100, 100, 20, 2),
        (100, 10, 100, 10),
        (100, 1000, 100, 1000),
    ]:
        pi = internal(float(n), float(t))
        ei = internal(float(m), float(u))
        print(f"{n:03d} {t:04d} {m:03d} {u:04d} {pi:.6f} {ei:.6f} {1-pi:.6f} {1-ei:.6f}")

    print()
    print(
        "Interpretation: finite graded corank windows are invariant-domain "
        "approximations only in a degree-rich limit T/N -> infinity. In the "
        "prime-first limit N -> infinity at fixed T, the window is almost all "
        "boundary. Adding a new prime outside a finite cutoff still has leak 1, "
        "so finite N windows cannot model the full prime-log algebra domain."
    )


if __name__ == "__main__":
    main()
