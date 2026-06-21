#!/usr/bin/env python3
"""THE-MACHINE NODE test.

NODE: parameter signs matter in ultradiscrete limits because the standard
epsilon-log max-plus limit assumes positivity/subtraction-free expressions.
"""

import math


def eps_log_abs_sum(A, B, sign_b, eps, delta=0.0):
    """epsilon * log | exp(A/eps) + sign_b * exp((B+delta)/eps) |."""
    x = math.exp(A / eps)
    y = sign_b * math.exp((B + delta) / eps)
    z = abs(x + y)
    if z == 0.0:
        return float("-inf")
    return eps * math.log(z)


def main():
    eps_values = [0.50, 0.25, 0.125, 0.0625, 0.03125]
    cases = [
        ("positive unequal", 3.0, 1.0, +1, 0.0),
        ("positive tie", 2.0, 2.0, +1, 0.0),
        ("negative unequal", 3.0, 1.0, -1, 0.0),
        ("negative exact tie", 2.0, 2.0, -1, 0.0),
        ("negative near tie", 2.0, 2.0, -1, -0.20),
    ]
    print("NODE ultradiscrete sign constraint")
    print("case eps values -> limit-estimates ; max(A,B)")
    for label, A, B, sign_b, delta in cases:
        vals = [eps_log_abs_sum(A, B, sign_b, eps, delta=delta) for eps in eps_values]
        rendered = " ".join("-inf" if v == float("-inf") else f"{v:.6f}" for v in vals)
        print(f"{label:18s} {rendered} ; max={max(A, B + delta):.6f}")
    print("interpretation: positive/subtraction-free cases converge to max; opposite-sign ties collapse and require a sign/parity carrier.")


if __name__ == "__main__":
    main()
