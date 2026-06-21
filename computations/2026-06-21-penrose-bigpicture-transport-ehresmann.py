#!/usr/bin/env python3
import cmath
import math


def holonomy(alpha):
    return cmath.exp(-1j * 2 * math.pi * alpha)


def fmt(z):
    return f"{z.real:+.12f}{z.imag:+.12f}i"


def main():
    print("NODE test: flat U(1) circle connections")
    print("local form A = alpha dtheta; curvature on S^1 is zero, but holonomy can be nontrivial")
    print()
    for alpha in [0, 0.125, 0.25, 0.5, 1.25]:
        print(f"alpha={alpha:5.3f}  curvature=0  holonomy={fmt(holonomy(alpha))}")
    print()
    print("gauge shift by an integer m changes the local coefficient but not holonomy")
    alpha = 0.25
    for m in [-2, -1, 0, 1, 2]:
        shifted = alpha + m
        gap = abs(holonomy(shifted) - holonomy(alpha))
        print(f"alpha+m={shifted:+5.2f}  holonomy={fmt(holonomy(shifted))}  |gap|={gap:.3e}")

    print()
    print("attack false: gauge the flat form away")
    print("on an interval, g(theta)=exp(i alpha theta) is allowed and removes A")
    print("on a circle, it is single-valued only if exp(i 2pi alpha)=1")
    for alpha in [0.0, 0.25, 0.5, 1.0]:
        single_valued_gap = abs(cmath.exp(1j * 2 * math.pi * alpha) - 1)
        print(
            f"alpha={alpha:4.2f}  endpoint_gauge_mismatch={single_valued_gap:.3e}  "
            f"circle_holonomy={fmt(holonomy(alpha))}"
        )


if __name__ == "__main__":
    main()
