#!/usr/bin/env python3
import cmath
import math


def log_step(value, center, target, terms=80):
    """Continue log from center to target by the local series at center."""
    ratio = (target - center) / center
    increment = 0j
    power = 1 + 0j
    for n in range(1, terms + 1):
        power *= ratio
        increment += ((-1) ** (n + 1)) * power / n
    return value + increment, abs(ratio)


def continue_path(points, terms=80):
    value = 0j
    max_ratio = 0.0
    ratios = []
    for center, target in zip(points, points[1:]):
        value, ratio = log_step(value, center, target, terms)
        ratios.append(ratio)
        max_ratio = max(max_ratio, ratio)
    return value, max_ratio, ratios


def circular_points(radius, start_angle, stop_angle, steps):
    return [
        radius * cmath.exp(1j * (start_angle + (stop_angle - start_angle) * j / steps))
        for j in range(steps + 1)
    ]


def fmt(z):
    return f"{z.real:+.12f}{z.imag:+.12f}i"


def main():
    print("NODE test: Weierstrass continuation by overlapping log-germ power series")
    print("constraint: each step must satisfy |target-center| < distance(center, 0)")
    print()

    print("closed loop around the singular point 0")
    for steps in [6, 8, 12, 24, 48, 96]:
        pts = circular_points(1.0, 0.0, 2 * math.pi, steps)
        val, max_ratio, _ = continue_path(pts, terms=100)
        err = abs(val - 2j * math.pi)
        print(
            f"steps={steps:3d}  max_overlap_ratio={max_ratio:.6f}  "
            f"final={fmt(val)}  |final-2pi i|={err:.3e}"
        )

    print()
    print("same endpoint, different chains")
    upper, upper_ratio, _ = continue_path(circular_points(1.0, 0.0, math.pi, 48), terms=100)
    lower, lower_ratio, _ = continue_path(circular_points(1.0, 0.0, -math.pi, 48), terms=100)
    print(f"upper half-chain to -1: final={fmt(upper)}  max_ratio={upper_ratio:.6f}")
    print(f"lower half-chain to -1: final={fmt(lower)}  max_ratio={lower_ratio:.6f}")
    print(f"branch gap upper-lower={fmt(upper-lower)}  |gap-2pi i|={abs((upper-lower)-2j*math.pi):.3e}")

    print()
    print("invalid one-step jump from 1 to -1")
    ratio = abs((-1 - 1) / 1)
    print(f"overlap_ratio={ratio:.1f}; the local series is outside its disk of convergence")
    for terms in [5, 10, 20, 40]:
        val, _ = log_step(0j, 1 + 0j, -1 + 0j, terms=terms)
        print(f"terms={terms:2d}  partial_sum={fmt(val)}  magnitude={abs(val):.3e}")


if __name__ == "__main__":
    main()
