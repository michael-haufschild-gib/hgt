#!/usr/bin/env python3
import cmath
import math


def circle(center, radius, samples):
    return [
        center + radius * cmath.exp(2j * math.pi * k / samples)
        for k in range(samples + 1)
    ]


def unwrap_delta(a, b):
    d = b - a
    while d <= -math.pi:
        d += 2 * math.pi
    while d > math.pi:
        d -= 2 * math.pi
    return d


def contour_winding_for_zeros(contour, zeros):
    total = 0.0
    for z0 in zeros:
        args = [cmath.phase(z - z0) for z in contour]
        total += sum(unwrap_delta(a, b) for a, b in zip(args, args[1:]))
    return total / (2 * math.pi)


def main():
    print("Step 9 small cases: faithful integer index versus measured off-line density")
    print("toy divisor: many on-line zeros plus one off-line FE pair")
    print()

    a = 0.18
    gamma = 3.5
    off_pair = [a + 1j * gamma, -a + 1j * gamma]
    local_contour = circle(1j * gamma, radius=0.25, samples=720)

    for n_on in [10, 100, 1000, 10000]:
        on_line = [1j * (k + 1) for k in range(n_on)]
        zeros = on_line + off_pair
        measured_offline_density = len(off_pair) / len(zeros)
        kappa_minus = 1
        local_winding = contour_winding_for_zeros(local_contour, zeros)
        print(
            f"N_on={n_on:5d}  measured_offline_density={measured_offline_density:.6e}  "
            f"local_contour_winding={local_winding:.6f}  kappa_minus={kappa_minus}"
        )

    print()
    print("control: remove the off-line pair")
    for n_on in [10, 1000]:
        zeros = [1j * (k + 1) for k in range(n_on)]
        local_winding = contour_winding_for_zeros(local_contour, zeros)
        print(f"N_on={n_on:5d}  local_contour_winding={local_winding:.6f}  kappa_minus=0")


if __name__ == "__main__":
    main()
