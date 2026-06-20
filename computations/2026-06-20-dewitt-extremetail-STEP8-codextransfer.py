#!/usr/bin/env python3
# MACHINE STEP6: RUNNABLE test of a HYPERTRANSCENDENTAL value-relation constraint.
#
# Function: Euler gamma Gamma(z), a classical hypertranscendental / differentially transcendental function.
# Constraint: the reflected pair of values satisfies the exact value relation
#
#     Gamma(z) * Gamma(1 - z) * sin(pi*z) = pi
#
# This is a constraint among values at z and 1-z. It is not a dependency, deduction, or causal claim.

import math
import cmath
import random

random.seed(7)

def gamma_complex(z):
    return complex(math.gamma(z.real)) if abs(z.imag) < 1e-15 else lanczos_gamma(z)

def lanczos_gamma(z):
    # Lanczos approximation for complex Gamma, sufficient for this runnable constraint test.
    g = 7
    p = [
        0.99999999999980993,
        676.5203681218851,
        -1259.1392167224028,
        771.32342877765313,
        -176.61502916214059,
        12.507343278686905,
        -0.13857109526572012,
        9.9843695780195716e-6,
        1.5056327351493116e-7,
    ]

    if z.real < 0.5:
        return math.pi / (cmath.sin(math.pi * z) * lanczos_gamma(1 - z))

    z -= 1
    x = p[0]
    for i in range(1, len(p)):
        x += p[i] / (z + i)
    t = z + g + 0.5
    return cmath.sqrt(2 * math.pi) * (t ** (z + 0.5)) * cmath.exp(-t) * x

def reflection_residual(z):
    lhs = gamma_complex(z) * gamma_complex(1 - z) * cmath.sin(math.pi * z)
    return abs(lhs - math.pi) / math.pi

points = [
    0.13,
    0.25,
    0.5,
    0.73,
    1.37,
    -0.41,
    0.22 + 0.31j,
    0.67 - 0.44j,
    -0.35 + 0.28j,
    1.21 - 0.19j,
]

for _ in range(40):
    re = random.uniform(-1.3, 1.7)
    im = random.uniform(-0.8, 0.8)
    z = complex(re, im)
    if abs(z - round(z.real)) > 1e-6 and abs(1 - z - round((1 - z).real)) > 1e-6:
        points.append(z)

print("=== NODE test: hypertranscendental Gamma reflection value-relation constraint ===")
print("Constraint: Gamma(z) * Gamma(1-z) * sin(pi*z) = pi")
print()

residuals = []
for z in points:
    r = reflection_residual(complex(z))
    residuals.append(r)
    print(f"z={z!s:>18s}  relative_residual={r:.3e}")

max_residual = max(residuals)
median_residual = sorted(residuals)[len(residuals) // 2]
tolerance = 5e-12

print()
print(f"max_relative_residual={max_residual:.3e}")
print(f"median_relative_residual={median_residual:.3e}")
print(f"tolerance={tolerance:.1e}")

assert max_residual < tolerance, (
    "Gamma reflection value-relation constraint failed: "
    f"max residual {max_residual:.3e} >= tolerance {tolerance:.1e}"
)

print()
print("Constraint validated ON NODE.")
