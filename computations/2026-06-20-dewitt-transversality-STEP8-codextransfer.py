#!/usr/bin/env python3
# RUNNABLE test of a HYPERTRANSCENDENTAL value constraint.
# Function: Gamma(x), a classical hypertranscendental function.
# Constraint: Euler reflection is a VALUE RELATION on paired values:
#     Gamma(x) * Gamma(1-x) * sin(pi*x) = pi
# This is not a dependency, deduction, or causality test. It checks that jointly sampled
# function values satisfy a rigid algebraic/trigonometric relation.

import math
import random

TOL = 1e-11

def reflection_residual(x):
    lhs = math.gamma(x) * math.gamma(1.0 - x) * math.sin(math.pi * x)
    return lhs, lhs - math.pi

def duplication_residual(x):
    # Legendre duplication is a second value relation:
    # Gamma(x) * Gamma(x + 1/2) = 2^(1-2x) * sqrt(pi) * Gamma(2x)
    lhs = math.gamma(x) * math.gamma(x + 0.5)
    rhs = (2.0 ** (1.0 - 2.0 * x)) * math.sqrt(math.pi) * math.gamma(2.0 * x)
    return lhs, rhs, lhs - rhs

print("=== HYPERTRANSCENDENTAL NODE test: Gamma value constraints ===")
print("Constraint A: Gamma(x) * Gamma(1-x) * sin(pi*x) = pi")
print("  x          | lhs                         | residual")

xs = [-2.7, -1.4, -0.6, 0.1, 0.25, 0.5, 0.73, 1.3, 2.8, 4.2]
for x in xs:
    lhs, err = reflection_residual(x)
    print(f"  {x:+.6f} | {lhs:+.16e} | {err:+.3e}")
    assert abs(err) < TOL

print("\nConstraint B: Gamma(x) * Gamma(x+1/2) = 2^(1-2x) * sqrt(pi) * Gamma(2x)")
print("  x          | lhs                         | rhs                         | residual")

ys = [0.1, 0.25, 0.5, 0.9, 1.2, 2.5, 4.0, 7.3]
for x in ys:
    lhs, rhs, err = duplication_residual(x)
    rel = abs(err) / max(1.0, abs(lhs), abs(rhs))
    print(f"  {x:+.6f} | {lhs:+.16e} | {rhs:+.16e} | {err:+.3e}")
    assert rel < TOL

print("\n=== randomized value-relation checks ===")
rng = random.Random(12345)
max_reflection_error = 0.0
max_duplication_rel_error = 0.0

for _ in range(100):
    x = rng.uniform(-6.0, 6.0)
    if abs(x - round(x)) < 1e-6:
        continue
    lhs, err = reflection_residual(x)
    max_reflection_error = max(max_reflection_error, abs(err))
    assert abs(err) < 1e-9

for _ in range(100):
    x = rng.uniform(0.05, 8.0)
    lhs, rhs, err = duplication_residual(x)
    rel = abs(err) / max(1.0, abs(lhs), abs(rhs))
    max_duplication_rel_error = max(max_duplication_rel_error, rel)
    assert rel < 1e-11

print(f"  max reflection absolute residual: {max_reflection_error:.3e}")
print(f"  max duplication relative residual: {max_duplication_rel_error:.3e}")
print("\nConstraint validated ON NODE: Gamma values obey rigid hypertranscendental value relations.")
