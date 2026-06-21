#!/usr/bin/env python3
"""
Finite-support witnesses for the source-aware Q0-alone theorem.

The paper proof uses real-symmetric polynomial approximation on the compact
reciprocal support.  In finite support this reduces to interpolation: a real
polynomial can isolate a negative real atom, or isolate a non-real conjugate
pair with a phase that makes Re(y p(y)^2) negative.
"""

import cmath
import numpy as np


def interpolate(values):
    """Return coefficients c_k for p(z)=sum c_k z^k."""
    xs = np.array([z for z, _target in values], dtype=complex)
    ys = np.array([target for _z, target in values], dtype=complex)
    vandermonde = np.vander(xs, N=len(xs), increasing=True)
    coeffs = np.linalg.solve(vandermonde, ys)
    return coeffs


def eval_poly(coeffs, z):
    total = 0j
    power = 1 + 0j
    for coeff in coeffs:
        total += coeff * power
        power *= z
    return total


def q0_value(atoms, weights, coeffs):
    return sum(weight * y * eval_poly(coeffs, y) ** 2 for y, weight in zip(atoms, weights))


def print_poly(label, coeffs):
    max_imag = max(abs(c.imag) for c in coeffs)
    print(label)
    print("  coefficients:")
    for idx, coeff in enumerate(coeffs):
        print(f"    c_{idx} = {coeff.real:.12g} + {coeff.imag:.3e}i")
    print(f"  max imaginary coefficient residue = {max_imag:.3e}")


def negative_real_witness():
    atoms = [-0.4 + 0j, 0.25 + 0j, 1.0 + 0j]
    weights = [1.0, 3.0, 2.0]
    targets = [(-0.4 + 0j, 1.0 + 0j), (0.25 + 0j, 0j), (1.0 + 0j, 0j)]
    coeffs = interpolate(targets)
    value = q0_value(atoms, weights, coeffs)
    print_poly("Negative-real atom isolation", coeffs)
    print(f"  Q0[p] = {value.real:.12g} + {value.imag:.3e}i")
    print("  expected sign: negative, from weight*y at y=-0.4")
    print()


def nonreal_pair_witness():
    y = 0.4 + 1.1j
    phase = cmath.exp(0.5j * (cmath.pi - cmath.phase(y)))
    atoms = [y, y.conjugate(), 0.2 + 0j, 1.3 + 0j]
    weights = [1.0, 1.0, 5.0, 2.0]
    targets = [
        (y, phase),
        (y.conjugate(), phase.conjugate()),
        (0.2 + 0j, 0j),
        (1.3 + 0j, 0j),
    ]
    coeffs = interpolate(targets)
    value = q0_value(atoms, weights, coeffs)
    expected = 2 * (y * phase**2).real
    print_poly("Non-real conjugate-pair isolation", coeffs)
    print(f"  chosen phase z gives Re(y*z^2) = {(y * phase**2).real:.12g}")
    print(f"  Q0[p] = {value.real:.12g} + {value.imag:.3e}i")
    print(f"  expected finite-pair contribution = {expected:.12g}")
    print("  expected sign: negative, so H^(0) cannot be PSD")
    print()


if __name__ == "__main__":
    negative_real_witness()
    nonreal_pair_witness()
    print("Conclusion:")
    print("  In finite divisor models, any bad reciprocal atom has a real polynomial")
    print("  witness with Q0[p] < 0.  The infinite divisor proof replaces exact")
    print("  interpolation by real-symmetric polynomial approximation on the compact")
    print("  reciprocal support, with summability of sum weight*|y| giving passage")
    print("  to the Q0 limit.")
