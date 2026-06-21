#!/usr/bin/env python3
"""
Seam-center uniqueness for the reciprocal bridge coordinate.

Use c=1/2+eps.  An FE pair is w and -w in the true seam coordinate.
The shifted reciprocal atoms are -(w-eps)^(-2) and -(-w-eps)^(-2).
They coincide for every nonzero FE pair only when eps=0.
"""


def reciprocal(z: complex) -> complex:
    return -1.0 / (z * z)


def fe_mismatch(w: complex, eps: float) -> complex:
    return reciprocal(w - eps) - reciprocal(-w - eps)


def fe_mismatch_formula(w: complex, eps: float) -> complex:
    return -4.0 * w * eps / ((w * w - eps * eps) ** 2)


def online_atom(gamma: float, eps: float) -> complex:
    return reciprocal(1j * gamma - eps)


def online_imag_formula(gamma: float, eps: float) -> float:
    denom = (eps * eps - gamma * gamma) ** 2 + 4 * eps * eps * gamma * gamma
    return -2 * eps * gamma / denom


def main():
    w = 0.23 + 14.13j
    gamma = 14.13
    print("seam_center_uniqueness")
    print("FE pair test with w=0.23+14.13i")
    for eps in [0.0, 0.01, 0.05, -0.05]:
        mismatch = fe_mismatch(w, eps)
        formula = fe_mismatch_formula(w, eps)
        y = online_atom(gamma, eps)
        print(f"eps={eps:+.3f}")
        print(f"  |y(w-eps)-y(-w-eps)| = {abs(mismatch):.12e}")
        print(f"  formula error          = {abs(mismatch-formula):.3e}")
        print(f"  RH-line y_eps          = {y.real:+.12e}{y.imag:+.12e}i")
        print(f"  Im formula             = {online_imag_formula(gamma, eps):+.12e}")
    print()
    print("Algebra:")
    print("  -(w-eps)^(-2) = -(-w-eps)^(-2) iff (w-eps)^2=(w+eps)^2")
    print("  iff 4*w*eps=0.  For nonzero zeros, this forces eps=0.")
    print("  For an RH-line zero w=i*gamma, Im[-(i*gamma-eps)^(-2)]")
    print("  equals -2*eps*gamma/((eps^2-gamma^2)^2+4 eps^2 gamma^2),")
    print("  so positive-real reciprocal atoms for all gamma require eps=0.")


if __name__ == "__main__":
    main()
