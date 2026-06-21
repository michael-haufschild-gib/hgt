#!/usr/bin/env python3
"""
Finite check for the FE-orbit quotient moment dictionary.

For an even product Xi(w)=prod_[a] (1 - w^2/a^2)^m, define
Phi(z)=Xi(sqrt(z)).  If l_k=[z^k] log Phi(z), then the bridge
reciprocal trace moments are T_k=-2*k*(-1)^k*l_k.
"""

from fractions import Fraction


def finite_orbits():
    # Use rational w^2 values directly; the actual roots are the FE pairs +/-w.
    return [
        (Fraction(-4, 1), 1),   # on-line-style pair w=+/-2i
        (Fraction(9, 1), 2),    # real-axis toy pair w=+/-3
        (Fraction(3, 2), 1),    # generic finite algebraic placeholder
    ]


def log_phi_coeff(k, orbits):
    # Phi(z)=prod (1-z/a2)^m, so log coeff is -1/k sum m*a2^(-k).
    return -sum(Fraction(m, 1) * a2 ** (-k) for a2, m in orbits) / k


def bridge_moment(k, orbits):
    # Each FE orbit contributes two original zeros at y=-1/a2.
    return 2 * sum(Fraction(m, 1) * (-a2 ** -1) ** k for a2, m in orbits)


def main():
    orbits = finite_orbits()
    print("FE orbit quotient moment dictionary")
    print("orbits are listed by a2=w^2 and quotient multiplicity m")
    for a2, m in orbits:
        print(f"  a2={a2}, m={m}, reciprocal y={-a2**-1}")
    print()
    print("k  [z^k]logPhi        -2*k*(-1)^k*l_k     T_k")
    for k in range(1, 7):
        ell = log_phi_coeff(k, orbits)
        recovered = -2 * k * ((-1) ** k) * ell
        moment = bridge_moment(k, orbits)
        print(f"{k}  {str(ell):>16}  {str(recovered):>20}  {moment}")
        assert recovered == moment
    print()
    print("Conclusion:")
    print("  Phi(z)=Xi(sqrt(z)) carries quotient multiplicity m on each [w].")
    print("  The bridge sequence T_k is the doubled trace over the original")
    print("  FE pair, recovered from log Phi by T_k=-2*k*(-1)^k*[z^k]logPhi.")


if __name__ == "__main__":
    main()
