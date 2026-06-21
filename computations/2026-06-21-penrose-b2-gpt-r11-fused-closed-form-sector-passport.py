#!/usr/bin/env python3
import cmath
import math


def holonomy(a):
    return cmath.exp(2j * math.pi * a)


def branch_value(x, n):
    return math.log(x) + 2j * math.pi * n


def branch_derivative(x, n):
    return 1.0 / x


def main():
    print("NODE test: compact U(1) can have large-gauge copies even in an Abelian theory")
    print("Gauge condition dA=0 is satisfied by every constant representative a+n on S^1.")
    print()
    a0 = 0.37
    print("n | representative a+n | |holonomy(a+n)-holonomy(a)| | in fundamental [0,1)?")
    print("--|--------------------|-----------------------------|----------------------")
    for n in range(-2, 3):
        rep = a0 + n
        diff = abs(holonomy(rep) - holonomy(a0))
        in_fundamental = 0 <= rep < 1
        print(f"{n:2d} | {rep:18.2f} | {diff:27.3e} | {str(in_fundamental):>20s}")
    print()
    print("ResearchNode mutation: fused closed form under branch/sector copies")
    print("Local derivative checks cannot see additive 2*pi*i branch sectors.")
    print()
    x = 0.7
    principal = branch_value(x, 0)
    print("n | derivative check | value error versus principal")
    print("--|------------------|----------------------------")
    for n in range(-2, 3):
        derivative_ok = abs(branch_derivative(x, n) - branch_derivative(x, 0)) < 1e-15
        value_error = abs(branch_value(x, n) - principal)
        print(f"{n:2d} | {str(derivative_ok):>16s} | {value_error:26.12f}")
    print()
    print("Step-12 follow-up: certification strength")
    print("n | derivative only accepts? | derivative + basepoint accepts?")
    print("--|--------------------------|-------------------------------")
    for n in range(-2, 3):
        derivative_ok = abs(branch_derivative(x, n) - branch_derivative(x, 0)) < 1e-15
        basepoint_ok = abs(branch_value(x, n) - principal) < 1e-15
        print(f"{n:2d} | {str(derivative_ok):>24s} | {str(derivative_ok and basepoint_ok):>29s}")
    print()
    print("Finding:")
    print("  A theorem-grade fused closed form needs a sector passport: branch choices,")
    print("  large-gauge/winding constants, contour homotopy class, and residue conventions.")
    print("  Matching derivatives, asymptotics, or local expansions does not certify exact")
    print("  equality of the fused value.")


if __name__ == "__main__":
    main()
