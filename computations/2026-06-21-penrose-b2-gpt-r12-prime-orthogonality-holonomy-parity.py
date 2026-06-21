#!/usr/bin/env python3
import cmath
import math


def defect(z):
    return abs(1 - z)


def row(name, phi):
    h = cmath.exp(1j * phi)
    return name, defect(h), defect(h * h), abs(h) ** 2


def main():
    print("NODE test: orientation-reversing holonomy can close only after two traversals")
    print("ResearchNode mutation: Source-B-only even positivity can miss one-pass signed holonomy")
    print()
    print("case | one-pass defect | two-pass defect | even magnitude reporter")
    print("-----|-----------------|-----------------|----------------------")
    cases = [
        ("orientable H=+1", 0.0),
        ("quarter-turn H=i", math.pi / 2),
        ("third-turn", math.pi / 3),
        ("nonorientable H=-1", math.pi),
    ]
    for name, phi in cases:
        _, d1, d2, even = row(name, phi)
        print(f"{name:20s} | {d1:15.6f} | {d2:15.6f} | {even:22.6f}")
    print()
    print("Step-12 boundary sweep: two-pass false closure")
    print("phi/pi | one-pass defect | two-pass defect")
    print("-------|-----------------|----------------")
    for frac in [0.0, 0.25, 0.5, 0.75, 1.0]:
        phi = math.pi * frac
        print(f"{frac:6.2f} | {defect(cmath.exp(1j * phi)):15.6f} | {defect(cmath.exp(2j * phi)):14.6f}")
    print()
    print("Finding:")
    print("  A prime-side-only positive reporter that is even under holonomy can certify")
    print("  two-pass closure while missing one-pass orientation reversal. Prime-side")
    print("  orthogonality should require a holonomy-parity passport: either preserve the")
    print("  odd/one-pass sector or prove it vanishes before claiming RH-equivalence.")


if __name__ == "__main__":
    main()
