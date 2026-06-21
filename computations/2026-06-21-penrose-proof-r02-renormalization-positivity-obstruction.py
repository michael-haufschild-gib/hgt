#!/usr/bin/env python3
import numpy as np


def eigvals_2x2(a, b, c):
    return np.linalg.eigvalsh(np.array([[a, b], [b, c]], dtype=float))


def main():
    print("ResearchNode: bridge theorem completion + explicit formula + pole cancellation => Stieltjes")
    print("NODE constraint: renormalization is a positivity-preserving change of description,")
    print("not merely subtraction of infinities.")
    print()
    print("Essential countermodel:")
    print("  cutoff positive measure mu_L = L*delta_0 + delta_1")
    print("  raw moments: m0=L+1, m1=1, m2=1")
    print("  raw Hankel [[m0,m1],[m1,m2]] is PSD for every L>0.")
    print("  naive pole cancellation subtracts the divergent zeroth mass and sets m0^ren=0.")
    print()
    print("L | raw eigmin | ren eigmin | ren determinant")
    print("--|------------|------------|----------------")
    for L in [1, 10, 100, 1000]:
        raw_eigs = eigvals_2x2(L + 1, 1, 1)
        ren_eigs = eigvals_2x2(0, 1, 1)
        ren_det = -1.0
        print(f"{L:4.0f} | {raw_eigs[0]:10.6f} | {ren_eigs[0]:10.6f} | {ren_det:14.6f}")
    print()
    print("Quadratic form check for p(y)=a+b*y:")
    print("  raw Q_L(1,-1)=L >= 0")
    print("  ren Q(1,-1)=0 - 2 + 1 = -1")
    print()
    print("Finding:")
    print("  Pole cancellation/finiteness alone does not imply Stieltjes positivity.")
    print("  A bridge theorem must prove that the completion/explicit-formula cancellation")
    print("  acts as a positive map on squares, or it must work in the shifted finite")
    print("  moment space where the infinite mass at y=0 has been removed before testing.")


if __name__ == "__main__":
    main()
