#!/usr/bin/env python3
"""
NODE experiment: finite Gram determinants and positive-definite kernels.

Constraint under test:
  K is positive definite only if every finite Gram matrix [K(x_i,x_j)]
  is PSD for every finite node set.  Pairwise checks are not enough.

Test kernel:
  K_tau(x,y)=1+x*y-tau*x^2*y^2 on [-1,1].
For small positive tau, all sampled 2x2 tests pass while a 3x3 test fails.
"""

import itertools
import numpy as np


def k_bad(x, y, tau=0.1):
    return 1.0 + x * y - tau * x * x * y * y


def k_good(x, y):
    return 1.0 + x * y + 0.1 * x * x * y * y


def gram(xs, kernel):
    return np.array([[kernel(x, y) for y in xs] for x in xs], dtype=float)


def min_eig(xs, kernel):
    return float(np.linalg.eigvalsh(gram(xs, kernel))[0])


def det(xs, kernel):
    return float(np.linalg.det(gram(xs, kernel)))


def scan_subsets(grid, size, kernel):
    best = (float("inf"), None, None)
    for xs in itertools.combinations(grid, size):
        eig = min_eig(xs, kernel)
        determinant = det(xs, kernel)
        if eig < best[0]:
            best = (eig, determinant, xs)
    return best


def main():
    grid = np.linspace(-1.0, 1.0, 41)
    print("NODE: positive-definite kernel requires all finite Gram tests")
    print("bad kernel: K_tau(x,y)=1+x*y-0.1*x^2*y^2")
    print("good control: K_+(x,y)=1+x*y+0.1*x^2*y^2")
    print()
    for name, kernel in [("bad", k_bad), ("good", k_good)]:
        print(f"{name} kernel scan on 41-point grid")
        for size in [2, 3, 4]:
            eig, determinant, xs = scan_subsets(grid, size, kernel)
            print(
                f"  size={size}: min_eig={eig:+.12e} det={determinant:+.12e} nodes={tuple(round(float(x), 3) for x in xs)}"
            )
        print()

    xs = (-1.0, 0.0, 1.0)
    mat = gram(xs, k_bad)
    print("explicit failing 3-point Gram matrix for bad kernel at (-1,0,1):")
    for row in mat:
        print("  " + " ".join(f"{v:+.6f}" for v in row))
    print(f"  eigenvalues={np.linalg.eigvalsh(mat)}")
    print(f"  determinant={np.linalg.det(mat):+.12e}")
    print()

    print("Interpretation:")
    print("  Pairwise Gram positivity is a false shortcut.  The defining constraint")
    print("  is universal over finite subsets; the first failure can occur at size 3")
    print("  even when every sampled 2x2 determinant is nonnegative.")


if __name__ == "__main__":
    main()
