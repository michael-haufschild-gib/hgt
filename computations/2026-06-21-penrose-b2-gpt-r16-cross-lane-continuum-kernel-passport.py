#!/usr/bin/env python3
import math
import numpy as np


def interval_kernel(x, y, ell=0.2):
    return math.exp(-abs(x - y) / ell)


def cyclic_kernel(x, y, ell=0.2):
    d = abs(x - y)
    return math.exp(-min(d, 1.0 - d) / ell)


def max_error(xs, kernel):
    errs = []
    for x in xs:
        for y in xs:
            errs.append(abs(kernel(x, y) - interval_kernel(x, y)))
    return max(errs)


def main():
    print("NODE test: finite/discrete spectra can create recurrence artifacts")
    print("ResearchNode mutation: finite sigma-lane matrices need a continuum-kernel passport")
    print()
    print("Compare true interval kernel exp(-|s-s'|/ell) with cyclic finite-lane kernel.")
    print("The cyclic kernel is a recurrence/boundary artifact if sigma lanes live on an interval.")
    print()
    print("N lanes | true edge K(0,1) | cyclic edge K(0,1) | max cyclic error")
    print("--------|------------------|--------------------|-----------------")
    for n in [5, 9, 17, 33]:
        xs = np.linspace(0.0, 1.0, n)
        true_edge = interval_kernel(0.0, 1.0)
        cyclic_edge = cyclic_kernel(0.0, 1.0)
        err = max_error(xs, cyclic_kernel)
        print(f"{n:7d} | {true_edge:16.6f} | {cyclic_edge:18.6f} | {err:15.6f}")
    print()
    print("Step-12 follow-up: correct topology under refinement")
    print("N lanes | max interval-sampled error against itself")
    print("--------|-----------------------------------------")
    for n in [5, 9, 17, 33]:
        xs = np.linspace(0.0, 1.0, n)
        err = max_error(xs, interval_kernel)
        print(f"{n:7d} | {err:39.6f}")
    print()
    print("Finding:")
    print("  A cross-lane association matrix is not yet a continuum operator K(sigma,sigma').")
    print("  It needs a continuum-kernel passport: boundary topology, refinement behavior,")
    print("  recurrence/alias tests, and convergence of kernel values under lane densification.")


if __name__ == "__main__":
    main()
