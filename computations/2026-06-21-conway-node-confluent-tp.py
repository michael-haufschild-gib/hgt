#!/usr/bin/env python3
"""
NODE experiment: multiple nodes in determinant limits for a TP kernel.

Kernel: K(x,y)=exp(x*y), a classical strictly totally positive kernel on
ordered real nodes.  When y-nodes coalesce, det[K(x_i,y_j)] must vanish at
the Vandermonde rate, and the normalized determinant must tend to the
confluent derivative determinant.
"""

import math
import numpy as np


def kernel(x, y):
    return math.exp(x * y)


def matrix(xs, ys):
    return np.array([[kernel(x, y) for y in ys] for x in xs], dtype=float)


def vandermonde(vals):
    prod = 1.0
    for i in range(len(vals)):
        for j in range(i + 1, len(vals)):
            prod *= vals[j] - vals[i]
    return prod


def confluent_target(xs, y0):
    n = len(xs)
    mat = np.zeros((n, n), dtype=float)
    for i, x in enumerate(xs):
        for j in range(n):
            mat[i, j] = (x ** j) * math.exp(x * y0) / math.factorial(j)
    return np.linalg.det(mat)


def slope(xs, ys):
    xbar = sum(xs) / len(xs)
    ybar = sum(ys) / len(ys)
    num = sum((x - xbar) * (y - ybar) for x, y in zip(xs, ys))
    den = sum((x - xbar) ** 2 for x in xs)
    return num / den


def main():
    xs = [0.2, 0.8, 1.4, 2.1]
    y0 = 0.3
    offsets = [0.0, 1.0, 2.0, 4.0]
    n = len(xs)
    exponent = n * (n - 1) // 2
    target = confluent_target(xs, y0)

    print("NODE: confluent determinant limit for K(x,y)=exp(x*y)")
    print(f"ordered xs={xs}")
    print(f"coalescing y_j = {y0} + eps*{offsets}")
    print(f"expected raw determinant exponent: eps^{exponent}")
    print(f"confluent derivative determinant target: {target:.15e}")
    print()
    print("eps det raw_det_abs normalized_det rel_error")
    log_eps = []
    log_abs = []
    for eps in [1e-1, 5e-2, 2e-2, 1e-2, 5e-3, 2e-3, 1e-3]:
        ys = [y0 + eps * r for r in offsets]
        raw = np.linalg.det(matrix(xs, ys))
        vy = vandermonde(ys)
        normalized = raw / vy
        rel = abs(normalized - target) / abs(target)
        print(f"{eps:.1e} {raw:+.15e} {abs(raw):.15e} {normalized:+.15e} {rel:.3e}")
        log_eps.append(math.log(eps))
        log_abs.append(math.log(abs(raw)))
    print()
    print(f"estimated log-log raw determinant slope: {slope(log_eps, log_abs):.6f}")
    print()

    ys_exact_duplicate = [y0, y0, y0 + 0.01, y0 + 0.02]
    raw_duplicate = np.linalg.det(matrix(xs, ys_exact_duplicate))
    print("exact duplicate-node check:")
    print(f"  ys={ys_exact_duplicate}")
    print(f"  det={raw_duplicate:+.15e}")
    print()

    eps = 1e-3
    ys_ordered = [y0 + eps * r for r in offsets]
    ys_swapped = ys_ordered[:]
    ys_swapped[1], ys_swapped[2] = ys_swapped[2], ys_swapped[1]
    raw_ordered = np.linalg.det(matrix(xs, ys_ordered))
    raw_swapped = np.linalg.det(matrix(xs, ys_swapped))
    norm_ordered = raw_ordered / vandermonde(ys_ordered)
    norm_swapped = raw_swapped / vandermonde(ys_swapped)
    print("ordering check:")
    print(f"  raw ordered sign={math.copysign(1, raw_ordered):+.0f}")
    print(f"  raw adjacent-swap sign={math.copysign(1, raw_swapped):+.0f}")
    print(f"  normalized ordered={norm_ordered:+.15e}")
    print(f"  normalized adjacent-swap={norm_swapped:+.15e}")
    print()

    print("Interpretation:")
    print("  Multiple nodes are not harmless duplicates.  The determinant collapses")
    print("  exactly at the Vandermonde rate, and the sign-stable object is the")
    print("  confluent derivative determinant after order-aware normalization.")


if __name__ == "__main__":
    main()
