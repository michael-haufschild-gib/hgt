#!/usr/bin/env python3
"""THE-MACHINE NODE + Step 8/9.

NODE: in special matrix classes, contiguous minors can sometimes suffice; in
generic matrices, adjacent checks do not certify total positivity.

Step 9 method #9: test small cases.
"""

import itertools
import math

import mpmath as mp
import numpy as np


def det_sub(M, rows, cols):
    return float(np.linalg.det(M[np.ix_(rows, cols)]))


def adjacent_2x2_positive(M, tol=1e-10):
    n, m = M.shape
    vals = []
    for i in range(n - 1):
        for j in range(m - 1):
            vals.append(det_sub(M, [i, i + 1], [j, j + 1]))
    return min(vals), all(v > tol for v in vals)


def all_minors_summary(M, k):
    vals = []
    for rows in itertools.combinations(range(M.shape[0]), k):
        for cols in itertools.combinations(range(M.shape[1]), k):
            vals.append(det_sub(M, rows, cols))
    arr = np.array(vals)
    return float(arr.min()), int(np.sum(arr <= 0)), len(vals)


def find_generic_counterexample(seed=20260620):
    rng = np.random.default_rng(seed)
    for trial in range(200000):
        M = np.exp(rng.normal(size=(4, 4)))
        m2, ok2 = adjacent_2x2_positive(M)
        if not ok2:
            continue
        m3, bad3, total3 = all_minors_summary(M, 3)
        if bad3:
            return trial, M, m2, m3, bad3, total3
    raise RuntimeError("no counterexample found")


def dlog_zeta(s, h=1e-4):
    z0 = mp.fp.zeta(s)
    return (mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300))


def dlog_gamma(s):
    return -0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0)


def dlog_finite_euler(s):
    out = 0j
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29):
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return out


def dlog(name, s):
    if name == "lambda":
        return complex(dlog_gamma(s) + dlog_zeta(s))
    if name == "zeta":
        return complex(dlog_zeta(s))
    if name == "gamma-factor":
        return complex(dlog_gamma(s))
    if name == "finite-euler":
        return complex(dlog_finite_euler(s))
    raise ValueError(name)


def strip_matrix(name, sigmas, ts):
    M = np.empty((len(sigmas), len(ts)), dtype=float)
    for i, sigma in enumerate(sigmas):
        for j, t in enumerate(ts):
            M[i, j] = math.log1p(abs(dlog(name, complex(float(sigma), float(t)))))
    return M


def main():
    trial, M, m2, m3, bad3, total3 = find_generic_counterexample()
    print("NODE small-case contiguous-minor check")
    print(f"generic positive 4x4 counterexample trial={trial} min_adjacent_2x2={m2:.6g} min_3x3={m3:.6g} bad_3x3={bad3}/{total3}")
    print("matrix")
    for row in M:
        print(" ".join(f"{x:.5g}" for x in row))

    sigmas = np.linspace(0.2, 0.8, 4)
    windows = [(14, 84), (100, 170), (500, 570)]
    print("STEP8/9 HT strip minor probe: entries=log(1+|dlog f(sigma+it)|)")
    print("name window min_adj2 ok_adj2 min_3x3 bad_3x3/total")
    for t0, t1 in windows:
        ts = np.linspace(t0, t1, 4)
        for name in ("lambda", "zeta", "gamma-factor", "finite-euler"):
            A = strip_matrix(name, sigmas, ts)
            min2, ok2 = adjacent_2x2_positive(A)
            min3, bad3, total3 = all_minors_summary(A, 3)
            print(f"{name:12s} [{t0},{t1}] {min2:.6g} {int(ok2)} {min3:.6g} {bad3}/{total3}")


if __name__ == "__main__":
    main()
