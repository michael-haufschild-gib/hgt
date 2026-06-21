#!/usr/bin/env python3
import math

import mpmath as mp
import numpy as np


def first_primes(n):
    primes = []
    candidate = 2
    while len(primes) < n:
        ok = True
        for p in primes:
            if p * p > candidate:
                break
            if candidate % p == 0:
                ok = False
                break
        if ok:
            primes.append(candidate)
        candidate += 1 if candidate == 2 else 2
    return tuple(primes)


def gamma_part(s):
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def dlog_zeta(s, h=1e-4):
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite_euler(s, primes):
    out = 0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(g, p):
    return math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)


def profile(kind, beta, sigma, window, samples, primes):
    vals = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true":
            p = dlog_zeta(s)
        elif kind == "finite":
            p = dlog_finite_euler(s, primes)
        else:
            raise ValueError(kind)
        z = g + beta * p
        vals.append([math.log1p(abs(z)), max(0.0, phase_defect(g, beta * p)), math.atan2(z.imag, z.real)])
    arr = np.array(vals, dtype=float)
    arr[:, 2] = np.unwrap(arr[:, 2])
    mean = arr.mean(axis=0)
    std = arr.std(axis=0) + 1e-12
    return (arr - mean) / std


def dist(a, b):
    return float(np.linalg.norm(a - b) / math.sqrt(a.size))


def monotone_direction(xs):
    diffs = np.diff(xs)
    if np.all(diffs >= -1e-9):
        return "nondecreasing"
    if np.all(diffs <= 1e-9):
        return "nonincreasing"
    return "nonmonotone"


def main():
    primes = first_primes(160)
    betas = [0.0, 0.05, 0.10, 0.20, 0.40, 0.70, 1.00, 1.50, 2.00, 3.00]
    cases = [(0.3, (100.0, 170.0)), (0.5, (100.0, 170.0)), (0.7, (100.0, 170.0)), (0.3, (500.0, 570.0))]
    print("STEP11 stem-taxa metaphor monotone sweep")
    print("method=13 find-a-monotone-quantity; beta grows prime-component strength")
    print("sigma window kind direction distances")
    for sigma, window in cases:
        ancestor = profile("true", 0.0, sigma, window, 240, primes)
        for kind in ["true", "finite"]:
            ds = [dist(profile(kind, beta, sigma, window, 240, primes), ancestor) for beta in betas]
            print(
                f"{sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {kind:6s} "
                f"{monotone_direction(ds):13s} "
                + ",".join(f"{x:.4f}" for x in ds)
            )


if __name__ == "__main__":
    main()
