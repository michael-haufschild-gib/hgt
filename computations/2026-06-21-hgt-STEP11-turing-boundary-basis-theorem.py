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
    return max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))


def series(kind, sigma, window, samples, primes):
    vals = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true-zeta":
            p = dlog_zeta(s)
        elif kind == "finite-euler":
            p = dlog_finite_euler(s, primes)
        else:
            raise ValueError(kind)
        vals.append(phase_defect(g, p))
    arr = np.array(vals)
    return arr - arr.mean()


def basis(kind, n, m):
    x = np.linspace(0.0, 1.0, n)
    if kind == "periodic":
        return np.ones(n) if m == 0 else np.cos(2.0 * math.pi * m * x)
    if kind == "neumann":
        return np.cos(math.pi * m * x)
    if kind == "dirichlet":
        return np.sin(math.pi * (m + 1) * x)
    if kind == "mixed":
        return np.cos(math.pi * (m + 0.5) * x)
    raise ValueError(kind)


def captured_energy(vals, boundary, modes):
    energy = 0.0
    for m in range(modes):
        b = basis(boundary, len(vals), m)
        coeff = float(np.dot(vals, b) / (np.linalg.norm(b) + 1e-12))
        energy += coeff * coeff
    return energy / (float(np.dot(vals, vals)) + 1e-12)


def main():
    primes = first_primes(160)
    mode_counts = [4, 8, 16, 32, 64]
    print("STEP11 Turing-boundary right-theorem test")
    print("method=18 look-for-right-theorem; finite boundary-mode selection vs basis expansion")
    print("kind sigma window boundary captured_energy_by_modes")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for sigma in [0.3, 0.7]:
            for kind in ["true-zeta", "finite-euler"]:
                vals = series(kind, sigma, window, 260, primes)
                for boundary in ["periodic", "neumann", "dirichlet", "mixed"]:
                    vals_by_m = [captured_energy(vals, boundary, m) for m in mode_counts]
                    print(
                        f"{kind:12s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {boundary:9s} "
                        + ",".join(f"{x:.4f}" for x in vals_by_m)
                    )


if __name__ == "__main__":
    main()
