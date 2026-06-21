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


def obs(kind, sigma, t, primes, rng):
    s = complex(float(sigma), float(t))
    g = gamma_part(s)
    if kind == "true-zeta":
        return phase_defect(g, dlog_zeta(s))
    if kind == "finite-euler":
        return phase_defect(g, dlog_finite_euler(s, primes))
    if kind == "random-phase":
        base = dlog_zeta(s)
        theta = rng.uniform(-math.pi, math.pi)
        return phase_defect(g, abs(base) * complex(math.cos(theta), math.sin(theta)))
    raise ValueError(kind)


def glyph(v):
    if v > 3.0:
        return "#"
    if v > 0.3:
        return "+"
    if v > -0.3:
        return "."
    if v > -3.0:
        return "-"
    return "_"


def main():
    rng = np.random.default_rng(20260621)
    primes = first_primes(160)
    print("STEP11 pitting potential visual")
    print("method=5 make-it-visual; # strong left-bottom potential, _ strong reverse potential")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        print(f"WINDOW [{window[0]:.0f},{window[1]:.0f}]")
        for kind in ["true-zeta", "finite-euler", "random-phase"]:
            chars = []
            vals = []
            for t in np.linspace(window[0], window[1], 90):
                left = obs(kind, 0.2, t, primes, rng)
                right = obs(kind, 0.8, t, primes, rng)
                v = math.log((left + 1e-9) / (right + 1e-9))
                chars.append(glyph(v))
                vals.append(v)
            print(f"{kind:12s} {''.join(chars)} median={np.median(vals):.6f} frac_pos={np.mean(np.array(vals)>0.3):.6f}")


if __name__ == "__main__":
    main()
