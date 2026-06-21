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


def stress(kind, window, primes):
    vals = []
    for t in np.linspace(window[0], window[1], 240):
        s = complex(0.3, float(t))
        g = gamma_part(s)
        p = dlog_zeta(s) if kind == "true-zeta" else dlog_finite_euler(s, primes)
        vals.append(phase_defect(g, p))
    arr = np.array(vals)
    return arr / (np.quantile(arr, 0.9) + 1e-12)


def response(driver, memory_strength):
    pit = 0.02
    acid = 0.0
    rates = []
    for k, raw in enumerate(driver):
        chloride = float(raw) if k < len(driver) // 2 else 0.05
        acid = 0.90 * acid + memory_strength * pit + 0.10 * chloride
        repair = 0.020 / (1.0 + 5.0 * acid)
        growth = (0.006 * chloride + 0.016 * acid) * (1.0 - pit)
        pit = min(1.0, max(0.0, pit + growth - repair))
        rates.append(growth)
    return float(np.mean(rates[-40:])), float(pit)


def main():
    primes = first_primes(160)
    print("STEP11 concrete memory theorem-boundary test")
    print("method=18 look-for-right-theorem; vary hysteresis memory strength")
    print("window kind memory_strength tail_growth final_state")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for kind in ["true-zeta", "finite-euler"]:
            driver = stress(kind, window, primes)
            for mem in [0.02, 0.04, 0.06, 0.08, 0.10, 0.14]:
                tail, pit = response(driver, mem)
                print(f"[{window[0]:.0f},{window[1]:.0f}] {kind:12s} {mem:.2f} {tail:.6f} {pit:.6f}")


if __name__ == "__main__":
    main()
