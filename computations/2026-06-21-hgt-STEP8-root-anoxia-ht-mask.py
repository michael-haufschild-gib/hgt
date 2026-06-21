#!/usr/bin/env python3
"""THE-MACHINE Step 8 HT transfer.

NODE: nitrate can mask oxygen stress but cannot replace aerobic ATP.

Selected minimal HT edit: compare an alternate scalar relief proxy with a
phase-specific continuum function proxy in the archimedean-prime weld.
"""

import argparse
import math

import mpmath as mp
import numpy as np


BASE_TRANSFER = (
    "alternate electron sink raises a stress-relief proxy while ATP remains "
    "deficient under oxygen limitation"
)

ATTEMPTS = {
    "amplitude-mask-phase-atp": (
        "alternate scalar amplitude raises a stress-relief proxy while "
        "phase-specific HT function remains deficient under continuation stress"
    ),
    "finite-euler-nitrate": (
        "finite Euler terms serve as nitrate-like sinks; they mask local stress "
        "without replacing analytic-continuation energy"
    ),
    "random-phase-fermentation": (
        "random phase surrogates act like fermentation; they provide partial "
        "relief but fail the full aerobic phase constraint"
    ),
}


def levenshtein(a, b):
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


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


def scores(kind, sigma, window, primes, rng):
    relief = []
    function = []
    for t in np.linspace(window[0], window[1], 220):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true-zeta":
            p = dlog_zeta(s)
        elif kind == "finite-euler":
            p = dlog_finite_euler(s, primes)
        elif kind == "random-phase":
            base = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(base) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        relief.append(math.log1p(max(abs(g), abs(p))))
        function.append(phase_defect(g, p))
    return float(np.median(relief)), float(np.median(function))


def attempt_report():
    rows = []
    for name, text in ATTEMPTS.items():
        d = levenshtein(BASE_TRANSFER, text)
        rows.append((d, d / max(len(BASE_TRANSFER), len(text)), name))
    rows.sort()
    print("STEP8 three HT-transfer attempts by Levenshtein from NODE test")
    for d, norm, name in rows:
        marker = "SELECTED" if name == rows[0][2] else "rejected"
        print(f"attempt={name:25s} levenshtein={d:3d} normalized={norm:.4f} {marker}")
    print()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    rng = np.random.default_rng(20260621)
    primes = first_primes(args.prime_count)
    attempt_report()
    print("STEP8/9 root-anoxia nitrate-mask HT transfer")
    print("method=13 find-a-monotone-quantity; test finite-prime relief growth against phase-function deficiency")
    print(f"finite_prime_count={args.prime_count}")
    print("sigma window kind relief_proxy phase_function masked_but_deficient")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for sigma in [0.3, 0.5, 0.7]:
            rows = {}
            for kind in ["true-zeta", "finite-euler", "random-phase"]:
                rows[kind] = scores(kind, sigma, window, primes, rng)
            true_relief, true_function = rows["true-zeta"]
            for kind, (relief, function) in rows.items():
                masked = int(relief >= 0.9 * true_relief and function < 0.35 * true_function)
                print(
                    f"{sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {kind:12s} "
                    f"{relief:.6f} {function:.6f} {masked}"
                )
    print("MONOTONE finite-euler prime-count sweep at sigma=0.3")
    print("window prime_count relief_proxy phase_function")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for count in [10, 30, 80, 160, 240]:
            relief, function = scores("finite-euler", 0.3, window, first_primes(count), rng)
            print(f"[{window[0]:.0f},{window[1]:.0f}] {count:11d} {relief:.6f} {function:.6f}")


if __name__ == "__main__":
    main()
