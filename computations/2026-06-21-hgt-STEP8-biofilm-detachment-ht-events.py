#!/usr/bin/env python3
"""THE-MACHINE Step 8 HT transfer.

NODE: biofilm detachment is active life-history release, not passive sloughing.

Selected minimal HT edit: compare stress-triggered event release in a continuum
phase-defect field against passive random event sampling.
"""

import argparse
import math

import mpmath as mp
import numpy as np


BASE_TRANSFER = (
    "state-triggered detachment is compared with passive sloughing; active "
    "release has burst/timing structure"
)

ATTEMPTS = {
    "stress-triggered-events": (
        "phase-stress-triggered HT events are compared with passive sampling; "
        "active release has burst/timing structure"
    ),
    "zero-spore-release": (
        "zero-neighborhoods release spores when local analytic stress crosses "
        "a threshold rather than by random erosion"
    ),
    "finite-cutoff-slough": (
        "finite Euler cutoff artifacts are treated as passive sloughing and "
        "compared with true analytic event detachment"
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


def stress(kind, sigma, window, primes, rng):
    vals = []
    for t in np.linspace(window[0], window[1], 240):
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
        vals.append(phase_defect(g, p))
    arr = np.array(vals)
    return arr / (np.quantile(arr, 0.9) + 1e-12)


def event_metrics(driver, rng):
    active = driver * (1.0 / (1.0 + np.exp(-18.0 * (driver - 0.55))))
    passive = np.mean(active) * (0.75 + 0.5 * rng.random(len(driver)))
    def summary(x):
        return float(x.std() / (x.mean() + 1e-12)), float(np.mean(x > np.quantile(x, 0.9))), float(x[len(x)//2:].sum() / (x.sum() + 1e-12))
    return summary(active), summary(passive)


def attempt_report():
    rows = []
    for name, text in ATTEMPTS.items():
        d = levenshtein(BASE_TRANSFER, text)
        rows.append((d, d / max(len(BASE_TRANSFER), len(text)), name))
    rows.sort()
    print("STEP8 three HT-transfer attempts by Levenshtein from NODE test")
    for d, norm, name in rows:
        marker = "SELECTED" if name == rows[0][2] else "rejected"
        print(f"attempt={name:24s} levenshtein={d:3d} normalized={norm:.4f} {marker}")
    print()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    rng = np.random.default_rng(20260621)
    primes = first_primes(args.prime_count)
    attempt_report()
    print("STEP8/9 biofilm active-detachment HT events")
    print("method=8 look-for-similar-objects; compare true zeta with finite-Euler and random-phase event release")
    print(f"finite_prime_count={args.prime_count}")
    print("sigma window kind active_cv passive_cv active_late_frac passive_late_frac")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for sigma in [0.3, 0.5, 0.7]:
            for kind in ["true-zeta", "finite-euler", "random-phase"]:
                a, p = event_metrics(stress(kind, sigma, window, primes, rng), rng)
                print(
                    f"{sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {kind:12s} "
                    f"{a[0]:.6f} {p[0]:.6f} {a[2]:.6f} {p[2]:.6f}"
                )


if __name__ == "__main__":
    main()
