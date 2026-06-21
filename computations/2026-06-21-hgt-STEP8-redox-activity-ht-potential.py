#!/usr/bin/env python3
"""THE-MACHINE Step 8 HT transfer.

NODE: activity coefficients shift redox potential away from concentration
ratios.

Selected minimal HT edit: compare an ideal amplitude-ratio potential with a
phase/activity-corrected complex potential for the continuum differential weld.
"""

import argparse
import math

import mpmath as mp
import numpy as np


BASE_TRANSFER = (
    "ideal concentration-ratio potential is compared with activity-corrected "
    "potential; activity coefficients create a shift"
)

ATTEMPTS = {
    "phase-activity-potential": (
        "ideal amplitude-ratio potential is compared with phase-activity "
        "corrected potential; complex activity creates a shift"
    ),
    "prime-ionic-strength": (
        "prime-count cutoff becomes ionic strength; finite Euler activity "
        "coefficients shift a redox-like potential"
    ),
    "gamma-activity-coeff": (
        "archimedean gamma component supplies activity coefficients that shift "
        "prime concentration potentials"
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


def potentials(kind, sigma, window, primes, rng):
    ideal = []
    active = []
    shift = []
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
        ideal_v = math.log((abs(p) + 1e-12) / (abs(g) + 1e-12))
        active_v = math.log((abs(g + p) + 1e-12) / (abs(g) + 1e-12))
        ideal.append(ideal_v)
        active.append(active_v)
        shift.append(active_v - ideal_v)
    return float(np.median(ideal)), float(np.median(active)), float(np.median(shift)), float(np.mean(np.array(shift) < -0.5))


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
    print("STEP8/9 redox activity-corrected HT potential")
    print("method=2 attack-as-false; finite-Euler and random-phase controls test whether shifts are just phase-defect artifacts")
    print(f"finite_prime_count={args.prime_count}")
    print("sigma window kind ideal_med active_med shift_med frac_shift_lt_-0.5")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for sigma in [0.3, 0.5, 0.7]:
            for kind in ["true-zeta", "finite-euler", "random-phase"]:
                row = potentials(kind, sigma, window, primes, rng)
                print(
                    f"{sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {kind:12s} "
                    f"{row[0]:.6f} {row[1]:.6f} {row[2]:.6f} {row[3]:.6f}"
                )


if __name__ == "__main__":
    main()
