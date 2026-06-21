#!/usr/bin/env python3
"""THE-MACHINE Step 8 HT transfer.

NODE: boundary conditions select/suppress Turing modes.

Selected minimal HT edit: keep the mode-selection test, but apply boundary
bases (periodic/Neumann/Dirichlet/mixed) to a continuum differential strip
observable rather than to morphogen PDE variables.
"""

import argparse
import math

import mpmath as mp
import numpy as np


BASE_TRANSFER = (
    "same reaction data is projected onto boundary-admissible modes; boundary "
    "conditions select or suppress pattern modes"
)

ATTEMPTS = {
    "strip-boundary-modes": (
        "same continuum differential data is projected onto boundary-admissible "
        "modes; boundary conditions select or suppress HT strip modes"
    ),
    "zero-neighborhood-growth": (
        "reaction instability becomes growth of neighborhoods around zeros; "
        "boundary constraints select which zero-neighborhood modes amplify"
    ),
    "prime-diffusion-operator": (
        "diffusion constants become prime-frequency smoothing operators; "
        "admissible frequency bases select log-derivative modes"
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


def series(kind, sigma, window, samples, primes, rng):
    vals = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "gamma-only":
            vals.append(math.log1p(abs(g)))
        elif kind == "true-zeta":
            p = dlog_zeta(s)
            vals.append(phase_defect(g, p))
        elif kind == "finite-euler":
            p = dlog_finite_euler(s, primes)
            vals.append(phase_defect(g, p))
        elif kind == "random-phase":
            base = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(base) * complex(math.cos(theta), math.sin(theta))
            vals.append(phase_defect(g, p))
        else:
            raise ValueError(kind)
    arr = np.array(vals, dtype=float)
    return arr - arr.mean()


def basis(kind, n, m):
    x = np.linspace(0.0, 1.0, n)
    if kind == "periodic":
        if m == 0:
            return np.ones(n)
        return np.cos(2.0 * math.pi * m * x)
    if kind == "neumann":
        return np.cos(math.pi * m * x)
    if kind == "dirichlet":
        return np.sin(math.pi * (m + 1) * x)
    if kind == "mixed":
        return np.cos(math.pi * (m + 0.5) * x)
    raise ValueError(kind)


def mode_summary(vals, boundary, modes=16):
    energies = []
    for m in range(modes):
        b = basis(boundary, len(vals), m)
        coeff = float(np.dot(vals, b) / (np.linalg.norm(b) + 1e-12))
        energies.append(coeff * coeff)
    energies = np.array(energies)
    total = float(energies.sum() + 1e-12)
    return int(np.argmax(energies)), float(np.max(energies) / total), int(np.sum(energies > 0.05 * total))


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
    parser.add_argument("--samples", type=int, default=260)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    rng = np.random.default_rng(20260621)
    primes = first_primes(args.prime_count)
    attempt_report()
    print("STEP8/9 Turing boundary-mode HT transfer")
    print("method=15 strengthen-the-conjecture; count distinct best modes across boundary bases")
    print(f"samples={args.samples} finite_prime_count={args.prime_count}")
    print("kind sigma window boundary best_mode best_energy_frac active_modes")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for sigma in [0.3, 0.5, 0.7]:
            for kind in ["gamma-only", "true-zeta", "finite-euler", "random-phase"]:
                vals = series(kind, sigma, window, args.samples, primes, rng)
                selected = []
                active_counts = []
                for boundary in ["periodic", "neumann", "dirichlet", "mixed"]:
                    mode, frac, active = mode_summary(vals, boundary)
                    selected.append(mode)
                    active_counts.append(active)
                    print(
                        f"{kind:12s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {boundary:9s} "
                        f"{mode:9d} {frac:.6f} {active:12d}"
                    )
                print(
                    f"STRENGTH kind={kind} sigma={sigma:.1f} window=[{window[0]:.0f},{window[1]:.0f}] "
                    f"distinct_best_modes={len(set(selected))} active_mode_range={min(active_counts)}:{max(active_counts)}"
                )


if __name__ == "__main__":
    main()
