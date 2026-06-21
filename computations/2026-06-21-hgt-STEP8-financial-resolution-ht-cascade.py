#!/usr/bin/env python3
"""THE-MACHINE Step 8 HT transfer.

NODE: cross-border resolution rules alter financial loss propagation.

Selected minimal HT edit: keep the same cascade test, but replace institutions
by continuum differential strip samples. Jurisdictions are the two mirror lanes
sigma and 1-sigma; resolution rules change recovery/delay of cross-lane loss.
"""

import argparse
import math

import mpmath as mp
import numpy as np


BASE_TRANSFER = (
    "same exposure network is run under different recovery and delay rules; "
    "cross-border resolution changes loss propagation"
)

ATTEMPTS = {
    "strip-resolution-cascade": (
        "same continuum strip exposure network is run under different recovery "
        "and delay rules; cross-lane resolution changes loss propagation"
    ),
    "branch-cut-bankruptcy": (
        "branch choices are treated as bankruptcy courts; continuation through "
        "a cut changes which local singular stresses are written down"
    ),
    "prime-collateral-haircut": (
        "prime factors become reusable collateral chains; Euler cutoffs and "
        "analytic continuation impose different haircuts on propagated shocks"
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
    return math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)


def component(kind, s, primes, rng):
    g = gamma_part(s)
    if kind == "gamma-only":
        return g, 0.0
    if kind == "true-lambda":
        p = dlog_zeta(s)
        return g + p, max(0.0, phase_defect(g, p))
    if kind == "zeta-prime":
        p = dlog_zeta(s)
        return p, max(0.0, phase_defect(g, p))
    if kind == "finite-euler":
        p = dlog_finite_euler(s, primes)
        return p, max(0.0, phase_defect(g, p))
    if kind == "random-phase":
        base = dlog_zeta(s)
        theta = rng.uniform(-math.pi, math.pi)
        p = abs(base) * complex(math.cos(theta), math.sin(theta))
        return p, max(0.0, phase_defect(g, p))
    raise ValueError(kind)


def build_network(kind, window, samples, primes, rng):
    vals = []
    defects = []
    lanes = []
    for lane, sigma in enumerate([0.3, 0.7]):
        for t in np.linspace(window[0], window[1], samples):
            z, d = component(kind, complex(sigma, float(t)), primes, rng)
            vals.append(z)
            defects.append(d)
            lanes.append(lane)
    vals = np.array(vals, dtype=complex)
    defects = np.array(defects, dtype=float)
    lanes = np.array(lanes, dtype=int)
    n = len(vals)
    exposure = np.zeros((n, n), dtype=float)
    scale = np.quantile(np.log1p(np.abs(vals)), 0.85) + 1e-12
    stress = np.log1p(np.abs(vals)) / scale + defects
    for i in range(n):
        lane = lanes[i]
        k = i % samples
        for step in [1, 2, 5]:
            for kk in [k - step, k + step]:
                if 0 <= kk < samples:
                    j = lane * samples + kk
                    exposure[j, i] += 0.025 * min(stress[i], stress[j])
        mirror = (1 - lane) * samples + k
        mirror_resid = abs(vals[i] + np.conjugate(vals[mirror])) / (abs(vals[i]) + abs(vals[mirror]) + 1e-12)
        exposure[mirror, i] += 0.11 * min(stress[i], stress[mirror]) / (0.35 + mirror_resid)
    capital = 0.11 + 0.07 / (1.0 + stress)
    return lanes, exposure, capital, stress


def cascade(lanes, exposure, capital, recovery, delay_loss, seed):
    equity = capital.copy()
    defaulted = np.zeros(len(capital), dtype=bool)
    pending = np.zeros(len(capital))
    equity[seed] = -0.20
    losses_by_step = []
    for _ in range(24):
        new_default = equity < 0.0
        shockers = np.flatnonzero(new_default & ~defaulted)
        if len(shockers) == 0 and np.all(pending <= 1e-12):
            break
        defaulted |= new_default
        current = pending.copy()
        pending[:] = 0.0
        for i in shockers:
            for j in np.flatnonzero(exposure[:, i] > 0.0):
                loss = exposure[j, i] * (1.0 - recovery[lanes[i], lanes[j]])
                if lanes[i] == lanes[j]:
                    current[j] += loss
                else:
                    pending[j] += loss * delay_loss[lanes[i], lanes[j]]
                    current[j] += loss * (1.0 - delay_loss[lanes[i], lanes[j]])
        equity -= current
        losses_by_step.append(float(current.sum()))
    return int(defaulted.sum()), float(sum(losses_by_step)), float(sum(losses_by_step[:2]) / (sum(losses_by_step) + 1e-12))


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
    parser.add_argument("--samples", type=int, default=120)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    rng = np.random.default_rng(20260621)
    primes = first_primes(args.prime_count)
    regimes = {
        "uniform": (np.ones((2, 2)) * 0.42, np.zeros((2, 2))),
        "fragmented": (np.array([[0.56, 0.24], [0.18, 0.50]]), np.array([[0.0, 0.70], [0.55, 0.0]])),
        "harsh_cross": (np.array([[0.58, 0.10], [0.10, 0.58]]), np.array([[0.0, 0.85], [0.85, 0.0]])),
    }
    attempt_report()
    print("STEP8/9 cross-border resolution cascade on HT strip")
    print("method=5 make-it-visual; severity glyph uses median defaults across top-stress seed shocks")
    print(f"samples_per_lane={args.samples} finite_prime_count={args.prime_count}")
    print("kind window regime defaults_q50 defaults_q90 loss_q50 loss_q90 front_loaded_q50 severity")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for kind in ["gamma-only", "true-lambda", "zeta-prime", "finite-euler", "random-phase"]:
            lanes, exposure, capital, stress = build_network(kind, window, args.samples, primes, rng)
            seeds = np.argsort(stress)[-40:]
            for regime, (recovery, delay) in regimes.items():
                defaults = []
                losses = []
                front = []
                for seed in seeds:
                    d, loss, f = cascade(lanes, exposure, capital, recovery, delay, int(seed))
                    defaults.append(d)
                    losses.append(loss)
                    front.append(f)
                sev = int(round(20.0 * np.quantile(defaults, 0.5) / (2 * args.samples)))
                print(
                    f"{kind:12s} [{window[0]:.0f},{window[1]:.0f}] {regime:11s} "
                    f"{np.quantile(defaults,0.5):12.6f} {np.quantile(defaults,0.9):12.6f} "
                    f"{np.quantile(losses,0.5):9.6f} {np.quantile(losses,0.9):9.6f} "
                    f"{np.quantile(front,0.5):17.6f} {'#' * sev}"
                )


if __name__ == "__main__":
    main()
