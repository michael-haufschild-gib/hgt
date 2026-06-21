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


def component(kind, s, primes, rng):
    g = gamma_part(s)
    if kind == "true-lambda":
        p = dlog_zeta(s)
        return g + p, max(0.0, phase_defect(g, p))
    if kind == "finite-euler":
        p = dlog_finite_euler(s, primes)
        return p, max(0.0, phase_defect(g, p))
    if kind == "random-phase":
        base = dlog_zeta(s)
        theta = rng.uniform(-math.pi, math.pi)
        p = abs(base) * complex(math.cos(theta), math.sin(theta))
        return p, max(0.0, phase_defect(g, p))
    raise ValueError(kind)


def network(kind, window, samples, primes, rng):
    vals = []
    defects = []
    lanes = []
    for lane, sigma in enumerate([0.3, 0.7]):
        for t in np.linspace(window[0], window[1], samples):
            z, d = component(kind, complex(sigma, float(t)), primes, rng)
            vals.append(z)
            defects.append(d)
            lanes.append(lane)
    vals = np.array(vals)
    defects = np.array(defects)
    lanes = np.array(lanes)
    n = len(vals)
    exposure = np.zeros((n, n))
    stress = np.log1p(np.abs(vals)) / (np.quantile(np.log1p(np.abs(vals)), 0.85) + 1e-12) + defects
    for i in range(n):
        lane = lanes[i]
        k = i % samples
        for step in [1, 2, 5]:
            for kk in [k - step, k + step]:
                if 0 <= kk < samples:
                    j = lane * samples + kk
                    exposure[j, i] += 0.025 * min(stress[i], stress[j])
        mirror = (1 - lane) * samples + k
        resid = abs(vals[i] + np.conjugate(vals[mirror])) / (abs(vals[i]) + abs(vals[mirror]) + 1e-12)
        exposure[mirror, i] += 0.11 * min(stress[i], stress[mirror]) / (0.35 + resid)
    capital = 0.11 + 0.07 / (1.0 + stress)
    return lanes, exposure, capital, stress


def cascade(lanes, exposure, capital, seed, recovery, delay):
    equity = capital.copy()
    defaulted = np.zeros(len(capital), dtype=bool)
    pending = np.zeros(len(capital))
    equity[seed] = -0.20
    total = 0.0
    for _ in range(24):
        shockers = np.flatnonzero((equity < 0.0) & ~defaulted)
        if len(shockers) == 0 and np.all(pending <= 1e-12):
            break
        defaulted[shockers] = True
        current = pending.copy()
        pending[:] = 0.0
        for i in shockers:
            for j in np.flatnonzero(exposure[:, i] > 0.0):
                loss = exposure[j, i] * (1.0 - recovery[lanes[i], lanes[j]])
                if lanes[i] == lanes[j]:
                    current[j] += loss
                else:
                    pending[j] += loss * delay[lanes[i], lanes[j]]
                    current[j] += loss * (1.0 - delay[lanes[i], lanes[j]])
        equity -= current
        total += float(current.sum())
    return int(defaulted.sum()), total


def main():
    rng = np.random.default_rng(20260621)
    primes = first_primes(160)
    recovery = np.array([[0.58, 0.10], [0.10, 0.58]])
    delay = np.array([[0.0, 0.85], [0.85, 0.0]])
    print("STEP11 cross-border-resolution viewpoint change")
    print("method=4 change-viewpoint; original vs transposed exposures, high vs low stress seeds")
    print("kind window orientation seed_band defaults_q50 defaults_q90 loss_q50 loss_q90")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for kind in ["true-lambda", "finite-euler", "random-phase"]:
            lanes, exposure, capital, stress = network(kind, window, 120, primes, rng)
            bands = {
                "high": np.argsort(stress)[-40:],
                "low": np.argsort(stress)[:40],
            }
            for orientation, exp in [("original", exposure), ("transpose", exposure.T)]:
                for band, seeds in bands.items():
                    defaults = []
                    losses = []
                    for seed in seeds:
                        d, loss = cascade(lanes, exp, capital, int(seed), recovery, delay)
                        defaults.append(d)
                        losses.append(loss)
                    print(
                        f"{kind:12s} [{window[0]:.0f},{window[1]:.0f}] {orientation:9s} {band:4s} "
                        f"{np.quantile(defaults,0.5):12.6f} {np.quantile(defaults,0.9):12.6f} "
                        f"{np.quantile(losses,0.5):9.6f} {np.quantile(losses,0.9):9.6f}"
                    )


if __name__ == "__main__":
    main()
