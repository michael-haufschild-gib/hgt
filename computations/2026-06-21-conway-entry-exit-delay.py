#!/usr/bin/env python3
"""THE-MACHINE run: entry-exit delays near repelling slow branches."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def node_simulation() -> None:
    print("NODE simulation: delayed exit after slow passage through instability")
    print("epsilon exit_mu exit_time naive_crossing delay")
    for eps in [0.04, 0.02, 0.01, 0.005]:
        dt = 0.002
        x = 1e-4
        time = -2.0 / eps
        exit_mu = None
        while time < 3.0 / eps:
            mu = eps * time
            # x'=mu*x-x^3; x=0 becomes repelling after mu crosses 0.
            x += dt * (mu * x - x**3)
            time += dt
            if mu > 0 and abs(x) > 0.1:
                exit_mu = mu
                break
        print(f"{eps:.4f} {exit_mu if exit_mu is not None else math.nan:.4f} {time:.2f} 0.0000 {time:.2f}")


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def first_primes(n: int) -> tuple[int, ...]:
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


def gamma_part(s: complex) -> complex:
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def dlog_zeta(s: complex, h: float = 1e-4) -> complex:
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite_euler(s: complex, primes: tuple[int, ...]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(g: complex, p: complex) -> float:
    return math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)


def trace(kind: str, sigma: float, samples: int, primes: tuple[int, ...], rng: np.random.Generator):
    driver = []
    defect = []
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        last_t = None
        for t in np.linspace(window[0], window[1], samples):
            s = complex(float(sigma), float(t))
            g = gamma_part(s)
            if kind == "true":
                p = dlog_zeta(s)
            elif kind == "finite":
                p = dlog_finite_euler(s, primes)
            else:
                z = dlog_zeta(s)
                theta = rng.uniform(-math.pi, math.pi)
                p = abs(z) * complex(math.cos(theta), math.sin(theta))
            phase_opposition = -math.cos(math.atan2((g / (p + 1e-300)).imag, (g / (p + 1e-300)).real))
            balance_penalty = abs(math.log((abs(g) + 1e-300) / (abs(p) + 1e-300)))
            score = phase_opposition - 0.35 * balance_penalty
            driver.append(score)
            defect.append(phase_defect(g, p))
            last_t = t
        if last_t is not None:
            driver.append(float("nan"))
            defect.append(float("nan"))
    return np.asarray(driver), np.asarray(defect)


def run_lengths(mask: np.ndarray) -> list[int]:
    out = []
    cur = 0
    for item in mask:
        if item:
            cur += 1
        elif cur:
            out.append(cur)
            cur = 0
    if cur:
        out.append(cur)
    return out


def lag_stats(driver: np.ndarray, defect: np.ndarray) -> tuple[float, float, float]:
    valid = ~np.isnan(driver)
    d_on = (driver > 0.45) & valid
    z_on = (defect > 1.0) & valid
    # Positive exit tail: defect remains on after driver turns off.
    tails = []
    for i in range(1, len(valid)):
        if valid[i - 1] and valid[i] and d_on[i - 1] and not d_on[i]:
            j = i
            while j < len(valid) and valid[j] and z_on[j]:
                j += 1
            if z_on[i]:
                tails.append(j - i)
    driver_runs = run_lengths(d_on)
    defect_runs = run_lengths(z_on)
    return (
        float(np.mean(tails)) if tails else 0.0,
        float(np.mean(driver_runs)) if driver_runs else 0.0,
        float(np.mean(defect_runs)) if defect_runs else 0.0,
    )


def run_levenshtein() -> None:
    node_sig = "entry exit delays near repelling slow branches dominate observed timing"
    candidates = [
        "entry exit delays near phase threshold branches dominate contour timing",
        "entry exit delays near zero shadow bridges dominate topology timing",
        "entry exit delays near amplitude basins dominate envelope timing",
    ]
    print("\nSTEP8 Levenshtein transfer candidates")
    best = None
    for i, cand in enumerate(candidates, 1):
        dist = levenshtein(node_sig, cand)
        ratio = dist / max(len(node_sig), len(cand))
        print(f"{i} distance={dist} ratio={ratio:.4f} {cand}")
        if best is None or dist < best[0]:
            best = (dist, i, cand)
    assert best is not None
    print(f"selected={best[1]} {best[2]}")


def ht_delay(samples: int, prime_count: int) -> None:
    primes = first_primes(prime_count)
    print("\nSTEP8/9 HT transfer: phase-driver entry/exit delay proxy")
    print("kind sigma exit_tail driver_run defect_run")
    for sigma in [0.3, 0.5, 1.2]:
        for kind in ["true", "finite", "random"]:
            rng = np.random.default_rng(991000 + int(100 * sigma) + {"true": 1, "finite": 2, "random": 3}[kind])
            driver, defect = trace(kind, sigma, samples, primes, rng)
            exit_tail, driver_run, defect_run = lag_stats(driver, defect)
            print(f"{kind:6s} {sigma:.1f} {exit_tail:.3f} {driver_run:.3f} {defect_run:.3f}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=220)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    node_simulation()
    run_levenshtein()
    ht_delay(args.samples, args.prime_count)


if __name__ == "__main__":
    main()
