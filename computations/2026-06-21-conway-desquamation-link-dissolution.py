#!/usr/bin/env python3
"""THE-MACHINE run: enzyme-regulated link dissolution in desquamation."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def node_simulation() -> None:
    print("NODE simulation: detachment requires adhesion dissolution, not passive falling")
    print("protease inhibitor detachment_time final_adhesion mechanism")
    for protease, inhibitor in [(0.04, 0.02), (0.08, 0.02), (0.08, 0.06), (0.14, 0.02)]:
        adhesion = 1.0
        time = 0
        while time < 300 and adhesion > 0.18:
            hydration = 0.65 + 0.15 * math.sin(time / 17.0)
            degradation = max(0.0, protease * hydration - inhibitor)
            adhesion = max(0.0, adhesion - degradation)
            time += 1
        mechanism = "released" if adhesion <= 0.18 else "retained"
        print(f"{protease:.2f} {inhibitor:.2f} {time:4d} {adhesion:.4f} {mechanism}")


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


def observables(g: complex, p: complex) -> tuple[float, float, float]:
    defect = math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)
    phase_link = -math.cos(math.atan2((g / (p + 1e-300)).imag, (g / (p + 1e-300)).real))
    balance_link = -abs(math.log((abs(g) + 1e-300) / (abs(p) + 1e-300)))
    return defect, phase_link, balance_link


def trace(kind: str, sigma: float, samples: int, primes: tuple[int, ...], rng: np.random.Generator):
    rows = []
    for window in [(100.0, 170.0), (500.0, 570.0)]:
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
            rows.append(observables(g, p))
        rows.append((float("nan"), float("nan"), float("nan")))
    return np.asarray(rows)


def exit_mechanisms(rows: np.ndarray, threshold: float) -> tuple[int, float, float, float]:
    d = rows[:, 0]
    phase = rows[:, 1]
    bal = rows[:, 2]
    valid = ~np.isnan(d)
    on = (d > threshold) & valid
    phase_fracs = []
    drops = []
    for i in range(1, len(on)):
        if valid[i - 1] and valid[i] and on[i - 1] and not on[i]:
            dp = max(0.0, phase[i - 1] - phase[i])
            db = max(0.0, bal[i - 1] - bal[i])
            total = dp + db
            if total > 1e-9:
                phase_fracs.append(dp / total)
                drops.append(total)
    if not phase_fracs:
        return 0, 0.0, 0.0, 0.0
    arr = np.asarray(phase_fracs)
    return len(arr), float(np.mean(arr)), float(np.mean(arr > 0.65)), float(np.mean(drops))


def run_levenshtein() -> None:
    node_sig = "enzyme regulated dissolution intercellular adhesion structures desquamation"
    candidates = [
        "phase regulated dissolution of cancellation adhesion structures",
        "zero shadow regulated dissolution of topology adhesion structures",
        "amplitude regulated passive falling of envelope structures",
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


def ht_dissolution(samples: int, prime_count: int, threshold: float) -> None:
    primes = first_primes(prime_count)
    print("\nSTEP8/9 HT transfer: high-defect run exit mechanism")
    print(f"threshold={threshold:.3f} samples_per_window={samples} prime_count={prime_count}")
    print("kind sigma exits mean_phase_fraction phase_dominant mean_link_drop")
    for sigma in [0.3, 0.5, 1.2]:
        for kind in ["true", "finite", "random"]:
            rng = np.random.default_rng(1510000 + int(100 * sigma) + {"true": 1, "finite": 2, "random": 3}[kind])
            rows = trace(kind, sigma, samples, primes, rng)
            exits, phase_frac, phase_dom, drop = exit_mechanisms(rows, threshold)
            print(f"{kind:6s} {sigma:.1f} {exits:4d} {phase_frac:.4f} {phase_dom:.4f} {drop:.4f}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=240)
    parser.add_argument("--prime-count", type=int, default=160)
    parser.add_argument("--threshold", type=float, default=1.0)
    args = parser.parse_args()
    node_simulation()
    run_levenshtein()
    ht_dissolution(args.samples, args.prime_count, args.threshold)


if __name__ == "__main__":
    main()
