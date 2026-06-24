#!/usr/bin/env python3
"""Workflow W4: nonhyperbolic chaotic escape tails.

NODE: nonhyperbolic escape can produce algebraic rather than exponential
lifetime distributions. The minimal counterexample to "escape is exponential"
is an open intermittent map with a neutral fixed point.
"""

from __future__ import annotations

import argparse
import math
import random
from typing import Callable, Iterable

import mpmath as mp


def linear_fit(xs: list[float], ys: list[float]) -> tuple[float, float, float]:
    n = len(xs)
    sx = sum(xs)
    sy = sum(ys)
    sxx = sum(x * x for x in xs)
    sxy = sum(x * y for x, y in zip(xs, ys))
    denom = n * sxx - sx * sx
    if abs(denom) < 1e-30:
        return 0.0, sy / max(n, 1), 0.0
    slope = (n * sxy - sx * sy) / denom
    intercept = (sy - slope * sx) / n
    mean_y = sy / n
    ss_tot = sum((y - mean_y) ** 2 for y in ys)
    ss_res = sum((y - (slope * x + intercept)) ** 2 for x, y in zip(xs, ys))
    r2 = 1.0 - ss_res / ss_tot if ss_tot > 1e-30 else 0.0
    return slope, intercept, r2


def fit_survival(checkpoints: list[int], survival: list[float], tail_start: int) -> dict[str, float]:
    pts = [(t, s) for t, s in zip(checkpoints, survival) if t >= tail_start and s > 0.0]
    if len(pts) < 4:
        return {"exp_slope": 0.0, "exp_r2": 0.0, "pow_slope": 0.0, "pow_r2": 0.0}
    ts = [float(t) for t, _ in pts]
    logs = [math.log(s) for _, s in pts]
    logts = [math.log(t) for t, _ in pts]
    exp_slope, _, exp_r2 = linear_fit(ts, logs)
    pow_slope, _, pow_r2 = linear_fit(logts, logs)
    return {
        "exp_slope": exp_slope,
        "exp_r2": exp_r2,
        "pow_slope": pow_slope,
        "pow_r2": pow_r2,
    }


def simulate_open_map(
    name: str,
    step: Callable[[float], float],
    hole: tuple[float, float],
    n: int,
    max_steps: int,
    checkpoints: list[int],
    seed: int,
) -> tuple[list[float], dict[str, float]]:
    rng = random.Random(seed)
    active = [rng.random() for _ in range(n)]
    survival = []
    checkpoint_set = set(checkpoints)
    for t in range(1, max_steps + 1):
        next_active = []
        lo, hi = hole
        for x in active:
            y = step(x)
            if not (lo <= y <= hi):
                next_active.append(y)
        active = next_active
        if t in checkpoint_set:
            survival.append(len(active) / n)
        if not active:
            for future in checkpoints:
                if future > t and future not in checkpoint_set:
                    survival.append(0.0)
            break
    while len(survival) < len(checkpoints):
        survival.append(0.0)
    fits = fit_survival(checkpoints, survival, tail_start=max(20, checkpoints[1]))
    print(f"NODE map={name} hole={hole} n={n} max_steps={max_steps}")
    print("checkpoint survival")
    for t, s in zip(checkpoints, survival):
        print(f"{t:6d} {s:.8f}")
    print(
        "fit "
        f"exp_slope={fits['exp_slope']:.8g} exp_r2={fits['exp_r2']:.6f} "
        f"pow_slope={fits['pow_slope']:.8g} pow_r2={fits['pow_r2']:.6f}"
    )
    return survival, fits


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def first_primes(n: int) -> list[int]:
    primes: list[int] = []
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
    return primes


def gamma_part(s: complex) -> complex:
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def dlog_zeta(s: complex, h: float = 2e-4) -> complex:
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite_euler(s: complex, primes: list[int]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(gamma_value: complex, prime_value: complex) -> float:
    return math.log(max(abs(gamma_value), abs(prime_value)) + 1e-300) - math.log(
        abs(gamma_value + prime_value) + 1e-300
    )


def quantile(values: list[float], q: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    idx = min(len(ordered) - 1, max(0, int(round(q * (len(ordered) - 1)))))
    return ordered[idx]


def run_lengths(flags: Iterable[bool]) -> list[int]:
    out: list[int] = []
    current = 0
    for flag in flags:
        if flag:
            current += 1
        elif current:
            out.append(current)
            current = 0
    if current:
        out.append(current)
    return out


def length_survival(lengths: list[int], checkpoints: list[int]) -> tuple[list[float], dict[str, float]]:
    if not lengths:
        return [0.0 for _ in checkpoints], {"exp_slope": 0.0, "exp_r2": 0.0, "pow_slope": 0.0, "pow_r2": 0.0}
    survival = [sum(1 for length in lengths if length >= t) / len(lengths) for t in checkpoints]
    return survival, fit_survival(checkpoints, survival, tail_start=max(3, checkpoints[len(checkpoints) // 3]))


def ht_transfer(samples: int, prime_count: int, seed: int) -> None:
    node_sig = "nonhyperbolic escape has algebraic lifetime tail"
    candidates = [
        "nonhyperbolic phase defect escape has algebraic lifetime tail",
        "seam source survival has algebraic lifetime tail",
        "zero shadow leak has algebraic lifetime tail",
    ]
    print("\nSTEP8 Levenshtein transfer candidates")
    best: tuple[int, int, str] | None = None
    for idx, cand in enumerate(candidates, 1):
        dist = levenshtein(node_sig, cand)
        ratio = dist / max(len(node_sig), len(cand))
        print(f"{idx} distance={dist} ratio={ratio:.4f} {cand}")
        if best is None or dist < best[0]:
            best = (dist, idx, cand)
    assert best is not None
    print(f"selected={best[1]} {best[2]}")

    primes = first_primes(prime_count)
    rng = random.Random(seed)
    print("\nSTEP9 method=16 minimal counterexample: HT phase-defect lifetime tails")
    print("kind sigma threshold run_count max_run exp_r2 pow_r2 exp_slope pow_slope survival")
    checkpoints = [2, 3, 4, 6, 8, 12, 16, 24, 32, 48]
    for sigma in [0.3, 0.5, 1.2]:
        base_values: dict[str, list[float]] = {"true": [], "finite": [], "random": []}
        for i in range(samples):
            t = 80.0 + 0.08 * i
            s = complex(float(sigma), t)
            g = gamma_part(s)
            z = dlog_zeta(s)
            f = dlog_finite_euler(s, primes)
            theta = rng.uniform(-math.pi, math.pi)
            r = abs(z) * complex(math.cos(theta), math.sin(theta))
            base_values["true"].append(phase_defect(g, z))
            base_values["finite"].append(phase_defect(g, f))
            base_values["random"].append(phase_defect(g, r))
        for kind, vals in base_values.items():
            threshold = quantile(vals, 0.75)
            flags = [value <= threshold for value in vals]
            lengths = run_lengths(flags)
            survival, fits = length_survival(lengths, checkpoints)
            surv_text = ",".join(f"{t}:{s:.3f}" for t, s in zip(checkpoints, survival))
            max_run = max(lengths) if lengths else 0
            print(
                f"{kind:6s} {sigma:.1f} {threshold:.6f} {len(lengths):4d} {max_run:4d} "
                f"{fits['exp_r2']:.4f} {fits['pow_r2']:.4f} "
                f"{fits['exp_slope']:.4g} {fits['pow_slope']:.4g} {surv_text}"
            )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--node-n", type=int, default=20000)
    parser.add_argument("--node-max-steps", type=int, default=6000)
    parser.add_argument("--ht-samples", type=int, default=900)
    parser.add_argument("--prime-count", type=int, default=80)
    parser.add_argument("--seed", type=int, default=279994678386043821 % (2**32))
    args = parser.parse_args()

    checkpoints = [20, 40, 80, 160, 320, 640, 1280, 2560, 5120]
    simulate_open_map(
        "mixing_logistic_control",
        lambda x: 4.0 * x * (1.0 - x),
        (0.20, 0.22),
        args.node_n,
        args.node_max_steps,
        checkpoints,
        args.seed,
    )
    print()
    alpha = 1.0
    coeff = 0.45
    simulate_open_map(
        "nonhyperbolic_intermittent",
        lambda x: (x + coeff * (x ** (1.0 + alpha))) % 1.0,
        (0.55, 0.65),
        args.node_n,
        args.node_max_steps,
        checkpoints,
        args.seed + 1,
    )
    ht_transfer(args.ht_samples, args.prime_count, args.seed + 2)


if __name__ == "__main__":
    main()
