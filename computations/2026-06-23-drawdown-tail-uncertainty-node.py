#!/usr/bin/env python3
"""Workflow W5: tail-index uncertainty from few extreme drawdown durations."""

from __future__ import annotations

import argparse
import math
import random
from statistics import mean, pstdev

import mpmath as mp


def pareto(rng: random.Random, alpha: float, xm: float = 1.0) -> float:
    u = max(rng.random(), 1e-15)
    return xm * (u ** (-1.0 / alpha))


def mixture_drawdowns(rng: random.Random, n: int, slow_weight: float) -> list[float]:
    out = []
    for _ in range(n):
        if rng.random() < slow_weight:
            out.append(pareto(rng, 0.85, xm=8.0))
        else:
            out.append(pareto(rng, 2.4, xm=1.0))
    return out


def pure_drawdowns(rng: random.Random, n: int) -> list[float]:
    return [pareto(rng, 1.35, xm=1.0) for _ in range(n)]


def hill_alpha(samples: list[float], k: int) -> tuple[float, float]:
    ordered = sorted(samples, reverse=True)
    if len(ordered) <= k:
        raise ValueError("need at least k+1 samples")
    threshold = ordered[k]
    denom = sum(math.log(max(x / threshold, 1e-300)) for x in ordered[:k])
    alpha_hat = k / max(denom, 1e-300)
    naive_se = alpha_hat / math.sqrt(k)
    return alpha_hat, naive_se


def linear_fit(xs: list[float], ys: list[float]) -> tuple[float, float, float]:
    n = len(xs)
    sx = sum(xs)
    sy = sum(ys)
    sxx = sum(x * x for x in xs)
    sxy = sum(x * y for x, y in zip(xs, ys))
    denom = n * sxx - sx * sx
    if abs(denom) < 1e-30:
        return 0.0, 0.0, 0.0
    slope = (n * sxy - sx * sy) / denom
    intercept = (sy - slope * sx) / n
    residuals = [y - (slope * x + intercept) for x, y in zip(xs, ys)]
    sigma2 = sum(r * r for r in residuals) / max(n - 2, 1)
    slope_se = math.sqrt(max(sigma2 * n / denom, 0.0))
    ybar = sy / n
    ss_tot = sum((y - ybar) ** 2 for y in ys)
    ss_res = sum(r * r for r in residuals)
    r2 = 1.0 - ss_res / ss_tot if ss_tot > 1e-30 else 0.0
    return slope, slope_se, r2


def ols_tail_alpha(samples: list[float], k: int) -> tuple[float, float, float]:
    ordered = sorted(samples, reverse=True)
    xs = [math.log(x) for x in ordered[:k]]
    ys = [math.log((rank + 0.5) / len(samples)) for rank in range(1, k + 1)]
    slope, slope_se, r2 = linear_fit(xs, ys)
    return -slope, slope_se, r2


def summarize_node(reps: int, n: int, seed: int) -> None:
    print("NODE: tail-index uncertainty with few extreme drawdown durations")
    print(f"reps={reps} n={n} seed={seed}")
    print("case k hill_mean hill_emp_sd hill_naive_se ols_mean ols_emp_sd ols_naive_se mean_ols_r2")
    for case_name, sampler in [
        ("pure_pareto", lambda rng: pure_drawdowns(rng, n)),
        ("mixture_tail", lambda rng: mixture_drawdowns(rng, n, slow_weight=0.035)),
    ]:
        for k in [5, 10, 20, 40]:
            hills = []
            hill_ses = []
            ols = []
            ols_ses = []
            r2s = []
            for rep in range(reps):
                rng = random.Random(seed + 100000 * (1 + k) + 997 * rep + (0 if case_name == "pure_pareto" else 17))
                samples = sampler(rng)
                h, h_se = hill_alpha(samples, k)
                o, o_se, r2 = ols_tail_alpha(samples, k)
                hills.append(h)
                hill_ses.append(h_se)
                ols.append(o)
                ols_ses.append(o_se)
                r2s.append(r2)
            print(
                f"{case_name:12s} {k:2d} "
                f"{mean(hills):9.4f} {pstdev(hills):11.4f} {mean(hill_ses):13.4f} "
                f"{mean(ols):8.4f} {pstdev(ols):10.4f} {mean(ols_ses):12.4f} {mean(r2s):10.4f}"
            )


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


def phase_defect(g: complex, p: complex) -> float:
    return math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)


def run_lengths(flags: list[bool]) -> list[int]:
    out = []
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


def ht_transfer(samples: int, prime_count: int, seed: int) -> None:
    node_sig = "few extreme drawdowns understate tail-index uncertainty"
    candidates = [
        "few extreme phase-defect runs understate tail-index uncertainty",
        "few zero-shadow extremes understate exponent uncertainty",
        "few seam lifetime extremes understate power-tail certainty",
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
    print("\nSTEP9 method=9 small cases: HT tail-index uncertainty")
    print("kind sigma run_count max_run top_k hill_alpha hill_naive_se ols_alpha ols_se ols_r2")
    for sigma in [0.3, 0.5, 1.2]:
        series: dict[str, list[float]] = {"true": [], "finite": [], "random": []}
        for i in range(samples):
            t = 80.0 + 0.05 * i
            s = complex(float(sigma), t)
            g = gamma_part(s)
            z = dlog_zeta(s)
            f = dlog_finite_euler(s, primes)
            theta = rng.uniform(-math.pi, math.pi)
            r = abs(z) * complex(math.cos(theta), math.sin(theta))
            series["true"].append(phase_defect(g, z))
            series["finite"].append(phase_defect(g, f))
            series["random"].append(phase_defect(g, r))
        for kind, vals in series.items():
            ordered = sorted(vals)
            threshold = ordered[int(0.75 * (len(ordered) - 1))]
            flags = [value <= threshold for value in vals]
            lengths = run_lengths(flags)
            if len(lengths) < 6:
                print(f"{kind:6s} {sigma:.1f} {len(lengths):9d} {max(lengths) if lengths else 0:7d} insufficient")
                continue
            for k in [min(5, len(lengths) - 1), min(10, len(lengths) - 1)]:
                if k < 3:
                    continue
                h, hse = hill_alpha([float(x) for x in lengths], k)
                o, ose, r2 = ols_tail_alpha([float(x) for x in lengths], k)
                print(
                    f"{kind:6s} {sigma:.1f} {len(lengths):9d} {max(lengths):7d} {k:5d} "
                    f"{h:10.4f} {hse:13.4f} {o:9.4f} {ose:7.4f} {r2:6.3f}"
                )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--reps", type=int, default=400)
    parser.add_argument("--n", type=int, default=800)
    parser.add_argument("--ht-samples", type=int, default=700)
    parser.add_argument("--prime-count", type=int, default=60)
    parser.add_argument("--seed", type=int, default=3142228065337374667 % (2**32))
    args = parser.parse_args()
    summarize_node(args.reps, args.n, args.seed)
    ht_transfer(args.ht_samples, args.prime_count, args.seed + 1)


if __name__ == "__main__":
    main()
