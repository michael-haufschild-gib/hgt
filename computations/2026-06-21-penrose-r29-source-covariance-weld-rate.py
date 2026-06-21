#!/usr/bin/env python3
import math
import random

import mpmath as mp
import numpy as np

mp.mp.dps = 32


def levenshtein(a, b):
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_validation():
    rng = np.random.default_rng(20260621)
    rows = []
    mean_x = 10.0
    mean_y = 8.0
    for rho in [-0.8, -0.4, 0.0, 0.4, 0.8]:
        z1 = rng.normal(size=200000)
        z2 = rho * z1 + math.sqrt(max(0.0, 1 - rho * rho)) * rng.normal(size=200000)
        x = np.exp(math.log(mean_x) - 0.5 * 0.25 + 0.5 * z1)
        y = np.exp(math.log(mean_y) - 0.5 * 0.25 + 0.5 * z2)
        rate = float(np.mean(x * y))
        marginal = float(np.mean(x) * np.mean(y))
        rows.append((rho, rate, marginal, rate / marginal))
    return rows


def first_primes(n):
    primes = []
    x = 2
    while len(primes) < n:
        ok = True
        for p in primes:
            if p * p > x:
                break
            if x % p == 0:
                ok = False
                break
        if ok:
            primes.append(x)
        x += 1
    return primes


PRIMES = first_primes(120)


def zeta_logder(s):
    h = mp.mpf("1e-5")
    z0 = mp.zeta(s)
    return complex((mp.zeta(s + h) - mp.zeta(s - h)) / (2 * h) / z0)


def gamma_part(s):
    return complex(0.5 * mp.digamma(s / 2.0) - 0.5 * mp.log(mp.pi))


def finite_logder(s, n=90, phases=None):
    total = 0j
    for i, p in enumerate(PRIMES[:n]):
        logp = math.log(p)
        ph = 1.0 if phases is None else phases[i]
        x = ph * complex(mp.e ** (-s * logp))
        total += -logp * x / (1 - x)
    return total


def source_arrays(kind, sigma, window, n=90):
    ts = np.linspace(window[0], window[1], 160)
    phases = None
    if kind == "random":
        rng = random.Random(int(window[0] * 10 + sigma * 1000))
        phases = [complex(math.cos(rng.random() * 2 * math.pi), math.sin(rng.random() * 2 * math.pi)) for _ in PRIMES]
    a = []
    b = []
    for t in ts:
        s = mp.mpc(sigma, t)
        g = gamma_part(s)
        if kind == "true":
            p = zeta_logder(s)
        elif kind == "finite":
            p = finite_logder(s, n=n)
        elif kind == "random":
            p = finite_logder(s, n=n, phases=phases)
        else:
            raise ValueError(kind)
        a.append(g)
        b.append(p)
    return np.asarray(a, dtype=complex), np.asarray(b, dtype=complex)


def covariance_rate(kind, sigma, window, n=90):
    a, b = source_arrays(kind, sigma, window, n=n)
    cross = np.real(a * np.conjugate(b))
    product_cross = np.real(np.mean(a) * np.conjugate(np.mean(b)))
    cov = float(np.mean(cross) - product_cross)
    actual = float(np.mean(np.abs(a + b) ** 2))
    marginal = float(np.mean(np.abs(a) ** 2) + np.mean(np.abs(b) ** 2) + 2 * product_cross)
    shuffled = []
    for shift in [11, 23, 37, 53]:
        bs = np.roll(b, shift)
        shuffled.append(float(np.mean(np.abs(a + bs) ** 2)))
    shuf_mean = float(np.mean(shuffled))
    return {
        "cov_cross": cov,
        "actual_power": actual,
        "marginal_power": marginal,
        "actual_minus_marginal": actual - marginal,
        "actual_minus_shuffle": actual - shuf_mean,
        "corr": float(np.corrcoef(np.real(a), np.real(b))[0, 1]),
    }


if __name__ == "__main__":
    print("NODE VALIDATION: correlated reactants change effective rate E[XY] vs E[X]E[Y]")
    for rho, rate, marginal, ratio in node_validation():
        print(f"rho={rho:+.1f} rate={rate:.4f} marginal={marginal:.4f} ratio={ratio:.4f}")

    target = "correlated_reactants_effective_rate"
    attempts = [
        "sourceA_sourceB_reactant_covariance_weld_rate",
        "gamma_prime_covariance_effective_cancellation",
        "seam_cross_term_reaction_rate",
    ]
    print("\nSTEP 8 LEVENSHTEIN")
    for a in attempts:
        print(f"{a}: {levenshtein(target, a)}")
    print(f"chosen={min(attempts, key=lambda a: levenshtein(target, a))}")

    print("\nTARGET TOPIC: docs/consolidated/01-landscape-and-geometry.md §1 two sources and seam")
    print("STEP 9 method 8: compare similar source-pair reaction systems")
    for window in [(100.0, 170.0), (500.0, 570.0), (900.0, 970.0)]:
        for sigma in [0.3, 0.5, 0.7, 1.2]:
            parts = {}
            for kind in ["true", "finite", "random"]:
                r = covariance_rate(kind, sigma, window)
                parts[kind] = r
            print(
                f"window={int(window[0])}-{int(window[1])} sigma={sigma:.1f} "
                f"true_cov={parts['true']['cov_cross']:+.4f} finite_cov={parts['finite']['cov_cross']:+.4f} random_cov={parts['random']['cov_cross']:+.4f} "
                f"true_dMarg={parts['true']['actual_minus_marginal']:+.4f} finite_dMarg={parts['finite']['actual_minus_marginal']:+.4f} random_dMarg={parts['random']['actual_minus_marginal']:+.4f} "
                f"true_dShuf={parts['true']['actual_minus_shuffle']:+.4f} finite_dShuf={parts['finite']['actual_minus_shuffle']:+.4f} random_dShuf={parts['random']['actual_minus_shuffle']:+.4f}"
            )
