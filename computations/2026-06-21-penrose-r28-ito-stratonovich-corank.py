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
    mu = 0.04
    sigma = 0.85
    tmax = 1.0
    steps = 800
    dt = tmax / steps
    paths = 7000
    dW = rng.normal(0.0, math.sqrt(dt), size=(paths, steps))
    # Same written SDE dX = mu X dt + sigma X dW. Ito and Stratonovich differ in log drift.
    x_ito = np.ones(paths)
    x_strat = np.ones(paths)
    for k in range(steps):
        dw = dW[:, k]
        x_ito += mu * x_ito * dt + sigma * x_ito * dw
        # Stratonovich midpoint, equivalent Ito drift mu + 0.5 sigma^2 for b(x)=sigma x.
        x_strat += (mu + 0.5 * sigma * sigma) * x_strat * dt + sigma * x_strat * dw
        x_ito = np.maximum(x_ito, 1e-30)
        x_strat = np.maximum(x_strat, 1e-30)
    return {
        "ito_mean_log": float(np.mean(np.log(x_ito))),
        "strat_mean_log": float(np.mean(np.log(x_strat))),
        "theory_ito_log": mu * tmax - 0.5 * sigma * sigma * tmax,
        "theory_strat_log": mu * tmax,
        "mean_x_ito": float(np.mean(x_ito)),
        "mean_x_strat": float(np.mean(x_strat)),
    }


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


def finite_logder(s, n=80, phases=None):
    total = 0j
    for i, p in enumerate(PRIMES[:n]):
        logp = math.log(p)
        ph = 1.0 if phases is None else phases[i]
        x = ph * complex(mp.e ** (-s * logp))
        total += -logp * x / (1 - x)
    return total


def robust01(vals):
    arr = np.asarray(vals, dtype=float)
    lo, hi = np.percentile(arr, [10, 90])
    if hi - lo < 1e-12:
        return np.zeros_like(arr)
    return np.clip((arr - lo) / (hi - lo), 0, 1)


def prime_feature_matrix(ts, sigma, n):
    rows = []
    for t in ts:
        s = complex(sigma, t)
        row = []
        for p in PRIMES[:n]:
            logp = math.log(p)
            x = np.exp(-s * logp)
            c = -logp * x / (1 - x)
            row.append(c.real)
        rows.append(row)
    return np.asarray(rows, dtype=float)


def effective_rank(mat):
    x = np.asarray(mat, dtype=float)
    x = x - np.mean(x, axis=0, keepdims=True)
    cov = x.T @ x / max(1, x.shape[0] - 1)
    vals = np.linalg.eigvalsh(cov)
    vals = vals[vals > 1e-12]
    if len(vals) == 0:
        return 0.0
    return float((np.sum(vals) ** 2) / np.sum(vals**2))


def carrier_b(kind, ts, sigma, n=80, seed=0):
    phases = None
    if kind == "random":
        rng = random.Random(seed)
        phases = [complex(math.cos(rng.random() * 2 * math.pi), math.sin(rng.random() * 2 * math.pi)) for _ in PRIMES]
    vals = []
    for t in ts:
        s = mp.mpc(sigma, t)
        if kind == "true":
            v = gamma_part(s) + zeta_logder(s)
        elif kind == "finite":
            v = gamma_part(s) + finite_logder(s, n=n)
        elif kind == "random":
            v = gamma_part(s) + finite_logder(s, n=n, phases=phases)
        elif kind == "constant":
            vals.append(1.0)
            continue
        else:
            raise ValueError(kind)
        vals.append(math.log1p(abs(v)))
    if kind == "constant":
        return np.ones(len(ts))
    return 0.25 + 1.75 * robust01(vals)


def ito_strato_dimension(kind, window, sigma=0.5, n=80):
    ts = np.linspace(window[0], window[1], 120)
    feat = prime_feature_matrix(ts, sigma, n)
    dfeat = np.diff(feat, axis=0)
    b = carrier_b(kind, ts, sigma, n=n, seed=int(window[0]))
    ito = b[:-1, None] * dfeat
    strat = 0.5 * (b[:-1] + b[1:])[:, None] * dfeat
    return effective_rank(ito), effective_rank(strat), float(np.mean(np.abs(strat - ito))), float(np.max(np.abs(np.diff(b))))


def transfer_experiment():
    rows = []
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for n in [30, 60, 100]:
            for kind in ["constant", "true", "finite", "random"]:
                ito, strat, stepdiff, maxdb = ito_strato_dimension(kind, window, n=n)
                rows.append(
                    {
                        "window": f"{int(window[0])}-{int(window[1])}",
                        "n": n,
                        "kind": kind,
                        "ito_rank": ito,
                        "strat_rank": strat,
                        "rank_delta": strat - ito,
                        "stepdiff": stepdiff,
                        "maxdb": maxdb,
                    }
                )
    return rows


if __name__ == "__main__":
    node = node_validation()
    print("NODE VALIDATION: state-dependent noise interpretation changes the result")
    print(
        "ito_mean_log={ito_mean_log:.6f} theory={theory_ito_log:.6f} "
        "strat_mean_log={strat_mean_log:.6f} theory={theory_strat_log:.6f} "
        "mean_x_ito={mean_x_ito:.6f} mean_x_strat={mean_x_strat:.6f}".format(**node)
    )
    target = "ito_stratonovich_state_dependent_noise"
    attempts = [
        "ito_stratonovich_weight_torus_corank",
        "state_dependent_phase_noise_dimW",
        "stochastic_calculus_prime_log_connection",
    ]
    print("\nSTEP 8 LEVENSHTEIN")
    for a in attempts:
        print(f"{a}: {levenshtein(target, a)}")
    print(f"chosen={min(attempts, key=lambda a: levenshtein(target, a))}")
    print("\nTARGET TOPIC: docs/consolidated/01-landscape-and-geometry.md lines 116-121, G4 weight/Tate torus dim W = corank")
    print("STEP 9 method 10: test extreme cases")
    for r in transfer_experiment():
        print(
            "window={window} n={n} kind={kind} ito_rank={ito_rank:.4f} "
            "strat_rank={strat_rank:.4f} delta={rank_delta:+.4f} "
            "mean_stepdiff={stepdiff:.6f} max_db={maxdb:.6f}".format(**r)
        )
