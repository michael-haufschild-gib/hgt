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


def fit_rmse(xcols, y):
    X = np.column_stack([np.ones(len(y))] + xcols)
    beta, *_ = np.linalg.lstsq(X, y, rcond=None)
    pred = X @ beta
    return float(np.sqrt(np.mean((y - pred) ** 2))), beta


def node_validation():
    rng = np.random.default_rng(20260621)
    L = np.array([16, 24, 32, 48, 64, 96, 128, 192, 256, 384], dtype=float)
    rows = []
    for p in [0.0, 0.35, 0.80]:
        y = 2.0 * L ** (-0.62) * np.log(L) ** p
        y *= np.exp(0.03 * rng.normal(size=len(L)))
        ly = np.log(y)
        lp = np.log(L)
        ll = np.log(np.log(L))
        rmse_power, bp = fit_rmse([lp], ly)
        rmse_log, bl = fit_rmse([lp, ll], ly)
        rows.append((p, rmse_power, rmse_log, bl[2]))
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


def robust(values):
    arr = np.asarray(values, dtype=float)
    med = np.median(arr)
    q25, q75 = np.percentile(arr, [25, 75])
    return (arr - med) / (q75 - q25 + 1e-12)


def signal_bundle(sigma, t0, t1, npts=160):
    ts = np.linspace(t0, t1, npts)
    rng = random.Random(int(t0 + sigma * 1000))
    phases = [complex(math.cos(rng.random() * 2 * math.pi), math.sin(rng.random() * 2 * math.pi)) for _ in PRIMES]
    vals = {k: [] for k in ["sourceA", "sourceB", "sum", "weld", "finite_weld", "random_weld"]}
    for t in ts:
        s = mp.mpc(sigma, t)
        g = gamma_part(s)
        p = zeta_logder(s)
        pf = finite_logder(s, n=90)
        pr = finite_logder(s, n=90, phases=phases)
        vals["sourceA"].append(math.log1p(abs(g)))
        vals["sourceB"].append(math.log1p(abs(p)))
        vals["sum"].append(math.log1p(abs(g + p)))
        vals["weld"].append(max(math.log(abs(g) + 1e-14), math.log(abs(p) + 1e-14)) - math.log(abs(g + p) + 1e-14))
        vals["finite_weld"].append(max(math.log(abs(g) + 1e-14), math.log(abs(pf) + 1e-14)) - math.log(abs(g + pf) + 1e-14))
        vals["random_weld"].append(max(math.log(abs(g) + 1e-14), math.log(abs(pr) + 1e-14)) - math.log(abs(g + pr) + 1e-14))
    return {k: robust(v) for k, v in vals.items()}


def block_variances(x):
    x = np.asarray(x, dtype=float)
    rows = []
    for b in [2, 4, 8, 16, 32, 64]:
        n = len(x) // b
        means = x[: n * b].reshape(n, b).mean(axis=1)
        rows.append((b, float(np.var(means) + 1e-12)))
    return rows


def scaling_fit(x):
    rows = block_variances(x)
    B = np.array([r[0] for r in rows], dtype=float)
    V = np.array([r[1] for r in rows], dtype=float)
    y = np.log(V)
    lb = np.log(B)
    ll = np.log(np.log(B + 1.0))
    rmse_power, bp = fit_rmse([lb], y)
    rmse_log, bl = fit_rmse([lb, ll], y)
    return rmse_power, rmse_log, bl[2], float((rmse_power - rmse_log) / (rmse_power + 1e-12))


def transfer_experiment():
    rows = []
    for sigma in [0.5, 1.2]:
        for window in [(100.0, 260.0)]:
            bundle = signal_bundle(sigma, window[0], window[1])
            for kind, x in bundle.items():
                rp, rl, q, gain = scaling_fit(x)
                rows.append((sigma, f"{int(window[0])}-{int(window[1])}", kind, rp, rl, q, gain))
    return rows


if __name__ == "__main__":
    print("NODE VALIDATION: upper-critical scaling needs log corrections")
    for p, rp, rl, q in node_validation():
        print(f"log_power={p:.2f} rmse_power={rp:.5f} rmse_powerlog={rl:.5f} fitted_log_coeff={q:.3f}")

    target = "upper_critical_dimension_log_corrections"
    attempts = [
        "weld_block_scaling_log_correction",
        "completed_log_derivative_marginal_scaling",
        "sourceA_sourceB_powerlaw_vs_weld_log",
    ]
    print("\nSTEP 8 LEVENSHTEIN")
    for a in attempts:
        print(f"{a}: {levenshtein(target, a)}")
    print(f"chosen={min(attempts, key=lambda a: levenshtein(target, a))}")

    print("\nTARGET TOPIC: native content is the archimedean-prime weld, not Source A or Source B alone")
    print("STEP 9 method 22: compare nearby false statements (power law only vs power law with log correction)")
    for sigma, window, kind, rp, rl, q, gain in transfer_experiment():
        print(
            f"sigma={sigma:.1f} window={window} kind={kind} "
            f"rmse_power={rp:.5f} rmse_log={rl:.5f} log_coeff={q:+.3f} gain={gain:.3f}"
        )
