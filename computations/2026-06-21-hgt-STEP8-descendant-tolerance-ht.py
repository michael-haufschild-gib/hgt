#!/usr/bin/env python3
"""STEP 8 HT transfer for descendant tolerance mismatch."""

import argparse
import math

import mpmath as mp
import numpy as np


ATTEMPTS = {
    "descendant-proxy-strip": (
        "Replace modern descendants by surviving easy proxies such as finite Euler or right-side strip samples; "
        "test whether their tolerance readouts match the extinct/left-strip true analytic relative."
    ),
    "completion-drift-family": (
        "Replace descendant adaptation by beta-drift in the completion family beta*Gamma_infty plus prime component; "
        "compare tolerance before and after the filter."
    ),
    "refuge-conditioned-collider": (
        "Replace refuge access by a gate on low-exposure continuum windows; condition on surviving windows and "
        "test whether proxy tolerance becomes biased."
    ),
}


def levenshtein(a, b):
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def choose_attempt():
    node_core = "environmental tolerance inferred from modern descendants may not match extinct relatives"
    return sorted((levenshtein(node_core, desc.lower()), name, desc) for name, desc in ATTEMPTS.items())


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


def dlog_finite(s, primes):
    out = 0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def tolerance(kind, sigma, ts, primes, beta=1.0):
    vals = []
    for t in ts:
        s = complex(float(sigma), float(t))
        g = beta * gamma_part(s)
        if kind == "true":
            p = dlog_zeta(s)
        elif kind == "finite":
            p = dlog_finite(s, primes)
        elif kind == "gamma":
            p = 0j
        else:
            raise ValueError(kind)
        amp = math.log1p(abs(g + p))
        phase_defect = max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))
        vals.append((amp, phase_defect))
    return np.array(vals)


def corr(a, b):
    if np.std(a) < 1e-12 or np.std(b) < 1e-12:
        return 0.0
    return float(np.corrcoef(a, b)[0, 1])


def run(args, selected):
    primes = first_primes(args.prime_count)
    ts = np.linspace(args.t_min, args.t_max, args.samples)
    print(f"Selected attempt: {selected}")
    if selected == "completion-drift-family":
        print("columns: window_sigma beta target_phase proxy_phase bias corr_amp")
        for sigma in [0.3, 0.5, 0.7, 1.2]:
            target = tolerance("true", sigma, ts, primes, beta=1.0)
            for beta in [0.0, 0.5, 1.0, 2.0]:
                prox = tolerance("true", sigma, ts, primes, beta=beta)
                print(
                    f"sigma={sigma:.1f} beta={beta:.1f} target_phase={float(np.median(target[:,1])):.5g} "
                    f"proxy_phase={float(np.median(prox[:,1])):.5g} bias={float(np.median(prox[:,1]-target[:,1])):+.5g} "
                    f"corr_amp={corr(target[:,0], prox[:,0]):+.5f}"
                )
    elif selected == "refuge-conditioned-collider":
        print("columns: sigma kind refuge_frac source_phase survivor_phase bias")
        for sigma in [0.3, 0.5, 0.7, 1.2]:
            for kind in ["true", "finite"]:
                dat = tolerance(kind, sigma, ts, primes)
                refuge = dat[:, 0] <= np.quantile(dat[:, 0], 0.30)
                print(
                    f"sigma={sigma:.1f} {kind:6s} refuge_frac={float(np.mean(refuge)):.3f} "
                    f"source_phase={float(np.median(dat[:,1])):.5g} survivor_phase={float(np.median(dat[refuge,1])):.5g} "
                    f"bias={float(np.median(dat[refuge,1])-np.median(dat[:,1])):+.5g}"
                )
    else:
        print("columns: target_sigma proxy_kind proxy_sigma target_phase proxy_phase bias corr_amp corr_phase")
        for target_sigma in [0.3, 0.5, 0.7]:
            target = tolerance("true", target_sigma, ts, primes)
            for proxy_kind, proxy_sigma in [("finite", target_sigma), ("true", 1.2), ("finite", 1.2), ("gamma", target_sigma)]:
                prox = tolerance(proxy_kind, proxy_sigma, ts, primes)
                print(
                    f"target_sigma={target_sigma:.1f} proxy={proxy_kind:6s}@{proxy_sigma:.1f} "
                    f"target_phase={float(np.median(target[:,1])):.5g} proxy_phase={float(np.median(prox[:,1])):.5g} "
                    f"bias={float(np.median(prox[:,1]-target[:,1])):+.5g} "
                    f"corr_amp={corr(target[:,0], prox[:,0]):+.5f} corr_phase={corr(target[:,1], prox[:,1]):+.5f}"
                )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--t-min", type=float, default=100.0)
    parser.add_argument("--t-max", type=float, default=170.0)
    parser.add_argument("--samples", type=int, default=300)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    scored = choose_attempt()
    selected = scored[0][1]
    print("STEP8 descendant-tolerance HT transfer")
    print("STEP9 method: 2 = Attack it as false")
    print("Attack controls: finite Euler, right-side true/finite proxies, and gamma-only proxy.")
    print("attempt distances:")
    for dist, name, desc in scored:
        marker = "SELECTED" if name == selected else "not-selected"
        print(f"  {name}: levenshtein={dist} {marker}; {desc}")
    print()
    run(args, selected)


if __name__ == "__main__":
    main()
