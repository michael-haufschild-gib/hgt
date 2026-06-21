#!/usr/bin/env python3
"""STEP 8 HT transfer for HMM transition estimates absorbing observation bias."""

import argparse
import math

import mpmath as mp
import numpy as np


ATTEMPTS = {
    "threshold-transition": (
        "Replace hidden Markov state by high/low regimes of a continuum differential readout; "
        "let biased thresholds make observed transition estimates absorb emission error."
    ),
    "phase-emission": (
        "Replace emissions by phase-carrier signs in the Gamma-prime weld; estimate transition "
        "rates after biased phase observation."
    ),
    "missingness-chain": (
        "Replace emission bias by state-dependent missingness from coarse sampling along height; "
        "compare inferred persistence of observed regimes."
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
    node_core = "hidden Markov transition estimates absorb systematic observation emission bias"
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


def readout(kind, sigma, ts, primes, mode):
    vals = []
    for t in ts:
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        p = dlog_zeta(s) if kind == "true" else dlog_finite(s, primes)
        if mode == "amp":
            vals.append(math.log1p(abs(p)))
        elif mode == "phase":
            vals.append(max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)))
        else:
            c = (g * p.conjugate()).real / max(abs(g) * abs(p), 1e-300)
            vals.append(max(0.0, -float(c)))
    return np.array(vals, dtype=float)


def smooth(vals, width):
    if width <= 1:
        return vals.copy()
    kernel = np.ones(width) / width
    return np.convolve(vals, kernel, mode="same")


def transition_rates(states):
    counts = np.ones((2, 2))
    for a, b in zip(states[:-1], states[1:]):
        counts[int(a), int(b)] += 1.0
    mat = counts / counts.sum(axis=1, keepdims=True)
    return float(mat[0, 1]), float(mat[1, 0])


def run_attempt(args, selected):
    primes = first_primes(args.prime_count)
    ts = np.linspace(args.t_min, args.t_max, args.samples)
    if selected == "phase-emission":
        mode = "phase"
    elif selected == "missingness-chain":
        mode = "cos"
    else:
        mode = "amp"
    print(f"Selected attempt: {selected}; readout={mode}")
    print("columns: sigma kind threshold_shift blur true_p01 true_p10 observed_p01 observed_p10 bias01 bias10")
    for sigma in [0.3, 0.5, 0.7, 1.2]:
        for kind in ["true", "finite"]:
            vals = readout(kind, sigma, ts, primes, mode)
            base_threshold = float(np.quantile(vals, 0.75))
            true_states = vals > base_threshold
            true_p01, true_p10 = transition_rates(true_states)
            for threshold_shift, blur in [(-0.15, 1), (0.0, 1), (0.15, 5), (0.30, 9)]:
                obs_vals = smooth(vals, blur)
                threshold = base_threshold + threshold_shift * max(float(np.std(vals)), 1e-12)
                obs_states = obs_vals > threshold
                obs_p01, obs_p10 = transition_rates(obs_states)
                print(
                    f"sigma={sigma:.1f} {kind:6s} shift={threshold_shift:+.2f} blur={blur:d} "
                    f"true_p01={true_p01:.5g} true_p10={true_p10:.5g} "
                    f"obs_p01={obs_p01:.5g} obs_p10={obs_p10:.5g} "
                    f"bias01={obs_p01-true_p01:+.5g} bias10={obs_p10-true_p10:+.5g}"
                )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--t-min", type=float, default=100.0)
    parser.add_argument("--t-max", type=float, default=170.0)
    parser.add_argument("--samples", type=int, default=420)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    scored = choose_attempt()
    selected = scored[0][1]
    print("STEP8 HMM transition-bias HT transfer")
    print("STEP9 method: 13 = Find a monotone quantity")
    print("Monotone knobs tested: threshold_shift and blur width as increasing observation bias.")
    print("attempt distances:")
    for dist, name, desc in scored:
        marker = "SELECTED" if name == selected else "not-selected"
        print(f"  {name}: levenshtein={dist} {marker}; {desc}")
    print()
    run_attempt(args, selected)


if __name__ == "__main__":
    main()
