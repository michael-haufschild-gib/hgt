#!/usr/bin/env python3
"""STEP 11 boundary classification for inlet-wall smoothing metaphor."""

import argparse
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


def dlog_finite(s, primes):
    out = 0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def line(kind, sigma, ts, primes):
    vals = []
    for t in ts:
        s = complex(float(sigma), float(t))
        if kind == "true":
            z = dlog_zeta(s)
        elif kind == "finite":
            z = dlog_finite(s, primes)
        elif kind == "gamma":
            z = gamma_part(s)
        else:
            raise ValueError(kind)
        vals.append(math.log1p(abs(z)))
    return np.array(vals, dtype=float)


def smooth(vals, dt, tau):
    alpha = 1.0 - math.exp(-dt / tau)
    out = np.zeros_like(vals)
    out[0] = vals[0]
    for i in range(1, len(vals)):
        out[i] = (1.0 - alpha) * out[i - 1] + alpha * vals[i]
    return out


def stats(vals, tau, dt):
    sm = smooth(vals, dt, tau)
    rel = np.abs(sm - vals) / np.maximum(vals, 1e-12)
    return float(np.median(rel)), float(np.max(sm) / max(np.max(vals), 1e-300))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=220)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    primes = first_primes(args.prime_count)
    windows = [(14.0, 84.0), (100.0, 170.0), (500.0, 570.0)]
    sigmas = [0.2, 0.3, 0.5, 0.7, 0.8, 1.2]
    taus = [0.5, 1.5, 4.0]
    print("STEP11 inlet-wall boundary classification, method 23")
    print("columns: window sigma tau true_med finite_med gamma_med true_capture finite_capture boundary_class")
    for w in windows:
        ts = np.linspace(w[0], w[1], args.samples)
        dt = float(ts[1] - ts[0])
        for sigma in sigmas:
            lines = {kind: line(kind, sigma, ts, primes) for kind in ["true", "finite", "gamma"]}
            for tau in taus:
                med_t, cap_t = stats(lines["true"], tau, dt)
                med_f, cap_f = stats(lines["finite"], tau, dt)
                med_g, cap_g = stats(lines["gamma"], tau, dt)
                if med_t > 1.5 * med_f and cap_t < cap_f - 0.1:
                    cls = "true-more-inlet-biased"
                elif abs(med_t - med_f) < 0.03 and abs(cap_t - cap_f) < 0.05:
                    cls = "collapse"
                else:
                    cls = "mixed"
                print(
                    f"window=[{w[0]:.0f},{w[1]:.0f}] sigma={sigma:.1f} tau={tau:.1f} "
                    f"true_med={med_t:.5g} finite_med={med_f:.5g} gamma_med={med_g:.5g} "
                    f"true_capture={cap_t:.5g} finite_capture={cap_f:.5g} class={cls}"
                )


if __name__ == "__main__":
    main()
