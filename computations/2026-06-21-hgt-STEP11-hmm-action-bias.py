#!/usr/bin/env python3
"""STEP 11 action test for HMM transition-bias metaphor."""

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


def phase_signal(kind, sigma, ts, primes, rng):
    vals = []
    for t in ts:
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true":
            p = dlog_zeta(s)
        elif kind == "finite":
            p = dlog_finite(s, primes)
        else:
            base = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(base) * complex(math.cos(theta), math.sin(theta))
        vals.append(max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)))
    return np.array(vals, dtype=float)


def smooth(vals, width):
    if width <= 1:
        return vals
    return np.convolve(vals, np.ones(width) / width, mode="same")


def events(states):
    runs = []
    start = None
    for i, val in enumerate(states):
        if val and start is None:
            start = i
        if start is not None and (not val or i == len(states) - 1):
            end = i if not val else i + 1
            runs.append((start, end))
            start = None
    return runs


def event_stats(states):
    ev = events(states)
    total_on = sum(e - s for s, e in ev)
    dwell = float(np.mean([e - s for s, e in ev])) if ev else 0.0
    transitions = int(np.sum(states[1:] != states[:-1]))
    return len(ev), total_on, dwell, transitions


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=420)
    parser.add_argument("--prime-count", type=int, default=160)
    parser.add_argument("--seed", type=int, default=20260621)
    args = parser.parse_args()
    rng = np.random.default_rng(args.seed)
    primes = first_primes(args.prime_count)
    ts = np.linspace(100.0, 170.0, args.samples)
    print("STEP11 HMM action test, method 6 = ask what action is happening")
    print("Action candidates: deleting events, merging events, or creating false persistence.")
    print("columns: sigma kind blur events_before events_after on_before on_after dwell_before dwell_after transitions_before transitions_after action")
    for sigma in [0.3, 0.5, 0.7, 1.2]:
        for kind in ["true", "finite", "random-phase"]:
            vals = phase_signal(kind, sigma, ts, primes, rng)
            threshold = float(np.quantile(vals, 0.75))
            before = vals > threshold
            b_events, b_on, b_dwell, b_trans = event_stats(before)
            for blur in [3, 7, 13]:
                after = smooth(vals, blur) > threshold
                a_events, a_on, a_dwell, a_trans = event_stats(after)
                if a_events < b_events and a_on <= b_on:
                    action = "delete"
                elif a_events < b_events and a_dwell > b_dwell:
                    action = "merge"
                elif a_on > b_on and a_trans < b_trans:
                    action = "false-persistence"
                else:
                    action = "mixed"
                print(
                    f"sigma={sigma:.1f} {kind:12s} blur={blur:2d} events_before={b_events:3d} events_after={a_events:3d} "
                    f"on_before={b_on:3d} on_after={a_on:3d} dwell_before={b_dwell:.3g} dwell_after={a_dwell:.3g} "
                    f"transitions_before={b_trans:3d} transitions_after={a_trans:3d} action={action}"
                )


if __name__ == "__main__":
    main()
