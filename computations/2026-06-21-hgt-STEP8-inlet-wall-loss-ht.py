#!/usr/bin/env python3
"""STEP 8 HT transfer for inlet wall-loss / inlet-chemistry bias."""

import argparse
import math

import mpmath as mp
import numpy as np


ATTEMPTS = {
    "residence-backaction": (
        "Replace inlet residence time by measurement step size h; compare the "
        "ambient continuum derivative against instrument-biased finite-difference readout."
    ),
    "component-inlet-map": (
        "Replace atmospheric radical vector by the archimedean-prime component vector "
        "(Gamma_infty, P) and apply a first-order loss/conversion inlet matrix before summing."
    ),
    "wall-memory-smoothing": (
        "Replace inlet wall loss by one-sided residence-time smoothing along height t; "
        "compare ambient and wall-memory measurements of the continuum differential signal."
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
    node_core = (
        "inlet wall loss inlet chemistry residence time instrument bias measured radical "
        "vector exp A tau ambient state"
    )
    scored = []
    for name, desc in ATTEMPTS.items():
        scored.append((levenshtein(node_core, desc.lower()), name, desc))
    return sorted(scored)


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


def zeta_val(s):
    return complex(mp.fp.zeta(s))


def dlog_zeta(s, h):
    z0 = zeta_val(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite_euler(s, primes):
    out = 0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def dlog(kind, s, h, primes):
    if kind == "true":
        return dlog_zeta(s, h)
    if kind == "finite":
        return dlog_finite_euler(s, primes)
    if kind == "gamma":
        return gamma_part(s)
    raise ValueError(kind)


def residence_backaction(args, method_name):
    primes = first_primes(args.prime_count)
    ts = np.linspace(args.t_min, args.t_max, args.samples)
    sigmas = [0.3, 0.5, 0.7, 1.2]
    print(f"Selected attempt: {method_name}")
    print("Residence/backaction readout: compare h_ref=1e-5 with coarser instrument h.")
    print("columns: sigma kind h median_rel_bias q95_rel_bias max_rel_bias")
    for sigma in sigmas:
        for kind in ["gamma", "true", "finite"]:
            ambient = np.array([dlog(kind, complex(sigma, float(t)), 1e-5, primes) for t in ts])
            for h in [1e-4, 1e-3, 1e-2]:
                measured = np.array([dlog(kind, complex(sigma, float(t)), h, primes) for t in ts])
                rel = np.abs(measured - ambient) / np.maximum(np.abs(ambient), 1e-12)
                print(
                    f"sigma={sigma:.1f} {kind:6s} h={h:g} "
                    f"median={float(np.median(rel)):.5g} q95={float(np.quantile(rel,0.95)):.5g} max={float(np.max(rel)):.5g}"
                )


def component_inlet_map(args, method_name):
    primes = first_primes(args.prime_count)
    ts = np.linspace(args.t_min, args.t_max, args.samples)
    print(f"Selected attempt: {method_name}")
    print("Component inlet map on vector (Gamma_infty, P), then sum components.")
    print("columns: sigma kind residence loss conversion median_rel_bias phase_defect_shift")
    for sigma in [0.3, 0.5, 0.7, 1.2]:
        for kind in ["true", "finite"]:
            ambient_vals = []
            phase_ambient = []
            data = []
            for t in ts:
                s = complex(sigma, float(t))
                g = gamma_part(s)
                p = dlog(kind, s, 1e-4, primes)
                ambient_vals.append(abs(g + p))
                phase_ambient.append(math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))
                data.append((g, p))
            for residence, loss, conv in [(0.05, 0.2, 0.0), (0.20, 0.2, 0.4), (0.20, 0.6, 0.4)]:
                measured_vals = []
                phase_measured = []
                a = math.exp(-loss * residence)
                b = math.exp(-3.0 * loss * residence)
                for g, p in data:
                    gp = a * g + conv * residence * p
                    pp = b * p + 0.1 * conv * residence * g
                    measured_vals.append(abs(gp + pp))
                    phase_measured.append(math.log(max(abs(gp), abs(pp)) + 1e-300) - math.log(abs(gp + pp) + 1e-300))
                rel = np.abs(np.array(measured_vals) - np.array(ambient_vals)) / np.maximum(np.array(ambient_vals), 1e-12)
                shift = float(np.median(np.array(phase_measured) - np.array(phase_ambient)))
                print(
                    f"sigma={sigma:.1f} {kind:6s} residence={residence:.2f} loss={loss:.1f} conversion={conv:.1f} "
                    f"median_rel_bias={float(np.median(rel)):.5g} phase_defect_shift={shift:.5g}"
                )


def wall_memory_smoothing(args, method_name):
    primes = first_primes(args.prime_count)
    ts = np.linspace(args.t_min, args.t_max, args.samples)
    print(f"Selected attempt: {method_name}")
    print("One-sided wall-memory smoothing along t.")
    print("columns: sigma kind tau median_rel_bias peak_capture")
    for sigma in [0.3, 0.5, 0.7, 1.2]:
        for kind in ["true", "finite", "gamma"]:
            vals = np.array([math.log1p(abs(dlog(kind, complex(sigma, float(t)), 1e-4, primes))) for t in ts])
            for tau in [0.5, 1.5, 4.0]:
                smoothed = np.zeros_like(vals)
                alpha = 1.0 - math.exp(-(ts[1] - ts[0]) / tau)
                smoothed[0] = vals[0]
                for i in range(1, len(vals)):
                    smoothed[i] = (1.0 - alpha) * smoothed[i - 1] + alpha * vals[i]
                rel = np.abs(smoothed - vals) / np.maximum(vals, 1e-12)
                print(
                    f"sigma={sigma:.1f} {kind:6s} tau={tau:.1f} median_rel_bias={float(np.median(rel)):.5g} "
                    f"peak_capture={float(np.max(smoothed)/max(np.max(vals),1e-300)):.5g}"
                )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--t-min", type=float, default=100.0)
    parser.add_argument("--t-max", type=float, default=170.0)
    parser.add_argument("--samples", type=int, default=220)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()

    scored = choose_attempt()
    selected = scored[0][1]
    print("STEP8 inlet wall-loss HT transfer")
    print("STEP9 method: 1 = Split it into subclaims")
    print("Subclaims tested: instrument bias exists; bias differs by function class; stronger instrument residence/backaction increases distortion.")
    print("attempt distances:")
    for dist, name, desc in scored:
        marker = "SELECTED" if name == selected else "not-selected"
        print(f"  {name}: levenshtein={dist} {marker}; {desc}")
    print()

    if selected == "residence-backaction":
        residence_backaction(args, selected)
    elif selected == "component-inlet-map":
        component_inlet_map(args, selected)
    else:
        wall_memory_smoothing(args, selected)


if __name__ == "__main__":
    main()
