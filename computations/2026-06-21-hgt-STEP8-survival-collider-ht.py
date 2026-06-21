#!/usr/bin/env python3
"""STEP 8 HT transfer for survival-conditioning collider bias."""

import argparse
import math

import mpmath as mp
import numpy as np


ATTEMPTS = {
    "component-survival-collider": (
        "Replace independent source variables by Gamma_infty and prime-side component magnitudes; "
        "condition on survival of the combined continuum differential readout."
    ),
    "phase-defect-survivor": (
        "Replace survival with passing a phase-carrier defect gate in the archimedean-prime weld; "
        "measure induced correlations among component amplitudes."
    ),
    "zero-shadow-conditioning": (
        "Replace survival by avoiding zero-shadow low-amplitude valleys along the vertical line; "
        "test whether conditioning changes component correlations."
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
    node_core = "hidden collider bias introduced by conditioning on survival"
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


def corr(a, b):
    a = np.asarray(a, dtype=float)
    b = np.asarray(b, dtype=float)
    if np.std(a) < 1e-12 or np.std(b) < 1e-12:
        return 0.0
    return float(np.corrcoef(a, b)[0, 1])


def component_data(kind, sigma, ts, primes, rng):
    rows = []
    for t in ts:
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true":
            p = dlog_zeta(s)
        elif kind == "finite":
            p = dlog_finite(s, primes)
        elif kind == "random-phase":
            base = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(base) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        lg = math.log(abs(g) + 1e-300)
        lp = math.log(abs(p) + 1e-300)
        combined = math.log(abs(g + p) + 1e-300)
        defect = math.log(max(abs(g), abs(p)) + 1e-300) - combined
        rows.append((lg, lp, combined, max(0.0, defect)))
    return np.array(rows, dtype=float)


def run_attempt(args, selected):
    rng = np.random.default_rng(args.seed)
    primes = first_primes(args.prime_count)
    ts = np.linspace(args.t_min, args.t_max, args.samples)
    print(f"Selected attempt: {selected}")
    print("columns: sigma kind gate source_corr survivor_corr collider_shift survival_frac")
    for sigma in [0.2, 0.3, 0.5, 0.7, 1.2]:
        for kind in ["true", "finite", "random-phase"]:
            data = component_data(kind, sigma, ts, primes, rng)
            lg, lp, combined, defect = data.T
            source = corr(lg, lp)
            gates = {}
            if selected == "component-survival-collider":
                gates["combined_top25"] = combined >= np.quantile(combined, 0.75)
                gates["combined_bottom25"] = combined <= np.quantile(combined, 0.25)
            elif selected == "phase-defect-survivor":
                gates["defect_top25"] = defect >= np.quantile(defect, 0.75)
                gates["defect_positive"] = defect > 0.0
            else:
                gates["avoid_zero_shadow"] = combined >= np.quantile(combined, 0.25)
                gates["deep_zero_shadow"] = combined <= np.quantile(combined, 0.10)
            for gate_name, mask in gates.items():
                if int(mask.sum()) < 5:
                    survivor = 0.0
                else:
                    survivor = corr(lg[mask], lp[mask])
                print(
                    f"sigma={sigma:.1f} {kind:12s} gate={gate_name:18s} "
                    f"source_corr={source:+.5f} survivor_corr={survivor:+.5f} "
                    f"collider_shift={survivor-source:+.5f} survival_frac={float(np.mean(mask)):.5f}"
                )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--t-min", type=float, default=100.0)
    parser.add_argument("--t-max", type=float, default=170.0)
    parser.add_argument("--samples", type=int, default=360)
    parser.add_argument("--prime-count", type=int, default=160)
    parser.add_argument("--seed", type=int, default=20260621)
    args = parser.parse_args()
    scored = choose_attempt()
    selected = scored[0][1]
    print("STEP8 survival-collider HT transfer")
    print("STEP9 method: 23 = Classify boundary cases")
    print("Boundary cases: left strip, critical line, right side, top-survival and bottom-survival gates.")
    print("attempt distances:")
    for dist, name, desc in scored:
        marker = "SELECTED" if name == selected else "not-selected"
        print(f"  {name}: levenshtein={dist} {marker}; {desc}")
    print()
    run_attempt(args, selected)


if __name__ == "__main__":
    main()
