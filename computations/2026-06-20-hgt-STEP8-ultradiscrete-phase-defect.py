#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 HT transfer.

NODE: ultradiscrete max-plus limits need a sign/parity carrier.

Minimal HT edit: change representation from scalar max-plus of positive
terms to a phase-aware tropical defect for the continuum differential weld

    d/ds log Lambda = Gamma_infty + prime_part.

The defect

    max(log|G|, log|P|) - log|G+P|

is positive when the max-plus magnitude forgets destructive phase/sign data.
"""

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


def zeta(s):
    return mp.fp.zeta(s)


def dlog_zeta(s, h=1e-4):
    z0 = zeta(s)
    return (zeta(s + h) - zeta(s - h)) / (2.0 * h * (z0 + 1e-300))


def gamma_part(s):
    return -0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0)


def dlog_finite_euler(s, primes):
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return out


def phase_defect(g, p):
    ag = abs(g)
    ap = abs(p)
    total = abs(g + p)
    if ag == 0.0 or ap == 0.0 or total == 0.0:
        cos = float("nan")
    else:
        cos = float((g * complex(p).conjugate()).real / (ag * ap))
    return math.log(max(ag, ap) + 1e-300) - math.log(total + 1e-300), cos, math.log((ap + 1e-300) / (ag + 1e-300))


def component(kind, s, primes):
    if kind == "true-zeta":
        return complex(dlog_zeta(s))
    if kind == "finite-euler":
        return complex(dlog_finite_euler(s, primes))
    raise ValueError(kind)


def summarize(kind, sigma, t_min, t_max, samples, primes):
    ts = np.linspace(t_min, t_max, samples)
    defects = []
    cosines = []
    log_ratios = []
    for t in ts:
        s = complex(float(sigma), float(t))
        g = complex(gamma_part(s))
        p = component(kind, s, primes)
        d, c, r = phase_defect(g, p)
        defects.append(d)
        cosines.append(c)
        log_ratios.append(r)
    arr = np.array(defects)
    cos = np.array(cosines)
    rat = np.array(log_ratios)
    positive = arr[arr > 0.0]
    return {
        "kind": kind,
        "sigma": sigma,
        "window": f"[{t_min:g},{t_max:g}]",
        "q50": float(np.quantile(arr, 0.50)),
        "q90": float(np.quantile(arr, 0.90)),
        "q99": float(np.quantile(arr, 0.99)),
        "frac_pos": float(np.mean(arr > 0.0)),
        "frac_big": float(np.mean(arr > 0.50)),
        "mean_pos": float(np.mean(positive)) if len(positive) else 0.0,
        "cos_q10": float(np.nanquantile(cos, 0.10)),
        "cos_q50": float(np.nanquantile(cos, 0.50)),
        "logratio_q50": float(np.quantile(rat, 0.50)),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=320)
    parser.add_argument("--prime-count", type=int, default=30)
    parser.add_argument("--sigmas", default="0.3,0.5,0.7")
    parser.add_argument("--windows", default="14:84,100:170,500:570")
    args = parser.parse_args()
    sigmas = [float(x) for x in args.sigmas.split(",")]
    primes = first_primes(args.prime_count)
    windows = []
    for item in args.windows.split(","):
        a, b = item.split(":")
        windows.append((float(a), float(b)))
    print("STEP8/9 ultradiscrete phase-defect probe")
    print("method=19 change-representation; defect=max(log|G|,log|P|)-log|G+P|")
    print(f"finite_euler_prime_count={args.prime_count}")
    print("kind sigma window q50 q90 q99 frac_pos frac_gt_0.5 mean_pos cos_q10 cos_q50 logratio_q50")
    for t_min, t_max in windows:
        for sigma in sigmas:
            for kind in ("true-zeta", "finite-euler"):
                row = summarize(kind, sigma, t_min, t_max, args.samples, primes)
                print(
                    f"{row['kind']:12s} {row['sigma']:.1f} {row['window']:9s}"
                    f" {row['q50']:.6g} {row['q90']:.6g} {row['q99']:.6g}"
                    f" {row['frac_pos']:.6g} {row['frac_big']:.6g} {row['mean_pos']:.6g}"
                    f" {row['cos_q10']:.6g} {row['cos_q50']:.6g} {row['logratio_q50']:.6g}"
                )


if __name__ == "__main__":
    main()
