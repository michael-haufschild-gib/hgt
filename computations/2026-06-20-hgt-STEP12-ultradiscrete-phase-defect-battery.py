#!/usr/bin/env python3
"""Step 12 battery for the ultradiscrete sign-carrier finding.

Finding under test:
    Delta = max(log|Gamma_infty|, log|P|) - log|Gamma_infty + P|
separates true analytic zeta'/zeta from finite Euler controls in prior runs.

This script maps the 23 scientific-method moves to concrete follow-up tests.
It is intentionally compact enough to run in minutes on the Runpod host.
"""

import argparse
import math
from collections import defaultdict

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


def dlog_zeta(s, h):
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite_euler(s, primes):
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def dlog_sine(s):
    return complex(math.pi / mp.fp.tan(math.pi * s))


def defect(g, p):
    ag = abs(g)
    ap = abs(p)
    total = abs(g + p)
    delta = math.log(max(ag, ap) + 1e-300) - math.log(total + 1e-300)
    if ag == 0.0 or ap == 0.0:
        cos = float("nan")
    else:
        cos = ((g * p.conjugate()).real / (ag * ap))
    ratio = math.log((ap + 1e-300) / (ag + 1e-300))
    return delta, cos, ratio


def sample(kind, sigma, window, samples, h, prime_count, rng=None, random_phase=False):
    t0, t1 = window
    ts = np.linspace(t0, t1, samples)
    primes = first_primes(prime_count)
    deltas, cosines, ratios = [], [], []
    for t in ts:
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true":
            p = dlog_zeta(s, h)
        elif kind == "finite":
            p = dlog_finite_euler(s, primes)
        elif kind == "sine":
            p = dlog_sine(s)
        else:
            raise ValueError(kind)
        if random_phase:
            phase = rng.uniform(-math.pi, math.pi)
            p = abs(p) * complex(math.cos(phase), math.sin(phase))
        d, c, r = defect(g, p)
        deltas.append(d)
        cosines.append(c)
        ratios.append(r)
    return np.array(deltas), np.array(cosines), np.array(ratios)


def metrics(vals):
    arr = np.array(vals)
    return {
        "med": float(np.quantile(arr, 0.50)),
        "q90": float(np.quantile(arr, 0.90)),
        "q99": float(np.quantile(arr, 0.99)),
        "pos": float(np.mean(arr > 0.0)),
        "big": float(np.mean(arr > 0.5)),
    }


def fmt_metric(m):
    return f"med={m['med']:.4g} q90={m['q90']:.4g} q99={m['q99']:.4g} pos={m['pos']:.3f} big={m['big']:.3f}"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=180)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()

    windows = [(14.0, 84.0), (100.0, 170.0), (500.0, 570.0), (1000.0, 1070.0)]
    sigmas = [0.2, 0.3, 0.5, 0.7, 0.8, 1.2]
    h = 1e-4
    rng = np.random.default_rng(20260620)

    cache = {}
    for w in windows:
        for sig in sigmas:
            for kind in ("true", "finite"):
                cache[(kind, sig, w)] = sample(kind, sig, w, args.samples, h, args.prime_count)
    print("STEP12 ultradiscrete phase-defect battery")
    print(f"samples={args.samples} finite_prime_count={args.prime_count} h={h}")

    print("\n01 split subclaims")
    for sig in (0.3, 0.5, 0.7):
        true_meds = [metrics(cache[("true", sig, w)][0])["med"] for w in windows[:3]]
        fin_meds = [metrics(cache[("finite", sig, w)][0])["med"] for w in windows[:3]]
        print(f"subclaim sigma={sig}: true_medians={np.round(true_meds,4).tolist()} finite_medians={np.round(fin_meds,4).tolist()}")

    print("\n02 attack as false")
    for sig in (0.3, 0.5):
        for w in windows[:3]:
            td = cache[("true", sig, w)][0]
            rd, _, _ = sample("true", sig, w, args.samples, h, args.prime_count, rng=rng, random_phase=True)
            print(f"random-phase true sigma={sig} window={w}: observed {fmt_metric(metrics(td))} surrogate {fmt_metric(metrics(rd))}")

    print("\n03 reverse")
    for sig in (0.3, 0.5):
        for w in windows[:2]:
            td, tc, tr = cache[("true", sig, w)]
            print(f"from high Delta infer antiphase sigma={sig} window={w}: cos_q10={np.nanquantile(tc,0.1):.4g} cos_med={np.nanmedian(tc):.4g} ratio_med={np.median(tr):.4g}")

    print("\n04 change viewpoint")
    print("two-vector identity: Delta is determined by amplitude ratio r=log|P/G| and cos(theta); no scalar max-plus carrier can see cos(theta).")

    print("\n05 make visual")
    for sig, w in [(0.3, windows[1]), (0.5, windows[1])]:
        td = cache[("true", sig, w)][0]
        spark = "".join("█" if x > 1.0 else "▓" if x > 0.5 else "▒" if x > 0 else "." for x in td[:: max(1, len(td)//60)])
        print(f"true sigma={sig} window={w} defect sparkline {spark}")

    print("\n06 action")
    print("action=cancellation/joining of two complex vectors; defect counts how much scalar max-plus overpredicts after destructive joining.")

    print("\n07 strip to essentials")
    for sig in (0.3, 0.5, 0.7):
        t_m = metrics(cache[("true", sig, windows[1])][0])
        f_m = metrics(cache[("finite", sig, windows[1])][0])
        print(f"essential statistic sigma={sig} window={windows[1]} median-gap={t_m['med']-f_m['med']:.4g} big-gap={t_m['big']-f_m['big']:.4g}")

    print("\n08 similar objects")
    for sig in (0.3, 0.5):
        sd, _, _ = sample("sine", sig, windows[1], args.samples, h, args.prime_count)
        print(f"sine control sigma={sig} window={windows[1]} {fmt_metric(metrics(sd))}")

    print("\n09 small cases")
    for w in [(5.0, 25.0), (14.0, 30.0)]:
        td, _, _ = sample("true", 0.3, w, args.samples, h, args.prime_count)
        fd, _, _ = sample("finite", 0.3, w, args.samples, h, args.prime_count)
        print(f"small window={w}: true {fmt_metric(metrics(td))}; finite {fmt_metric(metrics(fd))}")

    print("\n10 extreme cases")
    for sig in (0.1, 1.2):
        td, _, _ = sample("true", sig, windows[1], args.samples, h, args.prime_count)
        fd, _, _ = sample("finite", sig, windows[1], args.samples, h, args.prime_count)
        print(f"extreme sigma={sig}: true {fmt_metric(metrics(td))}; finite {fmt_metric(metrics(fd))}")

    print("\n11 experiments")
    best = []
    for sig in sigmas:
        for w in windows:
            tm = metrics(cache[("true", sig, w)][0])
            fm = metrics(cache[("finite", sig, w)][0])
            best.append((tm["med"] - fm["med"], sig, w, tm, fm))
    for gap, sig, w, tm, fm in sorted(best, reverse=True)[:6]:
        print(f"top median separation gap={gap:.4g} sigma={sig} window={w}: true {fmt_metric(tm)} finite {fmt_metric(fm)}")

    print("\n12 invariant")
    for w in windows[:3]:
        left = metrics(cache[("true", 0.3, w)][0])["med"]
        right = metrics(cache[("true", 0.7, w)][0])["med"]
        print(f"true mirror median difference window={w}: sigma0.3-sigma0.7={left-right:.4g}")

    print("\n13 monotone")
    for pc in (10, 30, 80, 160, 240):
        fd, _, _ = sample("finite", 0.3, windows[1], args.samples, h, pc)
        print(f"finite prime_count={pc}: {fmt_metric(metrics(fd))}")

    print("\n14 weaken")
    print("weakened claim: on sigma=0.3, median Delta_true > median Delta_finite over several windows; no claim of universal separation.")

    print("\n15 strengthen")
    passed = 0
    for w in windows[:3]:
        tm = metrics(cache[("true", 0.3, w)][0])
        fm = metrics(cache[("finite", 0.3, w)][0])
        passed += int(tm["med"] > 0.25 and abs(fm["med"]) < 0.08)
    print(f"strengthened prereg screen sigma=0.3: passed {passed}/3 windows (true_med>0.25 and |finite_med|<0.08)")

    print("\n16 minimal counterexample")
    failures = []
    for sig in sigmas:
        for w in windows:
            tm = metrics(cache[("true", sig, w)][0])
            fm = metrics(cache[("finite", sig, w)][0])
            if tm["med"] <= fm["med"]:
                failures.append((sig, w, tm["med"], fm["med"]))
    print(f"separation failures (true_median<=finite_median): {failures[:8]} total={len(failures)}")

    print("\n17 change representation")
    for sig in (0.3, 0.5):
        td, tc, tr = cache[("true", sig, windows[1])]
        high = td > np.quantile(td, 0.9)
        print(f"high-defect representation sigma={sig}: mean_cos_high={np.nanmean(tc[high]):.4g} mean_ratio_high={np.mean(tr[high]):.4g}")

    print("\n18 right theorem resemblance")
    print("resembles signed tropicalization plus phase-cancellation-crux: affine magnitudes are harmless; the missing carrier is the relative phase/cosine.")

    print("\n19 fake proof gap")
    print("fake proof would say analytic continuation forces antiphase while finite Euler cannot; gap: need theorem on phase distribution of zeta'/zeta relative to digamma, not just samples.")

    print("\n20 missing lemma")
    print("missing lemma: in left critical strip windows, median cos(arg Gamma_part - arg zeta_part) stays negative enough that scalar max-plus has positive median defect.")

    print("\n21 dependency chain")
    for hh in (1e-3, 1e-4, 1e-5):
        td, _, _ = sample("true", 0.3, windows[1], args.samples, hh, args.prime_count)
        print(f"h-stability h={hh:g}: {fmt_metric(metrics(td))}")

    print("\n22 nearby false statements")
    print("false: finite Euler never has large tails. Counterexample from prior P80 and this run: finite at sigma=0.7 can have q90/q99 comparable to true; use medians on sigma=0.3, not universal tails.")

    print("\n23 boundary cases")
    for sig in (0.2, 0.3, 0.5, 0.7, 0.8, 1.2):
        tm = metrics(cache[("true", sig, windows[1])][0])
        fm = metrics(cache[("finite", sig, windows[1])][0])
        print(f"boundary sigma={sig}: true_med={tm['med']:.4g} finite_med={fm['med']:.4g} gap={tm['med']-fm['med']:.4g}")


if __name__ == "__main__":
    main()
