#!/usr/bin/env python3
"""Step 12 battery for the hypercycle-specificity finding.

Finding under test:
    phase-specific catalyst selects true zeta'/zeta;
    amplitude-promiscuous catalyst selects finite Euler parasites.
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


def gamma_part(s):
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def dlog_zeta(s, h=1e-4):
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite_euler(s, primes):
    out = 0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def dlog_sine(s):
    return complex(math.pi / mp.fp.tan(math.pi * s))


def defect_and_cos(g, p):
    delta = math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)
    cos = float("nan") if abs(g) * abs(p) == 0 else float((g * p.conjugate()).real / (abs(g) * abs(p)))
    return delta, cos


def scores(kind, sigma, window, samples, prime_count, rng, h=1e-4):
    primes = first_primes(prime_count)
    phase = []
    amp = []
    cos_specific = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true":
            p = dlog_zeta(s, h)
        elif kind == "finite":
            p = dlog_finite_euler(s, primes)
        elif kind == "random-phase":
            base = dlog_zeta(s, h)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(base) * complex(math.cos(theta), math.sin(theta))
        elif kind == "sine":
            p = dlog_sine(s)
        else:
            raise ValueError(kind)
        d, c = defect_and_cos(g, p)
        phase.append(max(0.0, d))
        amp.append(math.log1p(max(abs(g), abs(p))))
        cos_specific.append(max(0.0, -c) if not math.isnan(c) else 0.0)
    return float(np.median(phase)), float(np.median(amp)), float(np.median(cos_specific))


def norm(vals):
    arr = np.array(vals, dtype=float)
    if float(arr.max() - arr.min()) < 1e-12:
        return np.ones_like(arr) / len(arr)
    return (arr - arr.min()) / (arr.max() - arr.min())


def winner(vals, labels):
    vals = np.array(vals)
    return labels[int(np.argmax(vals))]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=180)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    rng = np.random.default_rng(20260621)
    labels = ["true", "finite", "random-phase"]
    windows = [(14.0, 84.0), (100.0, 170.0), (500.0, 570.0), (1000.0, 1070.0)]
    sigmas = [0.2, 0.3, 0.5, 0.7, 0.8, 1.2]
    cache = {}
    for sig in sigmas:
        for w in windows:
            for lab in labels:
                cache[(lab, sig, w)] = scores(lab, sig, w, args.samples, args.prime_count, rng)

    print("STEP12 hypercycle specificity battery")
    print(f"samples={args.samples} finite_prime_count={args.prime_count}")
    print("score tuple = phase_specific, amplitude_promiscuous, cos_specific")

    print("\n01 split")
    for sig in [0.3, 0.5, 0.7]:
        w = (100.0, 170.0)
        phase = [cache[(lab, sig, w)][0] for lab in labels]
        amp = [cache[(lab, sig, w)][1] for lab in labels]
        print(f"sigma={sig}: phase={dict(zip(labels, np.round(phase,4)))} amp={dict(zip(labels, np.round(amp,4)))}")

    print("\n02 attack false")
    for sig in [0.3, 0.5]:
        w = (100.0, 170.0)
        print(f"sigma={sig}: true_phase={cache[('true',sig,w)][0]:.4g} random_phase={cache[('random-phase',sig,w)][0]:.4g}")

    print("\n03 reverse")
    for sig in [0.3, 0.5, 0.7]:
        w = (100.0, 170.0)
        phase_w = winner([cache[(lab, sig, w)][0] for lab in labels], labels)
        amp_w = winner([cache[(lab, sig, w)][1] for lab in labels], labels)
        print(f"sigma={sig}: phase_winner={phase_w} amplitude_winner={amp_w}")

    print("\n04 change viewpoint")
    print("viewpoint: specificity is a selector on relative phase/cosine; promiscuity is a selector on scalar magnitude.")

    print("\n05 make visual")
    for sig in sigmas:
        chars = []
        for w in windows:
            phase_w = winner([cache[(lab, sig, w)][0] for lab in labels], labels)
            amp_w = winner([cache[(lab, sig, w)][1] for lab in labels], labels)
            chars.append(("T" if phase_w == "true" else "x") + (("F" if amp_w == "finite" else "x")))
        print(f"sigma={sig}: {' '.join(chars)}  (T=phase true, F=amp finite)")

    print("\n06 action")
    print("action=filtering: a specific catalyst filters by phase carrier; a promiscuous catalyst amplifies high magnitude even when nonreciprocal.")

    print("\n07 strip")
    w = (100.0, 170.0)
    for sig in [0.3, 0.5, 0.7, 1.2]:
        phase_gap = cache[("true", sig, w)][0] - max(cache[("finite", sig, w)][0], cache[("random-phase", sig, w)][0])
        amp_gap = cache[("finite", sig, w)][1] - cache[("true", sig, w)][1]
        print(f"sigma={sig}: phase_gap_true_over_parasites={phase_gap:.4g} amp_gap_finite_over_true={amp_gap:.4g}")

    print("\n08 similar objects")
    for sig in [0.3, 0.5]:
        print(f"sine sigma={sig}: phase,amp,cos={scores('sine', sig, (100.0,170.0), args.samples, args.prime_count, rng)}")

    print("\n09 small cases")
    for w in [(5.0, 25.0), (14.0, 30.0)]:
        phase = [scores(lab, 0.3, w, args.samples, args.prime_count, rng)[0] for lab in labels]
        amp = [scores(lab, 0.3, w, args.samples, args.prime_count, rng)[1] for lab in labels]
        print(f"window={w}: phase_winner={winner(phase,labels)} amp_winner={winner(amp,labels)} phase={np.round(phase,4).tolist()} amp={np.round(amp,4).tolist()}")

    print("\n10 extreme")
    for sig in [0.1, 1.2, 1.5]:
        vals = {lab: scores(lab, sig, (100.0,170.0), args.samples, args.prime_count, rng) for lab in labels}
        print(f"sigma={sig}: {vals}")

    print("\n11 experiments")
    success = []
    for sig in sigmas:
        for w in windows:
            phase_w = winner([cache[(lab, sig, w)][0] for lab in labels], labels)
            amp_w = winner([cache[(lab, sig, w)][1] for lab in labels], labels)
            success.append((sig, w, phase_w == "true", amp_w == "finite"))
    print(f"phase_true count={sum(x[2] for x in success)}/{len(success)} amp_finite count={sum(x[3] for x in success)}/{len(success)}")

    print("\n12 invariant")
    print("invariant under windows at sigma=0.3: phase winner true and amplitude winner finite")
    for w in windows:
        print(f"window={w}: phase={winner([cache[(lab,0.3,w)][0] for lab in labels],labels)} amp={winner([cache[(lab,0.3,w)][1] for lab in labels],labels)}")

    print("\n13 monotone")
    for pc in [10, 30, 80, 160, 240]:
        vals = {lab: scores(lab, 0.3, (100.0,170.0), args.samples, pc, rng)[:2] for lab in ["true","finite"]}
        print(f"prime_count={pc}: {vals}")

    print("\n14 weaken")
    print("weakened claim: phase-specific selector chooses true on the left strip; amplitude selector chooses finite Euler. No universal sigma claim.")

    print("\n15 strengthen")
    passed = 0
    tested = 0
    for w in windows:
        ph = [cache[(lab,0.3,w)][0] for lab in labels]
        am = [cache[(lab,0.3,w)][1] for lab in labels]
        passed += int(winner(ph,labels) == "true" and winner(am,labels) == "finite" and ph[0] > 0.2)
        tested += 1
    print(f"sigma=0.3 strengthened screen passed {passed}/{tested}")

    print("\n16 minimal counterexample")
    bad = []
    for sig, w, phase_ok, amp_ok in success:
        if not (phase_ok and amp_ok):
            bad.append((sig, w, phase_ok, amp_ok))
    print(f"counterexamples to strong universal claim: {bad[:10]} total={len(bad)}")

    print("\n17 change representation")
    for sig in [0.3, 0.5]:
        w = (100.0,170.0)
        cos_w = winner([cache[(lab,sig,w)][2] for lab in labels], labels)
        print(f"sigma={sig}: cos_specific_winner={cos_w} scores={[round(cache[(lab,sig,w)][2],4) for lab in labels]}")

    print("\n18 theorem resemblance")
    print("resembles specificity in cooperative systems and the project phase-cancellation split: pair-specific phase is load-bearing, magnitude is promiscuous.")

    print("\n19 fake proof gap")
    print("fake proof gap: need an analytic phase-distribution theorem proving true zeta's phase-specific score exceeds finite/random controls on the left strip.")

    print("\n20 missing lemma")
    print("missing lemma: median positive phase defect for true zeta is bounded below while finite Euler's median positive defect stays near zero as prime cutoff grows.")

    print("\n21 dependency")
    for h in [1e-3, 1e-4, 1e-5]:
        vals = {}
        for lab in ["true", "finite"]:
            # Only h affects true; finite is repeated for comparable output.
            vals[lab] = scores(lab, 0.3, (100.0,170.0), args.samples, args.prime_count, rng, h=h)[:2]
        print(f"h={h:g}: {vals}")

    print("\n22 nearby false statements")
    print("false: phase selector is meaningful everywhere. At sigma=0.7/1.2 normalization can name a winner even when absolute phase scores are tiny.")

    print("\n23 boundary")
    for sig in sigmas:
        w = (100.0,170.0)
        phase = [cache[(lab,sig,w)][0] for lab in labels]
        amp = [cache[(lab,sig,w)][1] for lab in labels]
        print(f"sigma={sig}: phase={np.round(phase,4).tolist()} amp={np.round(amp,4).tolist()}")


if __name__ == "__main__":
    main()
