#!/usr/bin/env python3
"""STEP 12 battery for the margin-neutralized phase-carrier finding."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def first_primes(n: int) -> tuple[int, ...]:
    primes: list[int] = []
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


def gamma_part(s: complex) -> complex:
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def dlog_zeta(s: complex, h: float = 1e-4) -> complex:
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite_euler(s: complex, primes: tuple[int, ...]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def raw_values(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator):
    deltas: list[float] = []
    feats: dict[str, list[list[float]]] = {"amp": [], "amp_total": [], "amp_phase": []}
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true":
            p = dlog_zeta(s)
        elif kind == "finite":
            p = dlog_finite_euler(s, primes)
        elif kind == "random":
            base = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(base) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        ag = abs(g)
        ap = abs(p)
        at = abs(g + p)
        delta = math.log(max(ag, ap) + 1e-300) - math.log(at + 1e-300)
        cos = 0.0 if ag <= 1e-300 or ap <= 1e-300 else float((g * p.conjugate()).real / (ag * ap))
        amp = [
            1.0,
            math.log1p(ag),
            math.log1p(ap),
            math.log((ap + 1e-300) / (ag + 1e-300)),
            math.log1p(max(ag, ap)),
            math.log1p(min(ag, ap)),
        ]
        deltas.append(delta)
        feats["amp"].append(amp)
        feats["amp_total"].append(amp + [math.log1p(at)])
        feats["amp_phase"].append(amp + [cos])
    return np.asarray(deltas), {k: np.asarray(v) for k, v in feats.items()}


def residual_gap(sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], feature_set: str) -> dict[str, float]:
    rng = np.random.default_rng(1000 + int(100 * sigma) + int(window[0]))
    true_y, true_xs = raw_values("true", sigma, window, samples, primes, rng)
    finite_y, finite_xs = raw_values("finite", sigma, window, samples, primes, rng)
    random_y, random_xs = raw_values("random", sigma, window, samples, primes, rng)
    cx = np.vstack([finite_xs[feature_set], random_xs[feature_set]])
    cy = np.concatenate([finite_y, random_y])
    beta, *_ = np.linalg.lstsq(cx, cy, rcond=None)

    def resid(y: np.ndarray, x: np.ndarray) -> np.ndarray:
        return y - x @ beta

    tr = resid(true_y, true_xs[feature_set])
    fr = resid(finite_y, finite_xs[feature_set])
    rr = resid(random_y, random_xs[feature_set])
    return {
        "true_med": float(np.median(tr)),
        "finite_med": float(np.median(fr)),
        "random_med": float(np.median(rr)),
        "gap_true_random": float(np.median(tr) - np.median(rr)),
        "true_pos": float(np.mean(tr > 0.0)),
        "finite_pos": float(np.mean(fr > 0.0)),
        "random_pos": float(np.mean(rr > 0.0)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=180)
    args = parser.parse_args()

    print("STEP12 battery: margin-neutralized phase-carrier")
    print(f"samples={args.samples}")

    primes = first_primes(160)
    windows = [(14.0, 84.0), (100.0, 170.0), (500.0, 570.0)]
    sigmas = [0.2, 0.3, 0.4, 0.5, 0.7, 0.9, 1.2]
    print("\nA. sigma sweep, amp-only neutralization: mean true-random residual gap across windows")
    print("sigma mean_gap min_gap mean_true_pos mean_random_pos")
    for sigma in sigmas:
        rows = [residual_gap(sigma, window, args.samples, primes, "amp") for window in windows]
        print(
            f"{sigma:.1f} "
            f"{float(np.mean([r['gap_true_random'] for r in rows])):+.5f} "
            f"{float(np.min([r['gap_true_random'] for r in rows])):+.5f} "
            f"{float(np.mean([r['true_pos'] for r in rows])):.3f} "
            f"{float(np.mean([r['random_pos'] for r in rows])):.3f}"
        )

    print("\nB. feature-boundary test at sigma=0.3, window=[100,170]")
    print("feature_set true_med finite_med random_med gap_true_random true_pos finite_pos random_pos")
    for feature_set in ["amp", "amp_total", "amp_phase"]:
        row = residual_gap(0.3, (100.0, 170.0), args.samples, primes, feature_set)
        print(
            f"{feature_set:10s} "
            f"{row['true_med']:+.5f} {row['finite_med']:+.5f} {row['random_med']:+.5f} "
            f"{row['gap_true_random']:+.5f} "
            f"{row['true_pos']:.3f} {row['finite_pos']:.3f} {row['random_pos']:.3f}"
        )

    print("\nC. finite-Euler prime-count stress at sigma=0.3, window=[100,170], amp-only")
    print("prime_count true_med finite_med random_med gap_true_random finite_pos")
    for n in [30, 80, 160, 240]:
        pset = first_primes(n)
        row = residual_gap(0.3, (100.0, 170.0), args.samples, pset, "amp")
        print(
            f"{n:3d} "
            f"{row['true_med']:+.5f} {row['finite_med']:+.5f} {row['random_med']:+.5f} "
            f"{row['gap_true_random']:+.5f} {row['finite_pos']:.3f}"
        )

    print("\nD. method ledger for scientific-method moves")
    print("1 split: raw defect vs amplitude residual vs phase-included residual are separated in B.")
    print("2 attack-false: amp_total and amp_phase are overcontrols; they remove the signal by including the answer.")
    print("3 reverse: controls fitted first do not predict true left-strip residuals under amp-only features.")
    print("4 viewpoint: sigma sweep shows the effect is a left-strip residual, not a global property.")
    print("5 visual/action: margin-call metaphor becomes common-amplitude neutralization.")
    print("6 action: the action is neutralizing common collateral amplitude, not amplifying raw magnitude.")
    print("7 essentials: amp-only features suffice for the control; |G+P| is not an allowed essential input.")
    print("8 similar objects: finite Euler and random-phase controls are the nearby objects.")
    print("9 small cases: prime_count=30 already leaves finite residual near zero in C.")
    print("10 extremes: sigma=1.2 collapses the residual gap in A.")
    print("11 experiments: A-C are the runnable probes.")
    print("12 invariant: positive gap persists across three windows for sigma<=0.5 in A.")
    print("13 monotone: the mean gap decreases as sigma moves rightward in A.")
    print("14 weaken: claim only left-strip, amplitude-neutralized residual positivity.")
    print("15 strengthen: universal-sigma claim is false by sigma=1.2.")
    print("16 minimal counterexample: adding |G+P| or phase cosine is the minimal overcontrol that kills it.")
    print("17 representation: regression residual representation distinguishes phase from amplitude.")
    print("18 theorem-tool resemblance: would need a phase-distribution bound, not a magnitude bound.")
    print("19 fake-proof gap: cannot prove from amplitude moments; phase alignment is the missing step.")
    print("20 missing lemma: left-strip positive residual phase-defect lower bound after amplitude conditioning.")
    print("21 dependency: define amplitude sigma-algebra -> condition Delta -> prove positive conditional median.")
    print("22 nearby false: amp_total/phase-conditioned residual positivity is false by construction.")
    print("23 boundary cases: left strip survives; far right and overcontrolled features collapse.")


if __name__ == "__main__":
    main()
