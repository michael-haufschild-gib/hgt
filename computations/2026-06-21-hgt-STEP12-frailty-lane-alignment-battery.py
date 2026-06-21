#!/usr/bin/env python3
"""Step 12 battery for coupled low-reserve lane-alignment candidate.

Candidate:
    In left-strip sigma lanes, true zeta'/zeta has visible multi-lane
    low-phase-reserve events in temporal excess over shuffled lane timings.
    Finite Euler and random-phase controls mostly do not. This would mean the
    "frailty" event is not just low reserve in separate lanes, but aligned
    cross-lane failure of phase reserve.

The battery maps the 23 scientific-method moves to compact tests. It is
designed to finish in minutes on the Runpod host.
"""

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


def dlog_gamma_only(_: complex) -> complex:
    return 0.0 + 0.0j


def phase_defect(g: complex, p: complex) -> float:
    return max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))


def zero_shadow(g: complex, p: complex) -> float:
    return max(0.0, 1.0 - abs(g + p) / (max(abs(g), abs(p)) + 1e-300))


def lane_matrix(kind: str, sigmas: list[float], window: tuple[float, float], samples: int, primes: tuple[int, ...], seed: int, mode: str = "phase") -> np.ndarray:
    rng = np.random.default_rng(seed)
    mat = []
    for sigma in sigmas:
        row = []
        for t in np.linspace(window[0], window[1], samples):
            s = complex(float(sigma), float(t))
            g = gamma_part(s)
            true_p = dlog_zeta(s)
            finite_p = dlog_finite_euler(s, primes)
            if kind == "true":
                p = true_p
            elif kind == "finite":
                p = finite_p
            elif kind == "ampmatched-finite":
                p = finite_p * (abs(true_p) / (abs(finite_p) + 1e-300))
            elif kind == "random-phase":
                theta = float(rng.uniform(-math.pi, math.pi))
                p = abs(true_p) * complex(math.cos(theta), math.sin(theta))
            elif kind == "gamma-only":
                p = dlog_gamma_only(s)
            else:
                raise ValueError(kind)
            if mode == "phase":
                d = phase_defect(g, p)
                row.append(d / (1.0 + d))
            elif mode == "zero":
                row.append(zero_shadow(g, p))
            else:
                raise ValueError(mode)
        mat.append(row)
    return np.asarray(mat)


def visible_from_low(low: np.ndarray) -> np.ndarray:
    neighbor_low = (np.roll(low, 1, axis=0).astype(float) + np.roll(low, -1, axis=0).astype(float)) / 2.0
    coupled_low = low & (neighbor_low >= 0.5)
    return np.sum(coupled_low, axis=0) >= 3


def metric(reserve: np.ndarray, threshold: float, seed: int, trials: int = 48) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    low = reserve < threshold
    visible = visible_from_low(low)
    visible_frac = float(np.mean(visible))
    indep = []
    shifts = []
    for _ in range(trials):
        shuf = low.copy()
        shift = low.copy()
        for i in range(low.shape[0]):
            rng.shuffle(shuf[i])
            shift[i] = np.roll(shift[i], int(rng.integers(0, low.shape[1])))
        indep.append(float(np.mean(visible_from_low(shuf))))
        shifts.append(float(np.mean(visible_from_low(shift))))
    lane_low = np.mean(low, axis=1)
    if np.any(visible):
        cover = max(float(np.mean(low[i, visible])) for i in range(low.shape[0]))
        mean_lows_given = float(np.mean(np.sum(low[:, visible], axis=0)))
    else:
        cover = 0.0
        mean_lows_given = 0.0
    return {
        "visible": visible_frac,
        "indep": float(np.mean(indep)),
        "shift": float(np.mean(shifts)),
        "excess_indep": visible_frac - float(np.mean(indep)),
        "excess_shift": visible_frac - float(np.mean(shifts)),
        "weakest": float(np.max(lane_low)),
        "cover": cover,
        "mean_lows_given_visible": mean_lows_given,
        "mean_reserve": float(np.mean(reserve)),
    }


def fmt(m: dict[str, float]) -> str:
    return (
        f"vis={m['visible']:.3f} indep={m['indep']:.3f} shift={m['shift']:.3f} "
        f"exI={m['excess_indep']:.3f} exS={m['excess_shift']:.3f} "
        f"weak={m['weakest']:.3f} cover={m['cover']:.3f}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=140)
    parser.add_argument("--prime-count", type=int, default=100)
    args = parser.parse_args()

    primes = first_primes(args.prime_count)
    boundaries = {
        "left": [0.2, 0.3, 0.4, 0.5, 0.7],
        "middle": [0.5, 0.7, 0.8, 0.9, 1.0],
        "right": [0.9, 1.0, 1.1, 1.2, 1.3],
        "left_no_weakest": [0.2, 0.4, 0.5, 0.7],
    }
    windows = [(100.0, 170.0), (500.0, 570.0), (900.0, 970.0)]
    kinds = ["true", "finite", "ampmatched-finite", "random-phase", "gamma-only"]
    thresholds = [0.08, 0.12, 0.16, 0.20, 0.28]

    cache: dict[tuple[str, str, tuple[float, float], str], np.ndarray] = {}
    for mode in ["phase", "zero"]:
        for b_name, sigmas in boundaries.items():
            for w_i, window in enumerate(windows):
                for k_i, kind in enumerate(kinds):
                    cache[(mode, b_name, window, kind)] = lane_matrix(kind, sigmas, window, args.samples, primes, seed=20260621 + 1009 * w_i + 37 * k_i, mode=mode)

    print("STEP12 coupled low-reserve lane-alignment battery")
    print(f"samples={args.samples} prime_count={args.prime_count}")

    print("\n01 split subclaims")
    for window in windows[:2]:
        for thr in [0.12, 0.20]:
            vals = {kind: metric(cache[("phase", "left", window, kind)], thr, 1100 + int(thr * 1000) + len(kind)) for kind in kinds[:4]}
            print(f"left window={window} threshold={thr}: " + " | ".join(f"{k} {fmt(v)}" for k, v in vals.items()))

    print("\n02 attack as false")
    print("Controls tested: finite Euler, amplitude-matched finite, random phase, gamma-only, independent shuffle, circular lane shifts.")

    print("\n03 reverse")
    for window in windows[:2]:
        m = metric(cache[("phase", "left", window, "true")], 0.20, 1200)
        print(f"condition on visible true-left failure window={window}: mean_lows_given={m['mean_lows_given_visible']:.3f} weakest_cover={m['cover']:.3f} excess_indep={m['excess_indep']:.3f}")

    print("\n04 change viewpoint")
    for boundary in ["left", "middle", "right"]:
        m = metric(cache[("phase", boundary, windows[0], "true")], 0.20, 1300)
        print(f"view as boundary={boundary}: true {fmt(m)}")

    print("\n05 visual")
    reserve = cache[("phase", "left", windows[0], "true")]
    low = reserve < 0.20
    visible = visible_from_low(low)
    spark = "".join("█" if v else "." for v in visible[:: max(1, len(visible) // 70)])
    print(f"true left visible-failure sparkline threshold=0.20 window={windows[0]} {spark}")

    print("\n06 action")
    print("Action is cross-sigma co-failure: phase reserve drops in several adjacent lanes at the same height, not just low reserve in one lane.")

    print("\n07 strip essentials")
    for boundary in ["left", "left_no_weakest"]:
        m = metric(cache[("phase", boundary, windows[0], "true")], 0.20, 1400)
        print(f"true {boundary} {fmt(m)}")

    print("\n08 similar objects")
    for kind in ["finite", "ampmatched-finite", "random-phase", "gamma-only"]:
        m = metric(cache[("phase", "left", windows[0], kind)], 0.20, 1500 + len(kind))
        print(f"{kind} left {fmt(m)}")

    print("\n09 small cases")
    small_sigmas = {"small_left": [0.2, 0.3, 0.4], "pair_left": [0.2, 0.3]}
    for name, sigmas in small_sigmas.items():
        reserve = lane_matrix("true", sigmas, windows[0], args.samples, primes, seed=4444, mode="phase")
        m = metric(reserve, 0.20, 1600)
        print(f"{name} true lanes={len(sigmas)} {fmt(m)}")

    print("\n10 extreme cases")
    for thr in [0.04, 0.36]:
        m = metric(cache[("phase", "left", windows[0], "true")], thr, 1700)
        print(f"true left extreme threshold={thr}: {fmt(m)}")

    print("\n11 experiments")
    best = []
    for window in windows:
        for boundary in ["left", "middle", "right"]:
            for thr in thresholds:
                mt = metric(cache[("phase", boundary, window, "true")], thr, 1800 + int(thr * 1000))
                mf = metric(cache[("phase", boundary, window, "finite")], thr, 1810 + int(thr * 1000))
                best.append((mt["excess_indep"] - mf["excess_indep"], boundary, window, thr, mt, mf))
    for gap, boundary, window, thr, mt, mf in sorted(best, reverse=True)[:8]:
        print(f"gap={gap:.3f} boundary={boundary} window={window} thr={thr}: true {fmt(mt)} finite {fmt(mf)}")

    print("\n12 invariant")
    for window in windows:
        vals = [metric(cache[("phase", "left", window, "true")], thr, 1900 + int(thr * 1000))["excess_indep"] for thr in [0.12, 0.16, 0.20]]
        print(f"true left excess_indep window={window} thresholds=.12,.16,.20 -> {','.join(f'{v:.3f}' for v in vals)}")

    print("\n13 monotone")
    for kind in ["true", "finite", "random-phase"]:
        vals = [metric(cache[("phase", "left", windows[0], kind)], thr, 2000 + int(thr * 1000) + len(kind))["visible"] for thr in thresholds]
        print(f"{kind} visible monotone in threshold: {','.join(f'{v:.3f}' for v in vals)}")

    print("\n14 weaken")
    print("Weakened claim: true left has positive excess over independent lane shuffling at thresholds .12-.20; no claim for right strip or all thresholds.")

    print("\n15 strengthen")
    passes = 0
    for window in windows[:2]:
        mt = metric(cache[("phase", "left", window, "true")], 0.20, 2100)
        mf = metric(cache[("phase", "left", window, "finite")], 0.20, 2110)
        mr = metric(cache[("phase", "left", window, "random-phase")], 0.20, 2120)
        passes += int(mt["excess_indep"] > 0.15 and mf["excess_indep"] < 0.02 and mr["excess_indep"] < 0.02)
    print(f"strengthened screen windows_passed={passes}/2 for true_excess>.15 and finite/random<.02")

    print("\n16 minimal counterexample")
    mt = metric(cache[("phase", "left_no_weakest", windows[0], "true")], 0.20, 2200)
    print(f"remove sigma=.3 lane: {fmt(mt)}")

    print("\n17 representation")
    for mode in ["phase", "zero"]:
        m = metric(cache[(mode, "left", windows[0], "true")], 0.20, 2300)
        print(f"representation={mode}: true left {fmt(m)}")

    print("\n18 right theorem")
    print("Right theorem would be a lane-dependence theorem: visible multi-lane low-reserve exceeds the product/shuffle null in the left strip but collapses to finite Euler on the right.")

    print("\n19 fake proof")
    print("Fake proof gap: weakest lane alone covers visible events, but its low fraction does not determine visible fraction; shuffle null is needed to test cross-lane timing.")

    print("\n20 missing lemma")
    print("Missing lemma: prove that excess over the independent lane-shuffle null is not forced by one-lane marginal failure probabilities.")

    print("\n21 dependency chain")
    print("phase defect reserve -> lane low-reserve masks -> adjacent co-failure -> excess over shuffled lane timing -> boundary/control gap.")

    print("\n22 nearby false statements")
    for boundary in ["middle", "right"]:
        mt = metric(cache[("phase", boundary, windows[0], "true")], 0.20, 2400)
        mf = metric(cache[("phase", boundary, windows[0], "finite")], 0.20, 2410)
        print(f"false universal boundary={boundary}: true {fmt(mt)} finite {fmt(mf)}")

    print("\n23 boundary cases")
    for boundary in ["left", "middle", "right"]:
        for window in windows:
            mt = metric(cache[("phase", boundary, window, "true")], 0.20, 2500)
            mf = metric(cache[("phase", boundary, window, "finite")], 0.20, 2510)
            print(f"boundary={boundary} window={window}: true_excess={mt['excess_indep']:.3f} finite_excess={mf['excess_indep']:.3f}")


if __name__ == "__main__":
    main()
