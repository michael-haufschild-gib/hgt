#!/usr/bin/env python3
"""STEP 12 battery for kinetic-proofreading phase-lifetime finding."""

from __future__ import annotations

import argparse
import runpy
from pathlib import Path

import numpy as np


def load_base():
    remote = Path("/tmp/2026-06-21-conway-kinetic-proofreading-lifetime.py")
    local = Path("computations/2026-06-21-conway-kinetic-proofreading-lifetime.py")
    return runpy.run_path(str(remote if remote.exists() else local))


def mean_metrics(ns, kind: str, sigma: float, windows, samples: int, primes, threshold: float, rng) -> dict[str, float]:
    rows = []
    for window in windows:
        defects = ns["defects_for"](kind, sigma, window, samples, primes, rng)
        rows.append(ns["survival_metrics"](defects, threshold))
    keys = rows[0].keys()
    return {key: float(np.mean([row[key] for row in rows])) for key in keys}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=220)
    args = parser.parse_args()
    ns = load_base()
    windows = [(14.0, 84.0), (100.0, 170.0), (500.0, 570.0)]
    print("STEP12 battery: kinetic-proofreading phase-lifetime")
    print(f"samples={args.samples}")

    print("\nA. threshold stress at sigma=0.3, prime_count=160 (mean across windows)")
    print("threshold kind occupancy entry_rate off_hazard median_run survive_8 survive_16 survive_32")
    primes = ns["first_primes"](160)
    for threshold in [0.0, 0.1, 0.25, 0.5]:
        rng = np.random.default_rng(8100 + int(100 * threshold))
        for kind in ["true", "finite", "random"]:
            row = mean_metrics(ns, kind, 0.3, windows, args.samples, primes, threshold, rng)
            print(
                f"{threshold:.2f} {kind:6s} {row['occupancy']:.3f} {row['entry_rate']:.3f} "
                f"{row['off_hazard']:.4f} {row['median_run']:.2f} "
                f"{row['survive_8']:.3f} {row['survive_16']:.3f} {row['survive_32']:.3f}"
            )

    print("\nB. sigma boundary at threshold=0.0, prime_count=160 (mean across windows)")
    print("sigma true_entry finite_entry true_off finite_off true_survive8 finite_survive8 random_survive8")
    for sigma in [0.2, 0.3, 0.4, 0.5, 0.7, 0.9, 1.2]:
        rng = np.random.default_rng(9200 + int(100 * sigma))
        true = mean_metrics(ns, "true", sigma, windows, args.samples, primes, 0.0, rng)
        finite = mean_metrics(ns, "finite", sigma, windows, args.samples, primes, 0.0, rng)
        random = mean_metrics(ns, "random", sigma, windows, args.samples, primes, 0.0, rng)
        print(
            f"{sigma:.1f} {true['entry_rate']:.3f} {finite['entry_rate']:.3f} "
            f"{true['off_hazard']:.4f} {finite['off_hazard']:.4f} "
            f"{true['survive_8']:.3f} {finite['survive_8']:.3f} {random['survive_8']:.3f}"
        )

    print("\nC. finite-Euler prime-count stress at sigma=0.3, threshold=0.0")
    print("prime_count finite_entry finite_off finite_survive8 finite_survive16 true_survive16")
    for n in [30, 80, 160, 240]:
        pset = ns["first_primes"](n)
        rng = np.random.default_rng(10300 + n)
        true = mean_metrics(ns, "true", 0.3, windows, args.samples, pset, 0.0, rng)
        finite = mean_metrics(ns, "finite", 0.3, windows, args.samples, pset, 0.0, rng)
        print(
            f"{n:3d} {finite['entry_rate']:.3f} {finite['off_hazard']:.4f} "
            f"{finite['survive_8']:.3f} {finite['survive_16']:.3f} {true['survive_16']:.3f}"
        )

    print("\nD. method ledger for scientific-method moves")
    print("1 split: entry/on-rate and off-hazard/lifetime are reported separately.")
    print("2 attack-false: high occupancy alone is insufficient; true often has lower entry but longer survival.")
    print("3 reverse: finite controls can match occupancy but not long-run survival at sigma=0.3.")
    print("4 viewpoint: pointwise Delta is re-represented as a run-length survival process.")
    print("5 visual: proofreading depth becomes the length of a visible uninterrupted positive-defect run.")
    print("6 action: repeated rejection tests phase persistence, not amplitude size.")
    print("7 essentials: binary positive-defect runs are enough for the lifetime discriminator.")
    print("8 similar objects: finite Euler and random-phase controls are the similar objects.")
    print("9 small cases: finite prime_count=30 already has short-run behavior.")
    print("10 extremes: threshold=0.5 and sigma=1.2 are boundary stresses.")
    print("11 experiments: threshold, sigma, and prime-count sweeps are the probes.")
    print("12 invariant: true left-strip survival-depth advantage persists across windows.")
    print("13 monotone: survival advantage decreases moving right in sigma.")
    print("14 weaken: claim only left-strip lifetime/off-rate advantage.")
    print("15 strengthen: universal-depth or right-strip claim is false.")
    print("16 minimal counterexample: sigma=1.2 gives true and finite similar lifetimes.")
    print("17 representation: run-length survival is the required representation change.")
    print("18 theorem-tool resemblance: needs a persistence/hazard bound for phase-defect sign.")
    print("19 fake-proof gap: positive median Delta does not imply long-run survival without dependence control.")
    print("20 missing lemma: left-strip positive-defect run-length tail lower bound for true zeta.")
    print("21 dependency: prove entry/off decomposition, then survival-tail separation, then finite-control bound.")
    print("22 nearby false: more amplitude or more finite primes does not create true-like long survival.")
    print("23 boundary cases: left strip survives; right strip and high thresholds delimit the claim.")


if __name__ == "__main__":
    main()
