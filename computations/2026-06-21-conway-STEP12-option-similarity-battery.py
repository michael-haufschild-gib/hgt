#!/usr/bin/env python3
"""STEP 12 battery for option-similarity suppression finding."""

from __future__ import annotations

import argparse
import runpy
from pathlib import Path

import numpy as np


def load_base():
    remote = Path("/tmp/2026-06-21-conway-option-similarity-suppression.py")
    local = Path("computations/2026-06-21-conway-option-similarity-suppression.py")
    return runpy.run_path(str(remote if remote.exists() else local))


def average_rows(ns, sigma: float, prime_count: int, samples: int):
    primes = ns["first_primes"](prime_count)
    rng = np.random.default_rng(3300 + int(100 * sigma) + prime_count)
    windows = [(14.0, 84.0), (100.0, 170.0), (500.0, 570.0)]
    vals = []
    for window in windows:
        traces = {kind: ns["make_trace"](kind, sigma, window, samples, primes, rng) for kind in ["true", "finite", "random"]}
        for distractor in ["finite", "random"]:
            amp = ns["suppression"](traces["true"], traces[distractor], "amp")
            phase = ns["suppression"](traces["true"], traces[distractor], "phase")
            vals.append(
                {
                    "distractor": distractor,
                    "raw": amp["raw_median"],
                    "amp_sim": amp["sim_median"],
                    "phase_sim": phase["sim_median"],
                    "amp_supp": amp["suppression_median"],
                    "phase_supp": phase["suppression_median"],
                    "false_similarity": amp["sim_median"] - phase["sim_median"],
                }
            )
    out = {}
    for distractor in ["finite", "random"]:
        rows = [v for v in vals if v["distractor"] == distractor]
        out[distractor] = {key: float(np.mean([r[key] for r in rows])) for key in rows[0] if key != "distractor"}
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=180)
    args = parser.parse_args()
    ns = load_base()
    print("STEP12 battery: option-similarity suppression")
    print(f"samples={args.samples}")

    print("\nA. sigma sweep: amplitude-similarity minus phase-similarity")
    print("sigma distractor raw amp_sim phase_sim false_similarity amp_supp phase_supp")
    for sigma in [0.2, 0.3, 0.4, 0.5, 0.7, 0.9, 1.2]:
        rows = average_rows(ns, sigma, 160, args.samples)
        for distractor in ["finite", "random"]:
            row = rows[distractor]
            print(
                f"{sigma:.1f} {distractor:6s} {row['raw']:.4f} {row['amp_sim']:.4f} "
                f"{row['phase_sim']:.4f} {row['false_similarity']:+.4f} "
                f"{row['amp_supp']:.4f} {row['phase_supp']:.4f}"
            )

    print("\nB. finite-Euler prime-count stress at sigma=0.3")
    print("prime_count finite_amp_sim finite_phase_sim finite_false_similarity finite_phase_supp random_false_similarity")
    for n in [30, 80, 160, 240]:
        rows = average_rows(ns, 0.3, n, args.samples)
        finite = rows["finite"]
        random = rows["random"]
        print(
            f"{n:3d} {finite['amp_sim']:.4f} {finite['phase_sim']:.4f} "
            f"{finite['false_similarity']:+.4f} {finite['phase_supp']:.4f} {random['false_similarity']:+.4f}"
        )

    print("\nC. method ledger for scientific-method moves")
    print("1 split: amplitude-similarity and phase-similarity are separated.")
    print("2 attack-false: amplitude-similar alternatives can be false competitors.")
    print("3 reverse: phase-similarity, not amplitude-similarity, predicts valid suppression.")
    print("4 viewpoint: the option space is a feature space, not a scalar magnitude list.")
    print("5 visual: similar distractors crowd the target only in the metric they share.")
    print("6 action: suppression is local normalization by neighboring alternatives.")
    print("7 essentials: two feature maps are enough for the boundary test.")
    print("8 similar objects: finite Euler and random-phase controls are the neighbors tested.")
    print("9 small cases: finite prime_count=30 already shows phase-dissimilarity on the left.")
    print("10 extremes: sigma=1.2 has phase-similar finite controls but raw value collapses.")
    print("11 experiments: sigma and prime-count sweeps are the probes.")
    print("12 invariant: left-strip random-phase is amplitude-similar but phase-dissimilar.")
    print("13 monotone: raw value and false-similarity decline moving rightward.")
    print("14 weaken: claim only metric-dependence of competition, not a new phase statistic.")
    print("15 strengthen: universal phase-dissimilarity is false at sigma=1.2.")
    print("16 minimal counterexample: random-phase preserves amplitudes but loses phase-neighbor status.")
    print("17 representation: feature-metric representation is the crux.")
    print("18 theorem-tool resemblance: would need conditional metric-separation of phase features.")
    print("19 fake-proof gap: amplitude closeness does not imply phase closeness.")
    print("20 missing lemma: left-strip phase-feature separation between true zeta and finite/random alternatives.")
    print("21 dependency: NODE similarity normalization -> feature choice -> phase-vs-amplitude competition -> boundary.")
    print("22 nearby false: amplitude normalization alone gives false suppression.")
    print("23 boundary cases: left strip has value plus phase separation; right strip has similarity but no value.")


if __name__ == "__main__":
    main()
