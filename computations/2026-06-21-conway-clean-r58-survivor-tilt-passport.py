#!/usr/bin/env python3
"""Clean Finding 58 candidate: chemical-potential tilt passport for survivor spines.

ResearchNode:
    GPT topic #52, survivor spines.

Random NODE:
    Conserved charges and chemical potentials shift cosmological phase
    boundaries.

NODE constraint:
    A phase boundary is not determined by temperature/control alone when a
    conserved charge is present. The chemical potential tilts the ensemble and
    can move the apparent transition.

STEP 8 transfer options:
    A_survivor_ensemble_tilt: terminal positive-carrier bins are weighted by
      an exponential chemical-potential tilt of their carrier reserve.
    B_charge_constrained_descendant_tree: descendant branches conserve a
      synthetic carrier charge across levels.
    C_phase_boundary_shift_in_sigma: sigma-lane transition boundary is moved
      by a charge-like Lagrange multiplier.

Continue with A. It minimally changes the NODE: chemical potential becomes an
ensemble tilt, and phase boundary becomes survivor-spine concentration.

STEP 9 method #19:
    Write the fake proof. The fake proof says: a unique positive spine under a
    survivor ensemble is native. The gap is that the survivor ensemble may have
    an implicit chemical-potential tilt.
"""

from __future__ import annotations

import importlib.util
import math
from pathlib import Path

import numpy as np


ROOT = Path(__file__).resolve().parents[1]
SPINE_HELPER = ROOT / "computations" / "2026-06-21-hgt-STEP8-branching-ancestry-ht-spine.py"


def load_spine_helper():
    spec = importlib.util.spec_from_file_location("spine_helper", SPINE_HELPER)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {SPINE_HELPER}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def softmax(score: np.ndarray) -> np.ndarray:
    score = score - float(np.max(score))
    weights = np.exp(score)
    return weights / float(np.sum(weights))


def entropy(prob: np.ndarray) -> float:
    return float(-np.sum(prob * np.log(prob + 1e-300)) / math.log(len(prob)))


def node_validation() -> None:
    print("NODE validation: chemical potential shifts a two-phase boundary")
    print("Free energies: F_A=0, F_B=DeltaE - T*DeltaS - mu*DeltaQ")
    print("mu T_critical phase_at_T1.0")
    delta_e = 1.0
    delta_s = 1.0
    delta_q = 0.35
    for mu in [-1.5, -0.5, 0.0, 0.5, 1.5]:
        tcrit = (delta_e - mu * delta_q) / delta_s
        f_b_at_one = delta_e - 1.0 * delta_s - mu * delta_q
        phase = "B" if f_b_at_one < 0.0 else "A"
        print(f"{mu:5.2f} {tcrit:10.4f} {phase}")
    print(
        "Interpretation: the same temperature/control can select a different "
        "phase after the conserved-charge chemical potential is changed."
    )


def route_distribution(values: np.ndarray, lam: float, bins: int = 32) -> dict[str, float]:
    n = (len(values) // bins) * bins
    blocks = values[:n].reshape(bins, -1)
    success = np.mean(blocks > 0.0, axis=1)
    reserve = np.mean(np.log1p(np.maximum(blocks, 0.0)), axis=1)
    if float(np.std(reserve)) > 1e-12:
        charge = (reserve - float(np.mean(reserve))) / float(np.std(reserve))
    else:
        charge = np.zeros_like(reserve)

    prob = softmax(np.log(success + 1e-6) + lam * charge)
    neutral = softmax(np.log(success + 1e-6))
    return {
        "top_share": float(np.max(prob)),
        "entropy": entropy(prob),
        "mean_charge": float(np.dot(prob, charge)),
        "tv_from_neutral": float(0.5 * np.sum(np.abs(prob - neutral))),
        "top_bin": float(np.argmax(prob)),
        "occupancy": float(np.mean(success)),
        "reserve_mean": float(np.mean(reserve)),
    }


def transfer() -> None:
    spine = load_spine_helper()
    rng = np.random.default_rng(260621258)
    primes = spine.first_primes(160)
    cases = [
        (0.3, (100.0, 170.0)),
        (0.5, (100.0, 170.0)),
        (1.2, (100.0, 170.0)),
    ]
    lambdas = [-2.0, -1.0, 0.0, 1.0, 2.0]

    print("\nHT transfer: survivor-spine ensemble tilt passport")
    print("distribution: p(bin) proportional to success(bin) * exp(lambda * standardized_reserve)")
    print("kind sigma window lambda occupancy top_share entropy mean_charge tv_from_neutral top_bin")
    table: dict[tuple[str, float, tuple[float, float], float], dict[str, float]] = {}
    for sigma, window in cases:
        for kind in ["true", "finite", "random"]:
            values = spine.phase_series(kind, sigma, window, 512, primes, rng)
            for lam in lambdas:
                row = route_distribution(values, lam)
                table[(kind, sigma, window, lam)] = row
                print(
                    f"{kind:6s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {lam:5.1f} "
                    f"{row['occupancy']:.3f} {row['top_share']:.3f} {row['entropy']:.3f} "
                    f"{row['mean_charge']:.3f} {row['tv_from_neutral']:.3f} {int(row['top_bin']):2d}"
                )

    print("\nStress summaries")
    t = table[("true", 0.5, (100.0, 170.0), 2.0)]
    f = table[("finite", 0.5, (100.0, 170.0), 2.0)]
    print(
        "middle-strip positive tilt can over-concentrate finite controls: "
        f"true top_share={t['top_share']:.3f}, tv={t['tv_from_neutral']:.3f}; "
        f"finite top_share={f['top_share']:.3f}, tv={f['tv_from_neutral']:.3f}"
    )
    t = table[("true", 1.2, (100.0, 170.0), 2.0)]
    f = table[("finite", 1.2, (100.0, 170.0), 2.0)]
    print(
        "right-strip collapse under the same tilt: "
        f"true top_share={t['top_share']:.3f}, tv={t['tv_from_neutral']:.3f}; "
        f"finite top_share={f['top_share']:.3f}, tv={f['tv_from_neutral']:.3f}"
    )
    t_neg = table[("true", 0.5, (100.0, 170.0), -2.0)]
    t_pos = table[("true", 0.5, (100.0, 170.0), 2.0)]
    print(
        "same true window, opposite chemical-potential signs select different "
        f"spines: top_bin_minus={int(t_neg['top_bin'])}, top_share_minus={t_neg['top_share']:.3f}; "
        f"top_bin_plus={int(t_pos['top_bin'])}, top_share_plus={t_pos['top_share']:.3f}"
    )
    print(
        "\nFake-proof gap: uniqueness under a survivor ensemble does not prove a "
        "native completed-field descendant path unless the ensemble's implicit "
        "tilt is fixed or swept. Report neutral, positive-tilt, negative-tilt, "
        "finite/random controls, and right-strip collapse."
    )


def main() -> None:
    node_validation()
    transfer()


if __name__ == "__main__":
    main()
