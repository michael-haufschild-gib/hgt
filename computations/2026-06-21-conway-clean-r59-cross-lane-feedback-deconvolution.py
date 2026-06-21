#!/usr/bin/env python3
"""Clean Finding 59 candidate: feedback-deconvolution passport for cross-lane kernels.

ResearchNode:
    GPT topic #47, cross-lane kernel K(sigma, sigma').

Random NODE:
    Baryonic feedback alters late-time small-scale power, complicating
    reconstruction of primordial fluctuations.

NODE constraint:
    The observed late-time spectrum is a product/composition of primordial
    structure and a downstream feedback transfer. Raw observed correlations are
    not the primordial kernel unless the feedback operator is absent or
    deconvolved.

STEP 8 transfer options:
    A_sigma_lane_feedback_deconvolution: observed sigma-lane events are a
      downstream lane-mixed version of a native event field.
    B_small_scale_suppression_threshold_shift: feedback only changes event
      thresholds.
    C_common_feedback_as_noise_conditioning: treat it as a common-noise mode.

Continue with A. It differs from existing common-noise conditioning: this is a
lane-space transfer operator, not a shared time field.

STEP 9 method #13:
    Find a monotone quantity. Sweep feedback strength alpha and track observed
    off-diagonal kernel mass, deconvolved mass, and feedback condition number.
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


def node_validation() -> None:
    print("NODE validation: feedback transfer distorts reconstructed primordial power")
    print("alpha small_scale_suppression inferred_tilt_shift")
    k = np.geomspace(0.02, 5.0, 400)
    primordial = k ** -0.04
    k_feedback = 0.8
    for alpha in [0.0, 0.2, 0.4, 0.6, 0.8]:
        transfer = 1.0 - alpha * (k * k) / (k * k + k_feedback * k_feedback)
        observed = primordial * transfer
        # Fit log P = a + tilt log k on the high-k half.
        high = k > 0.7
        fit_prim = np.polyfit(np.log(k[high]), np.log(primordial[high]), 1)[0]
        fit_obs = np.polyfit(np.log(k[high]), np.log(observed[high]), 1)[0]
        print(f"{alpha:4.1f} {transfer[-1]:23.4f} {fit_obs - fit_prim:19.4f}")
    print(
        "Interpretation: increasing feedback monotonically suppresses small-scale "
        "power and biases the inferred primordial tilt if not deconvolved."
    )


def lane_feedback_matrix(lanes: int, alpha: float) -> np.ndarray:
    """Column-stochastic nearest-neighbor lane mixing."""

    matrix = (1.0 - alpha) * np.eye(lanes)
    for source in range(lanes):
        neighbors: list[int] = []
        if source > 0:
            neighbors.append(source - 1)
        if source < lanes - 1:
            neighbors.append(source + 1)
        for target in neighbors:
            matrix[source, target] += alpha / len(neighbors)
    return matrix


def offdiag_mass(events: np.ndarray) -> float:
    cov = np.cov(events, rowvar=False, bias=True)
    lanes = cov.shape[0]
    return float((np.sum(np.abs(cov)) - np.sum(np.abs(np.diag(cov)))) / (lanes * (lanes - 1)))


def synthetic_independent_demo() -> None:
    rng = np.random.default_rng(260621591)
    samples = 2400
    lanes = 9
    rates = np.linspace(0.15, 0.35, lanes)
    native = (rng.random((samples, lanes)) < rates).astype(float)
    native_mass = offdiag_mass(native)

    print("\nSynthetic no-native-coupling lane test")
    print("alpha observed_offdiag deconvolved_offdiag condition_number")
    for alpha in [0.0, 0.2, 0.4, 0.6]:
        feedback = lane_feedback_matrix(lanes, alpha)
        observed = native @ feedback
        deconvolved = observed @ np.linalg.inv(feedback)
        print(
            f"{alpha:4.1f} {offdiag_mass(observed):16.6f} "
            f"{offdiag_mass(deconvolved):19.6f} {np.linalg.cond(feedback):16.3f}"
        )
    print(f"native_offdiag={native_mass:.6f}")


def phase_event_matrix(kind: str, sigmas: np.ndarray, window: tuple[float, float]) -> np.ndarray:
    spine = load_spine_helper()
    rng = np.random.default_rng(260621592)
    primes = spine.first_primes(120)
    columns = []
    for sigma in sigmas:
        values = spine.phase_series(kind, float(sigma), window, 512, primes, rng)
        threshold = float(np.quantile(values, 0.75))
        columns.append((values > threshold).astype(float))
    return np.stack(columns, axis=1)


def ht_transfer() -> None:
    sigmas = np.linspace(0.2, 1.2, 9)
    window = (100.0, 170.0)
    print("\nHT transfer: cross-lane feedback-deconvolution passport")
    print("kind alpha native_offdiag observed_offdiag deconvolved_offdiag condition_number")
    for kind in ["true", "finite", "random"]:
        native = phase_event_matrix(kind, sigmas, window)
        native_mass = offdiag_mass(native)
        for alpha in [0.0, 0.2, 0.4, 0.6]:
            feedback = lane_feedback_matrix(len(sigmas), alpha)
            observed = native @ feedback
            deconvolved = observed @ np.linalg.inv(feedback)
            print(
                f"{kind:6s} {alpha:4.1f} {native_mass:14.6f} "
                f"{offdiag_mass(observed):16.6f} {offdiag_mass(deconvolved):20.6f} "
                f"{np.linalg.cond(feedback):16.3f}"
            )
    print(
        "\nInterpretation: a sigma-lane kernel claim needs a feedback-deconvolution "
        "passport: raw observed K, feedback operator or admissible family, "
        "deconvolved K, and the condition number/noise amplification. This is "
        "separate from common-time-field conditioning."
    )


def main() -> None:
    node_validation()
    synthetic_independent_demo()
    ht_transfer()


if __name__ == "__main__":
    main()
