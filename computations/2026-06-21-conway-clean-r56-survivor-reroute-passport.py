#!/usr/bin/env python3
"""Clean Finding 56 candidate: reroute passport for survivor spines.

ResearchNode:
    GPT topic #52, survivor spines: do positive carrier states have descendant
    paths uniquely in the true completed field?

Random NODE:
    Behavioral adaptation to previous failed route attempts, blocked exits, or
    unexpectedly slow corridors in stochastic crowd-flow models.

NODE constraint:
    The observed path distribution is not only a geometry/readout. It is also a
    history-dependent route policy: as failed or blocked routes are penalized,
    traffic can collapse onto a different route.

STEP 8 transfer options, scored informally by edit distance from the NODE test:
    A_route_failure_penalty_on_phase_bins: replace crowd routes by vertical
      phase-carrier bins; replace failed exits by non-positive phase samples.
    B_tree_prune_descendant_branches: replace corridors by dyadic ancestry
      branches and block branches with short positive runs.
    C_contour_exit_reroute: replace building exits by contour-side exits and
      penalize event-root refinements that lose source certificates.

Continue with A: it is the minimal transfer and stays on the survivor-spine
question without introducing contour machinery.

STEP 9 method #13:
    Find a monotone quantity. Sweep a route-adaptation strength alpha and track
    expected failed-route exposure. Under the model it must decrease with alpha;
    the useful question is whether spine uniqueness is stable under this
    monotone rerouting, or is created by it.
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
    centered = score - float(np.max(score))
    weights = np.exp(centered)
    return weights / float(np.sum(weights))


def entropy(prob: np.ndarray) -> float:
    return float(-np.sum(prob * np.log(prob + 1e-300)) / math.log(len(prob)))


def crowd_node_validation() -> None:
    """Validate the NODE on a tiny route-choice model.

    Each route has a base time and a failure/block probability. Adaptive agents
    choose with softmax(-base_time - alpha * failure_probability). The monotone
    quantity is expected failure exposure under the chosen route distribution.
    """

    names = np.asarray(["fast-but-blocked", "middle", "long-safe"])
    base_time = np.asarray([1.00, 1.22, 1.55])
    failure = np.asarray([0.62, 0.17, 0.03])
    alphas = [0.0, 0.5, 1.0, 2.0, 4.0, 8.0]

    print("NODE validation: blocked-exit adaptation in a crowd-flow toy model")
    print("alpha top_route entropy expected_failure expected_time route_probs")
    last_fail = float("inf")
    monotone = True
    for alpha in alphas:
        prob = softmax(-3.0 * (base_time + alpha * failure))
        expected_failure = float(np.dot(prob, failure))
        expected_time = float(np.dot(prob, base_time))
        monotone = monotone and expected_failure <= last_fail + 1e-12
        last_fail = expected_failure
        top = names[int(np.argmax(prob))]
        probs = ",".join(f"{p:.3f}" for p in prob)
        print(
            f"{alpha:4.1f} {top:16s} {entropy(prob):.3f} "
            f"{expected_failure:.4f} {expected_time:.4f} {probs}"
        )
    print(f"NODE monotone expected-failure decrease: {monotone}")


def route_passport(values: np.ndarray, bins: int, threshold: float, alpha: float) -> dict[str, float]:
    n = (len(values) // bins) * bins
    blocks = values[:n].reshape(bins, -1)
    success = np.mean(blocks > threshold, axis=1)
    failure = 1.0 - success
    quality = np.mean(np.log1p(np.maximum(blocks, 0.0)), axis=1)

    # Quality is the passive positive-carrier reserve; alpha penalizes failed
    # route attempts. Larger alpha should lower expected failure exposure.
    prob = softmax(6.0 * quality - alpha * failure)
    return {
        "entropy": entropy(prob),
        "expected_failure": float(np.dot(prob, failure)),
        "expected_quality": float(np.dot(prob, quality)),
        "top_share": float(np.max(prob)),
        "top_bin": float(np.argmax(prob)),
        "success_mean": float(np.mean(success)),
    }


def sweep(values: np.ndarray, bins: int, threshold: float) -> tuple[list[dict[str, float]], bool]:
    alphas = [0.0, 1.0, 2.0, 4.0, 8.0, 16.0]
    rows = [route_passport(values, bins, threshold, alpha) for alpha in alphas]
    failures = [row["expected_failure"] for row in rows]
    monotone = all(failures[i + 1] <= failures[i] + 1e-12 for i in range(len(failures) - 1))
    passive_prob = route_distribution(values, bins, threshold, 0.0)
    for row, alpha in zip(rows, alphas):
        prob = route_distribution(values, bins, threshold, alpha)
        row["alpha"] = alpha
        row["tv_from_passive"] = float(0.5 * np.sum(np.abs(prob - passive_prob)))
        row["top_switch"] = float(np.argmax(prob) != np.argmax(passive_prob))
    return rows, monotone


def route_distribution(values: np.ndarray, bins: int, threshold: float, alpha: float) -> np.ndarray:
    n = (len(values) // bins) * bins
    blocks = values[:n].reshape(bins, -1)
    success = np.mean(blocks > threshold, axis=1)
    failure = 1.0 - success
    quality = np.mean(np.log1p(np.maximum(blocks, 0.0)), axis=1)
    return softmax(6.0 * quality - alpha * failure)


def ht_transfer() -> None:
    spine = load_spine_helper()
    rng = np.random.default_rng(260621256)
    primes = spine.first_primes(160)
    windows = [(100.0, 170.0), (500.0, 570.0), (14.0, 84.0)]
    sigmas = [0.3, 0.5, 0.7, 1.2]
    bins = 32
    threshold = 0.0

    print("\nHT transfer: passive-vs-adaptive reroute passport for survivor spines")
    print(f"bins={bins} threshold={threshold} prime_count=160 samples=512")
    print(
        "kind sigma window occ fail0 fail16 fail_drop "
        "entropy0 entropy16 top0 top16 tv16 switched monotone"
    )

    rows_by_key: dict[tuple[float, tuple[float, float], str], dict[str, float]] = {}
    for sigma in sigmas:
        for window in windows:
            for kind in ["true", "finite", "random"]:
                values = spine.phase_series(kind, sigma, window, 512, primes, rng)
                rows, monotone = sweep(values, bins, threshold)
                first = rows[0]
                last = rows[-1]
                out = {
                    "occ": first["success_mean"],
                    "fail0": first["expected_failure"],
                    "fail16": last["expected_failure"],
                    "fail_drop": first["expected_failure"] - last["expected_failure"],
                    "entropy0": first["entropy"],
                    "entropy16": last["entropy"],
                    "top0": first["top_share"],
                    "top16": last["top_share"],
                    "tv16": last["tv_from_passive"],
                    "switched": max(row["top_switch"] for row in rows),
                    "monotone": float(monotone),
                }
                rows_by_key[(sigma, window, kind)] = out
                print(
                    f"{kind:6s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                    f"{out['occ']:.3f} {out['fail0']:.4f} {out['fail16']:.4f} "
                    f"{out['fail_drop']:.4f} {out['entropy0']:.3f} {out['entropy16']:.3f} "
                    f"{out['top0']:.3f} {out['top16']:.3f} {out['tv16']:.3f} "
                    f"{int(out['switched'])} {int(out['monotone'])}"
                )

    print("\nStress summaries")
    t = rows_by_key[(0.5, (100.0, 170.0), "true")]
    f = rows_by_key[(0.5, (100.0, 170.0), "finite")]
    print(
        "middle-strip reroute can over-concentrate a finite control: "
        f"true top16={t['top16']:.3f}, tv16={t['tv16']:.3f}; "
        f"finite top16={f['top16']:.3f}, tv16={f['tv16']:.3f}"
    )
    t = rows_by_key[(1.2, (100.0, 170.0), "true")]
    f = rows_by_key[(1.2, (100.0, 170.0), "finite")]
    print(
        "right-strip collapse under rerouting: "
        f"true fail16={t['fail16']:.4f}, top16={t['top16']:.3f}, tv16={t['tv16']:.3f}; "
        f"finite fail16={f['fail16']:.4f}, top16={f['top16']:.3f}, tv16={f['tv16']:.3f}"
    )
    t = rows_by_key[(0.3, (100.0, 170.0), "true")]
    f = rows_by_key[(0.3, (100.0, 170.0), "finite")]
    r = rows_by_key[(0.3, (100.0, 170.0), "random")]
    print(
        "left-strip full-positive true path has zero reroute exposure, while controls "
        "are reroute-sensitive: "
        f"true tv16={t['tv16']:.3f}, finite tv16={f['tv16']:.3f}, random tv16={r['tv16']:.3f}"
    )
    print(
        "\nInterpretation: raw survivor-spine uniqueness is not enough. A claim that "
        "positive carrier states have native descendant paths must publish the "
        "passive spine, the adaptive reroute sweep, finite/random controls, and "
        "the right-strip collapse check. If uniqueness appears only after alpha "
        "penalizes failed routes, it is route-policy structure, not completed-field "
        "descendant geometry."
    )


def main() -> None:
    crowd_node_validation()
    ht_transfer()


if __name__ == "__main__":
    main()
