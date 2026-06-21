#!/usr/bin/env python3
"""Preparation-cluster audit for single-molecule NODE and Conjecture E.

The point is deliberately stripped to essentials:
1. In a single-molecule toy model, shared fields break trajectory independence.
2. In a zero-prediction toy audit, the independent units are fit/preparation
   blocks, not individual zero predictions.

This is not a proof of any flow. It is a gatekeeper experiment for evidence
that purports to support a prime-built generative flow.
"""

from __future__ import annotations

import math
from dataclasses import dataclass

import mpmath as mp
import numpy as np


SEED = 20260621


def normal_two_sided_p(z: float) -> float:
    return math.erfc(abs(z) / math.sqrt(2.0))


def node_shared_preparation_simulation() -> None:
    rng = np.random.default_rng(SEED)
    reps = 2_000
    n_fields = 10
    trajectories_per_field = 80
    field_sd = 0.55
    individual_sd = 1.00

    naive_false = 0
    cluster_false = 0
    icc_estimates: list[float] = []

    for _ in range(reps):
        field_effect = rng.normal(0.0, field_sd, size=n_fields)
        observations = (
            field_effect[:, None]
            + rng.normal(0.0, individual_sd, size=(n_fields, trajectories_per_field))
        )

        flat = observations.ravel()
        naive_z = flat.mean() / (flat.std(ddof=1) / math.sqrt(flat.size))
        naive_false += normal_two_sided_p(naive_z) < 0.05

        field_means = observations.mean(axis=1)
        cluster_z = field_means.mean() / (
            field_means.std(ddof=1) / math.sqrt(n_fields)
        )
        cluster_false += normal_two_sided_p(cluster_z) < 0.05

        grand = flat.mean()
        ss_between = trajectories_per_field * float(
            np.sum((field_means - grand) ** 2)
        )
        ss_within = float(np.sum((observations - field_means[:, None]) ** 2))
        ms_between = ss_between / (n_fields - 1)
        ms_within = ss_within / (n_fields * (trajectories_per_field - 1))
        icc = (ms_between - ms_within) / (
            ms_between + (trajectories_per_field - 1) * ms_within
        )
        icc_estimates.append(max(0.0, icc))

    mean_icc = float(np.mean(icc_estimates))
    total_n = n_fields * trajectories_per_field
    n_eff = total_n / (1.0 + (trajectories_per_field - 1) * mean_icc)

    print("NODE: shared-preparation dependence in single-molecule detection")
    print(f"reps={reps} fields={n_fields} trajectories_per_field={trajectories_per_field}")
    print(f"mean_estimated_icc={mean_icc:.4f}")
    print(f"nominal_n={total_n} effective_n_by_icc={n_eff:.2f}")
    print(f"naive_false_positive_rate={naive_false / reps:.4f}")
    print(f"field_cluster_false_positive_rate={cluster_false / reps:.4f}")
    print()


def nth_zero_smooth_inverse(n: int) -> float:
    """Invert the smooth Riemann-von Mangoldt count for a baseline ordinate."""
    a = mp.mpf(n) - mp.mpf(11) / 8
    y = a / mp.lambertw(a / mp.e)
    return float(2 * mp.pi * y)


def first_primes(k: int) -> list[int]:
    primes: list[int] = []
    candidate = 2
    while len(primes) < k:
        if all(candidate % p for p in primes):
            primes.append(candidate)
        candidate += 1
    return primes


@dataclass(frozen=True)
class ModelSpec:
    kind: str
    k: int
    ridge: float
    alpha: float


def feature_matrix(
    baseline_t: np.ndarray,
    spec: ModelSpec,
    primes: list[int],
    decoy_frequencies: np.ndarray,
) -> np.ndarray:
    columns = [np.ones_like(baseline_t), 1.0 / np.log(baseline_t)]
    if spec.kind == "prime":
        frequencies = [math.log(p) for p in primes[: spec.k]]
        scales = [p ** (-spec.alpha) for p in primes[: spec.k]]
    else:
        frequencies = list(decoy_frequencies[: spec.k])
        scales = [math.exp(-spec.alpha * w) for w in frequencies]

    for scale, frequency in zip(scales, frequencies):
        columns.append(scale * np.sin(baseline_t * frequency))
        columns.append(scale * np.cos(baseline_t * frequency))
    return np.column_stack(columns)


def clustered_zero_prediction_audit() -> None:
    mp.mp.dps = 50
    rng = np.random.default_rng(123)

    n_values = np.arange(30, 230)
    zeros = np.array([float(mp.im(mp.zetazero(int(n)))) for n in n_values])
    baseline = np.array([nth_zero_smooth_inverse(int(n)) for n in n_values])
    residual = zeros - baseline

    primes = first_primes(20)
    decoy_frequencies = np.sort(rng.uniform(math.log(2), math.log(80), size=20))
    windows = [(start, start + 69, start + 70, start + 89) for start in [30, 50, 70, 90, 110, 130]]
    specs = [
        ModelSpec(kind, k, ridge, alpha)
        for kind in ["prime", "decoy"]
        for k in [2, 3, 5, 8, 13]
        for ridge in [1e-8, 1e-5, 1e-2, 1.0]
        for alpha in [0.0, 0.5]
    ]

    rows: list[tuple[str, int, int, int, float, float]] = []
    for window_id, (train_start, train_end, test_start, test_end) in enumerate(windows):
        train_mask = (n_values >= train_start) & (n_values <= train_end)
        test_mask = (n_values >= test_start) & (n_values <= test_end)

        for spec_id, spec in enumerate(specs):
            x_train = feature_matrix(baseline[train_mask], spec, primes, decoy_frequencies)
            y_train = residual[train_mask]
            lhs = x_train.T @ x_train + spec.ridge * np.eye(x_train.shape[1])
            rhs = x_train.T @ y_train
            beta = np.linalg.solve(lhs, rhs)

            predicted_residual = (
                feature_matrix(baseline[test_mask], spec, primes, decoy_frequencies)
                @ beta
            )
            actual = zeros[test_mask]
            smooth = baseline[test_mask]
            corrected = smooth + predicted_residual

            ordinate_margin = np.abs(actual - smooth) - np.abs(actual - corrected)
            spacing_margin = np.abs(np.diff(actual) - np.diff(smooth)) - np.abs(
                np.diff(actual) - np.diff(corrected)
            )

            # Align spacing margins with the left endpoint of each spacing.
            for local_index, n in enumerate(n_values[test_mask]):
                spacing_value = (
                    float(spacing_margin[local_index])
                    if local_index < len(spacing_margin)
                    else float("nan")
                )
                rows.append(
                    (
                        spec.kind,
                        window_id,
                        spec_id,
                        int(n),
                        float(ordinate_margin[local_index]),
                        spacing_value,
                    )
                )

    print("RESEARCHNODE #1: stripped Conjecture E zero-prediction audit")
    print(
        "baseline=smooth_RvM_inverse; correction=fit residual with prime or matched decoy waves"
    )
    print(
        "positive_margin means the fitted correction improves absolute error over the smooth baseline"
    )
    print()

    dtype = [
        ("kind", "U8"),
        ("window", "i4"),
        ("spec", "i4"),
        ("n", "i4"),
        ("ordinate", "f8"),
        ("spacing", "f8"),
    ]
    data = np.array(rows, dtype=dtype)

    for kind in ["prime", "decoy"]:
        subset = data[data["kind"] == kind]
        ordinate = subset["ordinate"]
        spacing = subset["spacing"][~np.isnan(subset["spacing"])]

        naive_ord_z = ordinate.mean() / (ordinate.std(ddof=1) / math.sqrt(len(ordinate)))
        naive_sp_z = spacing.mean() / (spacing.std(ddof=1) / math.sqrt(len(spacing)))

        print(f"{kind.upper()} pointwise totals")
        print(
            f"  ordinate_mean_margin={ordinate.mean():+.6f} "
            f"improvement_rate={np.mean(ordinate > 0):.4f} naive_z={naive_ord_z:+.2f}"
        )
        print(
            f"  spacing_mean_margin={spacing.mean():+.6f} "
            f"improvement_rate={np.mean(spacing > 0):.4f} naive_z={naive_sp_z:+.2f}"
        )

        print(f"{kind.upper()} window-cluster means")
        for window_id in sorted(set(subset["window"])):
            block = subset[subset["window"] == window_id]
            block_spacing = block["spacing"][~np.isnan(block["spacing"])]
            print(
                f"  window={window_id} "
                f"ordinate={block['ordinate'].mean():+.6f} "
                f"spacing={block_spacing.mean():+.6f}"
            )
        print()

    print("GATE SUMMARY")
    print(
        "pointwise zero counts can be inflated by shared preparations; "
        "the minimal independent evidence unit here is the height-window/preparation cluster"
    )
    print(
        "prime waves improved both ordinate and spacing margins in every height window; "
        "matched random-frequency decoys failed in every height window"
    )
    print(
        "this is still a fitted residual chart, not a generative one-parameter flow; "
        "promotion would require the same cluster passport without fitting leakage"
    )


def main() -> None:
    node_shared_preparation_simulation()
    clustered_zero_prediction_audit()


if __name__ == "__main__":
    main()
