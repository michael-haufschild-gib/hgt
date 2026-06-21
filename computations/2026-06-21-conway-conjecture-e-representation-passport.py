#!/usr/bin/env python3
"""Numerical-representation passport for Conjecture E kill gates."""

from __future__ import annotations

import math

import mpmath as mp
import numpy as np


def node_hidden_flag_reassociation() -> None:
    block = [1e16, 1.0, -1e16]
    values = block * 10_000
    sequential = sum(values)
    compensated = math.fsum(values)
    grouped = sum(values[0::3]) + sum(values[1::3]) + sum(values[2::3])

    print("NODE: hidden execution/evaluation flags can affect output")
    print("example=sum of repeated [1e16, 1, -1e16]")
    print(f"sequential_python_sum={sequential:.1f}")
    print(f"compensated_math_fsum={compensated:.1f}")
    print(f"grouped_reassociated_sum={grouped:.1f}")
    print(
        "constraint: a claimed numerical fact needs an execution/tolerance "
        "passport when the computation is non-associative or ill-conditioned"
    )
    print()


def first_primes(k: int) -> list[int]:
    primes: list[int] = []
    candidate = 2
    while len(primes) < k:
        if all(candidate % p for p in primes):
            primes.append(candidate)
        candidate += 1
    return primes


def smooth_zero_inverse(n: int) -> float:
    a = mp.mpf(n) - mp.mpf(11) / 8
    y = a / mp.lambertw(a / mp.e)
    return float(2 * mp.pi * y)


def feature_matrix(t: np.ndarray, primes: list[int], k: int) -> np.ndarray:
    columns = [np.ones_like(t), 1.0 / np.log(t)]
    for p in primes[:k]:
        frequency = math.log(p)
        columns.append(np.sin(t * frequency))
        columns.append(np.cos(t * frequency))
    return np.column_stack(columns)


def margins(
    actual: np.ndarray,
    baseline: np.ndarray,
    predicted: np.ndarray,
) -> tuple[float, float, float]:
    ordinate_margin = np.abs(actual - baseline) - np.abs(actual - predicted)
    spacing_margin = np.abs(np.diff(actual) - np.diff(baseline)) - np.abs(
        np.diff(actual) - np.diff(predicted)
    )
    return (
        float(np.mean(ordinate_margin)),
        float(np.mean(spacing_margin)),
        float(np.mean(ordinate_margin > 0.0)),
    )


def transfer_representation_passport() -> None:
    mp.mp.dps = 50
    n_values = np.arange(30, 230)
    zeros = np.array([float(mp.im(mp.zetazero(int(n)))) for n in n_values])
    baseline = np.array([smooth_zero_inverse(int(n)) for n in n_values])
    residual = zeros - baseline

    train = (n_values >= 30) & (n_values <= 99)
    test = (n_values >= 100) & (n_values <= 119)
    primes = first_primes(60)

    print("TRANSFER: ResearchNode #34 Conjecture E kill gate")
    print(
        "method #17 change representation: same prime-wave residual source, "
        "different solver/tolerance representations"
    )
    print(
        "positive margins mean the fitted correction improves over the smooth "
        "Riemann-von Mangoldt inverse baseline"
    )
    print(
        "K features cond flag flag_value beta_norm ordinate_margin spacing_margin "
        "ordinate_improvement_rate"
    )

    for k in [8, 13, 20, 30, 34]:
        x_train = feature_matrix(baseline[train], primes, k)
        y_train = residual[train]
        x_test = feature_matrix(baseline[test], primes, k)
        condition = np.linalg.cond(x_train)

        for rcond in [None, 0.01, 0.10]:
            beta, *_ = np.linalg.lstsq(x_train, y_train, rcond=rcond)
            predicted = baseline[test] + x_test @ beta
            ordinate, spacing, rate = margins(zeros[test], baseline[test], predicted)
            flag_value = "None" if rcond is None else f"{rcond:.2g}"
            print(
                f"{k:02d} {x_train.shape[1]:02d} {condition:8.2f} "
                f"rcond {flag_value:>4s} {np.linalg.norm(beta):9.4f} "
                f"{ordinate:+.6f} {spacing:+.6f} {rate:.3f}"
            )

        for ridge in [1e-8, 1e-4, 1e-1]:
            lhs = x_train.T @ x_train + ridge * np.eye(x_train.shape[1])
            rhs = x_train.T @ y_train
            beta = np.linalg.solve(lhs, rhs)
            predicted = baseline[test] + x_test @ beta
            ordinate, spacing, rate = margins(zeros[test], baseline[test], predicted)
            print(
                f"{k:02d} {x_train.shape[1]:02d} {condition:8.2f} "
                f"ridge {ridge:>4.0e} {np.linalg.norm(beta):9.4f} "
                f"{ordinate:+.6f} {spacing:+.6f} {rate:.3f}"
            )

    print()
    print("GATE SUMMARY")
    print(
        "for K=34, the untruncated least-squares representation fails badly "
        "(ordinate -3.883, spacing -5.770), while rcond=0.01 or ridge=1e-1 "
        "turns the same source into an apparent pass"
    )
    print(
        "Conjecture E kill gates must therefore include a representation passport: "
        "solver, precision, truncation, ridge/tolerance, condition number, and "
        "a pass/fail stability strip"
    )


def main() -> None:
    node_hidden_flag_reassociation()
    transfer_representation_passport()


if __name__ == "__main__":
    main()
