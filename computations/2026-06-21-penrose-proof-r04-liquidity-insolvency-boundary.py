#!/usr/bin/env python3
"""Boundary-case experiment for the proof-route boundary-extension node.

NODE constraint: liquidity default and balance-sheet insolvency are different
barriers.  A model can be solvent by one barrier and defaulted by the other.

Transferred constraint: the shifted proof-route has two square-test barriers,
H0 = [m_{i+j}] and H1 = [m_{i+j+1}] for m_n = T_{n+1}.  Boundary cases test
whether either shifted barrier can be dropped.  A secondary one-dimensional
extension check records the Schur reserve r - b^T A^{-1} b.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

import numpy as np


@dataclass(frozen=True)
class DefaultSummary:
    leverage: float
    cash0: float
    rho: float
    first_liq: float
    first_ins: float
    joint: float
    liq_without_ins: float
    ins_without_liq: float
    no_default: float


def simulate_default_grid(
    *,
    n_paths: int = 6000,
    steps: int = 252,
    seed: int = 20260621,
) -> list[DefaultSummary]:
    rng = np.random.default_rng(seed)
    dt = 1.0 / steps
    sqrt_dt = np.sqrt(dt)

    a0 = 100.0
    sigma_a = 0.30
    sigma_c = 10.0
    mu_a = 0.02
    cash_drift = 2.0
    quarterly_due = 3.0

    rows: list[DefaultSummary] = []
    for leverage in (0.70, 0.90, 1.05):
        for cash0 in (2.0, 8.0, 20.0):
            for rho in (-0.7, 0.0, 0.7):
                a = np.full(n_paths, a0)
                cash = np.full(n_paths, cash0)
                liabilities = np.full(n_paths, leverage * a0)
                tau_liq = np.full(n_paths, steps + 1, dtype=int)
                tau_ins = np.full(n_paths, steps + 1, dtype=int)

                for t in range(1, steps + 1):
                    z1 = rng.standard_normal(n_paths)
                    z2_raw = rng.standard_normal(n_paths)
                    z2 = rho * z1 + np.sqrt(1.0 - rho * rho) * z2_raw

                    a *= np.exp((mu_a - 0.5 * sigma_a * sigma_a) * dt + sigma_a * sqrt_dt * z1)
                    liabilities *= np.exp(0.035 * dt)
                    cash += cash_drift * dt + sigma_c * sqrt_dt * z2
                    if t in (63, 126, 189, 252):
                        cash -= quarterly_due

                    new_liq = (tau_liq == steps + 1) & (cash <= 0.0)
                    new_ins = (tau_ins == steps + 1) & (a - liabilities <= 0.0)
                    tau_liq[new_liq] = t
                    tau_ins[new_ins] = t

                first_liq = tau_liq < tau_ins
                first_ins = tau_ins < tau_liq
                joint = (tau_liq == tau_ins) & (tau_liq <= steps)
                liq_without_ins = (tau_liq <= steps) & (tau_ins == steps + 1)
                ins_without_liq = (tau_ins <= steps) & (tau_liq == steps + 1)
                no_default = (tau_liq == steps + 1) & (tau_ins == steps + 1)

                rows.append(
                    DefaultSummary(
                        leverage=leverage,
                        cash0=cash0,
                        rho=rho,
                        first_liq=float(np.mean(first_liq)),
                        first_ins=float(np.mean(first_ins)),
                        joint=float(np.mean(joint)),
                        liq_without_ins=float(np.mean(liq_without_ins)),
                        ins_without_liq=float(np.mean(ins_without_liq)),
                        no_default=float(np.mean(no_default)),
                    )
                )
    return rows


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        curr = [i]
        for j, cb in enumerate(b, 1):
            curr.append(
                min(
                    prev[j] + 1,
                    curr[j - 1] + 1,
                    prev[j - 1] + (ca != cb),
                )
            )
        prev = curr
    return prev[-1]


def transfer_choice() -> tuple[str, list[tuple[str, int]]]:
    node_test = (
        "Simulate asset value, liabilities, and cash; classify default by "
        "two barriers: cash <= 0 and asset - liabilities <= 0."
    )
    attempts = {
        "rank_one_schur": (
            "Sample positive bulk matrix A, boundary coupling b, and reserve r; "
            "classify extension failure by two barriers: min_eig(A) < 0 and "
            "r - b^T A^{-1} b < 0."
        ),
        "shifted_hankel": (
            "Sample reciprocal moment sequence T_k; classify failure by two "
            "shifted Hankel barriers H0 not PSD and H1 not PSD."
        ),
        "contour_delay": (
            "Sample windows R and compare economic contour crossing with legally "
            "recognized D2 crossing after delayed certification."
        ),
    }
    scores = [(name, levenshtein(node_test, text)) for name, text in attempts.items()]
    scores.sort(key=lambda item: item[1])
    return scores[0][0], scores


def random_spd(rng: np.random.Generator, n: int) -> np.ndarray:
    x = rng.standard_normal((n, n))
    return x.T @ x + 0.25 * np.eye(n)


def inertia(matrix: np.ndarray, tol: float = 1e-10) -> tuple[int, int, int, np.ndarray]:
    eig = np.linalg.eigvalsh(matrix)
    return (
        int(np.sum(eig < -tol)),
        int(np.sum(np.abs(eig) <= tol)),
        int(np.sum(eig > tol)),
        eig,
    )


def block_matrix(a: np.ndarray, b: np.ndarray, r: float) -> np.ndarray:
    top = np.column_stack([a, b])
    bottom = np.concatenate([b, [r]])[None, :]
    return np.vstack([top, bottom])


def hankel_pair(m: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    h0 = np.array([[m[0], m[1]], [m[1], m[2]]], dtype=float)
    h1 = np.array([[m[1], m[2]], [m[2], m[3]]], dtype=float)
    return h0, h1


def hankel_block(m: np.ndarray, shift: int, d: int) -> np.ndarray:
    return np.array([[m[i + j + shift] for j in range(d + 1)] for i in range(d + 1)], dtype=float)


def shifted_hankel_boundary_experiment() -> dict[str, object]:
    examples = []
    static_cases = {
        "H0_pass_H1_fail": np.array([1.0, 0.0, 1.0, 0.0]),
        "H1_pass_H0_fail": np.array([0.0, 1.0, 0.0, 1.0]),
    }
    for name, m in static_cases.items():
        h0, h1 = hankel_pair(m)
        examples.append(
            {
                "name": name,
                "m": m.tolist(),
                "H0": h0.tolist(),
                "H1": h1.tolist(),
                "H0_inertia": inertia(h0)[:3],
                "H1_inertia": inertia(h1)[:3],
            }
        )

    boundary_cases = []
    for eps in (-1e-4, 0.0, 1e-4):
        m_h0 = np.array([1.0, 1.0, 1.0 + eps, 2.0])
        h0, h1 = hankel_pair(m_h0)
        boundary_cases.append(
            {
                "family": "H0_det_boundary_H1_still_positive",
                "epsilon": eps,
                "m": m_h0.tolist(),
                "det_H0": float(np.linalg.det(h0)),
                "det_H1": float(np.linalg.det(h1)),
                "H0_inertia": inertia(h0)[:3],
                "H1_inertia": inertia(h1)[:3],
            }
        )

        m_h1 = np.array([2.0, 1.0, 1.0, 1.0 + eps])
        h0, h1 = hankel_pair(m_h1)
        boundary_cases.append(
            {
                "family": "H1_det_boundary_H0_still_positive",
                "epsilon": eps,
                "m": m_h1.tolist(),
                "det_H0": float(np.linalg.det(h0)),
                "det_H1": float(np.linalg.det(h1)),
                "H0_inertia": inertia(h0)[:3],
                "H1_inertia": inertia(h1)[:3],
            }
        )

    all_order = []
    max_d = 8
    even_moments = np.array([1.0 if n % 2 == 0 else 0.0 for n in range(2 * max_d + 3)])
    shifted_even_moments = np.empty_like(even_moments)
    shifted_even_moments[0] = 0.0
    shifted_even_moments[1:] = even_moments[:-1]
    for d in range(1, max_d + 1):
        h0_even = hankel_block(even_moments, 0, d)
        h1_even = hankel_block(even_moments, 1, d)
        h0_shift = hankel_block(shifted_even_moments, 0, d)
        h1_shift = hankel_block(shifted_even_moments, 1, d)
        all_order.append(
            {
                "d": d,
                "even_moments_H0_inertia": inertia(h0_even)[:3],
                "even_moments_H1_inertia": inertia(h1_even)[:3],
                "shifted_even_H0_inertia": inertia(h0_shift)[:3],
                "shifted_even_H1_inertia": inertia(h1_shift)[:3],
            }
        )

    return {
        "examples": examples,
        "boundary_cases": boundary_cases,
        "all_order": all_order,
    }


def schur_boundary_experiment(
    *,
    n_trials: int = 500,
    n: int = 5,
    seed: int = 20260622,
) -> dict[str, object]:
    rng = np.random.default_rng(seed)
    epsilons = (-1e-4, -1e-6, 0.0, 1e-6, 1e-4)
    mismatches = 0
    boundary_cases = []
    flip_examples = []

    for trial in range(n_trials):
        a = random_spd(rng, n)
        b = rng.standard_normal(n)
        threshold = float(b @ np.linalg.solve(a, b))
        for eps in epsilons:
            q = block_matrix(a, b, threshold + eps)
            neg, zero, pos, eig = inertia(q)
            expected = (1, 0, n) if eps < 0 else (0, 1, n) if eps == 0.0 else (0, 0, n + 1)
            if (neg, zero, pos) != expected:
                mismatches += 1
            if trial < 3:
                boundary_cases.append(
                    {
                        "trial": trial,
                        "epsilon": eps,
                        "schur_reserve": eps,
                        "inertia": (neg, zero, pos),
                        "min_eigenvalue": float(eig[0]),
                    }
                )

        if trial < 3:
            q_bad = block_matrix(a, b, threshold - 1e-3)
            q_good = block_matrix(a, b, threshold + 1e-3)
            flip_examples.append(
                {
                    "trial": trial,
                    "bulk_min_eig": float(np.linalg.eigvalsh(a)[0]),
                    "same_threshold": threshold,
                    "bad_inertia": inertia(q_bad)[:3],
                    "good_inertia": inertia(q_good)[:3],
                }
            )

    return {
        "trials": n_trials,
        "bulk_dimension": n,
        "epsilons": epsilons,
        "mismatches": mismatches,
        "boundary_cases": boundary_cases,
        "flip_examples": flip_examples,
    }


def print_default_summary(rows: Iterable[DefaultSummary]) -> None:
    print("NODE experiment: liquidity default versus balance-sheet insolvency")
    print("lev cash rho | first_liq first_ins joint | liq_no_ins ins_no_liq no_default")
    for row in rows:
        if max(row.liq_without_ins, row.ins_without_liq, row.joint) < 0.02:
            continue
        print(
            f"{row.leverage:0.2f} {row.cash0:4.1f} {row.rho:4.1f} | "
            f"{row.first_liq:8.3f} {row.first_ins:8.3f} {row.joint:5.3f} | "
            f"{row.liq_without_ins:10.3f} {row.ins_without_liq:10.3f} "
            f"{row.no_default:10.3f}"
        )


def main() -> None:
    rows = simulate_default_grid()
    print_default_summary(rows)

    chosen, scores = transfer_choice()
    print()
    print("Step 8 transfer attempts by Levenshtein distance")
    for name, score in scores:
        print(f"{name}: {score}")
    print(f"chosen_transfer: {chosen}")

    hankel = shifted_hankel_boundary_experiment()
    print()
    print("Workflow-selected transferred shifted-Hankel experiment")
    print("independence examples:")
    for item in hankel["examples"]:
        print(item)
    print("boundary cases:")
    for item in hankel["boundary_cases"]:
        print(item)
    print("all-order witness check through d=8:")
    for item in hankel["all_order"]:
        print(item)

    result = schur_boundary_experiment()
    print()
    print("Secondary rank-one boundary-extension experiment")
    print(f"trials: {result['trials']}")
    print(f"bulk_dimension: {result['bulk_dimension']}")
    print(f"epsilons: {result['epsilons']}")
    print(f"mismatches_against_schur_inertia: {result['mismatches']}")
    print("boundary_cases:")
    for item in result["boundary_cases"]:
        print(item)
    print("same-bulk flip examples:")
    for item in result["flip_examples"]:
        print(item)

    print()
    print("Interpretation:")
    print(
        "Liquidity and insolvency separate in the NODE: cash-default paths and "
        "net-worth-default paths occur without forcing each other. The workflow-"
        "selected shifted-Hankel transfer has the same two-barrier structure: "
        "H0 and H1 are independent at the first nontrivial truncation, and each "
        "can cross its PSD boundary while the other remains positive. Therefore "
        "the proof route cannot drop either shifted square-test condition. The "
        "secondary rank-one check gives the corresponding boundary-extension "
        "version: positive bulk does not determine the completed index; the "
        "missing datum is sigma = r - b^T A^{-1} b."
    )


if __name__ == "__main__":
    main()
