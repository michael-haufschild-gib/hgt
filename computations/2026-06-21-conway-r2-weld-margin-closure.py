#!/usr/bin/env python3
"""Run-2 finding 53 candidate: margin-closure passport for the native weld."""

from __future__ import annotations

import numpy as np


def node_margin_feedback(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    n = 600
    leverage = rng.lognormal(mean=1.1, sigma=0.35, size=n)
    collateral = rng.uniform(0.85, 1.15, size=n)
    exposure = leverage * collateral

    def step(price: float, shock: float) -> tuple[float, float]:
        collateral_value = collateral * price
        equity = collateral_value - exposure / leverage
        margin_gap = np.maximum(0.0, exposure * shock - equity)
        forced_sale = float(np.sum(margin_gap)) / n
        next_price = max(0.05, price - 0.18 * forced_sale)
        return next_price, forced_sale

    print("NODE: forced selling lowers collateral, raises leverage, and creates larger margin calls")
    print("shock first_forced_sale final_forced_sale price_after_1 price_final amplification")
    for shock in [0.04, 0.07, 0.10, 0.13]:
        price = 1.0 - shock
        price1, sale1 = step(price, shock)
        last_sale = sale1
        for _ in range(12):
            price, last_sale = step(price1, shock)
            price1 = price
        amp = last_sale / (sale1 + 1e-12)
        print(
            f"{shock:.2f} {sale1:.5f} {last_sale:.5f} "
            f"{1.0 - shock:.4f} {price:.4f} {amp:.2f}"
        )
    print("constraint: a one-shot margin pass is false unless it has reserve under the feedback closure")


def commutator_defect(load: float) -> float:
    a = np.array([[0.0, 1.0], [-1.0, 0.0]])
    p = np.array([[1.0 + load, 0.0], [0.0, 1.0 - load]])
    ref = np.array([[0.0, -2.0], [-2.0, 0.0]])
    return float(np.linalg.norm(a @ p - p @ a, ord="fro") / np.linalg.norm(ref, ord="fro"))


def close_load(load: float, coupling: float) -> float:
    # Margin-call style closure: small loads move little; near-boundary loads have
    # little reserve and are amplified by the endogenous recalculation.
    return min(4.0, load + coupling * load * load / max(0.04, 1.0 - load))


def transfer_weld_closure(seed: int = 20260622) -> None:
    rng = np.random.default_rng(seed)
    loads = np.r_[rng.uniform(0.08, 0.38, 52), rng.uniform(0.70, 0.94, 8)]
    threshold = 1.0

    print()
    print("TRANSFER: ResearchNode #21 native weld category M+")
    print("method #20 name the missing lemma: fiberwise compatibility needs closure reserve")
    print("coupling initial_pass_rate initial_max closed_pass_rate closed_max crossed_count reserve_min")
    for coupling in [0.05, 0.10, 0.16, 0.22, 0.30]:
        closed = loads.copy()
        for _ in range(5):
            closed = np.array([close_load(float(x), coupling) for x in closed])
        initial_defects = np.array([commutator_defect(float(x)) for x in loads])
        closed_defects = np.array([commutator_defect(float(x)) for x in closed])
        print(
            f"{coupling:.2f} "
            f"{float(np.mean(initial_defects < threshold)):.3f} {float(np.max(initial_defects)):.3f} "
            f"{float(np.mean(closed_defects < threshold)):.3f} {float(np.max(closed_defects)):.3f} "
            f"{int(np.sum((initial_defects < threshold) & (closed_defects >= threshold)))} "
            f"{float(np.min(threshold - initial_defects)):.3f}"
        )
    print()
    print("GATE SUMMARY")
    print(
        "objectwise Gamma/prime commutator bounds are not enough unless the fibers carry "
        "compatibility reserve under the induced closure"
    )
    print(
        "missing lemma: closed-fiber compatibility, a naturality-square pass plus an "
        "endogenous-update bound implying all iterated squares stay below threshold"
    )


def main() -> None:
    node_margin_feedback()
    transfer_weld_closure()


if __name__ == "__main__":
    main()
