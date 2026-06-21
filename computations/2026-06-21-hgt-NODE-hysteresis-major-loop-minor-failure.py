#!/usr/bin/env python3
"""THE-MACHINE NODE test: major-loop hysteresis fits fail on minor loops.

NODE:
    Models fitted only to the major loop can fail badly under partial cycling
    or reversal.

Constraint tested:
    The major loop is a boundary trace of a memory operator. It does not
    determine nested minor-loop behavior unless the hidden hysteron/memory
    distribution is modeled.
"""

from __future__ import annotations

import numpy as np


def make_hysterons(n: int = 1200, seed: int = 20260621) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    rng = np.random.default_rng(seed)
    centers = rng.normal(0.0, 0.45, n)
    widths = rng.gamma(shape=2.0, scale=0.09, size=n) + 0.03
    alpha = centers + widths
    beta = centers - widths
    weights = rng.lognormal(mean=0.0, sigma=0.35, size=n)
    weights /= weights.sum()
    return alpha, beta, weights


def run_preisach(protocol: np.ndarray, alpha: np.ndarray, beta: np.ndarray, weights: np.ndarray, start: int = -1) -> np.ndarray:
    states = np.full(alpha.shape, start, dtype=int)
    out = []
    for h in protocol:
        states[h >= alpha] = 1
        states[h <= beta] = -1
        out.append(float(np.dot(weights, states)))
    return np.asarray(out)


def interpolate_branch(x: np.ndarray, h_branch: np.ndarray, y_branch: np.ndarray) -> np.ndarray:
    order = np.argsort(h_branch)
    return np.interp(x, h_branch[order], y_branch[order])


def major_loop_predict(protocol: np.ndarray, h_up: np.ndarray, y_up: np.ndarray, h_down: np.ndarray, y_down: np.ndarray) -> np.ndarray:
    pred = []
    prev = protocol[0]
    for h in protocol:
        if h >= prev:
            pred.append(float(interpolate_branch(np.array([h]), h_up, y_up)[0]))
        else:
            pred.append(float(interpolate_branch(np.array([h]), h_down, y_down)[0]))
        prev = h
    return np.asarray(pred)


def rmse(a: np.ndarray, b: np.ndarray) -> float:
    return float(np.sqrt(np.mean((a - b) ** 2)))


def main() -> None:
    alpha, beta, weights = make_hysterons()
    up = np.linspace(-1.5, 1.5, 301)
    down = np.linspace(1.5, -1.5, 301)
    major_protocol = np.concatenate([up, down[1:]])
    major_true = run_preisach(major_protocol, alpha, beta, weights)
    h_up = major_protocol[: len(up)]
    y_up = major_true[: len(up)]
    h_down = major_protocol[len(up) - 1 :]
    y_down = major_true[len(up) - 1 :]
    major_pred = major_loop_predict(major_protocol, h_up, y_up, h_down, y_down)

    protocols = {
        "minor_high_reversal": np.concatenate([
            np.linspace(-1.5, 1.1, 180),
            np.linspace(1.1, -0.15, 120),
            np.linspace(-0.15, 0.85, 100),
        ]),
        "minor_mid_reversal": np.concatenate([
            np.linspace(-1.5, 0.45, 150),
            np.linspace(0.45, -0.55, 120),
            np.linspace(-0.55, 0.20, 90),
        ]),
        "nested_training": np.concatenate([
            np.linspace(-1.5, 1.2, 150),
            np.linspace(1.2, -0.4, 100),
            np.linspace(-0.4, 0.7, 80),
            np.linspace(0.7, -0.1, 70),
        ]),
    }

    print("NODE: major-loop fit failure under partial cycling/reversal")
    print(f"hysterons={len(alpha)}")
    print(f"major_loop_rmse={rmse(major_true, major_pred):.8f}")
    print("protocol true_range pred_range rmse max_abs_error loop_area_true loop_area_pred")
    for name, protocol in protocols.items():
        true = run_preisach(protocol, alpha, beta, weights)
        pred = major_loop_predict(protocol, h_up, y_up, h_down, y_down)
        loop_area_true = float(np.trapz(true, protocol))
        loop_area_pred = float(np.trapz(pred, protocol))
        print(
            f"{name:20s} {true.min():.6f},{true.max():.6f} "
            f"{pred.min():.6f},{pred.max():.6f} {rmse(true, pred):.6f} "
            f"{np.max(np.abs(true - pred)):.6f} {loop_area_true:.6f} {loop_area_pred:.6f}"
        )

    print(
        "\nInterpretation: the major-loop-only predictor has essentially zero "
        "training error on the major branch but fails on partial reversals. The "
        "missing constraint is hidden memory state, not a better static curve fit."
    )


if __name__ == "__main__":
    main()
