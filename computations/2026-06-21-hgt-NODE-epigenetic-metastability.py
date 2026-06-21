#!/usr/bin/env python3
"""THE-MACHINE NODE test: epigenetic states are metastable, not locked.

NODE:
    Epigenetic states can be metastable rather than permanently locked.

Constraint:
    A switched state may have a long lifetime and look fixed in short assays,
    but it has a nonzero escape/reversion rate. The defining test is not
    whether the state persists for a while, but whether survival decays with
    longer observation or after removing maintenance feedback.
"""

from __future__ import annotations

import math

import numpy as np


def simulate_two_state(
    rng: np.random.Generator,
    n: int,
    steps: int,
    p_on_to_off: float,
    p_off_to_on: float,
    init_on: float,
) -> np.ndarray:
    state = rng.random(n) < init_on
    history = np.empty((steps + 1, n), dtype=bool)
    history[0] = state
    for t in range(1, steps + 1):
        u = rng.random(n)
        off_events = state & (u < p_on_to_off)
        on_events = (~state) & (u < p_off_to_on)
        state = (state & ~off_events) | on_events
        history[t] = state
    return history


def survival_curve(history: np.ndarray) -> np.ndarray:
    initially_on = history[0]
    if not np.any(initially_on):
        return np.zeros(history.shape[0])
    return np.mean(history[:, initially_on], axis=1)


def first_escape_times(history: np.ndarray) -> np.ndarray:
    initially_on = np.where(history[0])[0]
    out = []
    for idx in initially_on:
        off = np.where(~history[:, idx])[0]
        out.append(int(off[0]) if len(off) else history.shape[0])
    return np.asarray(out, dtype=int)


def summarize_case(label: str, p_loss: float, p_gain: float, init_on: float, steps: int, rng: np.random.Generator) -> None:
    hist = simulate_two_state(rng, n=50_000, steps=steps, p_on_to_off=p_loss, p_off_to_on=p_gain, init_on=init_on)
    surv = survival_curve(hist)
    escapes = first_escape_times(hist)
    short_looks_locked = float(surv[20])
    long_survival = float(surv[-1])
    median_escape = float(np.median(escapes))
    q90_escape = float(np.quantile(escapes, 0.90))
    nonescape_frac = float(np.mean(escapes >= steps))
    print(
        f"{label:18s} p_loss={p_loss:.5f} p_gain={p_gain:.5f} "
        f"surv20={short_looks_locked:.4f} surv_end={long_survival:.4f} "
        f"median_escape={median_escape:.1f} q90_escape={q90_escape:.1f} "
        f"not_escaped_by_end={nonescape_frac:.4f}"
    )


def barrier_sweep(rng: np.random.Generator) -> None:
    print("\nBarrier/maintenance sweep")
    print("barrier p_loss expected_lifetime observed_median_escape surv100")
    for barrier in [2.0, 3.0, 4.0, 5.0, 6.0]:
        p_loss = 0.08 * math.exp(-barrier)
        hist = simulate_two_state(rng, n=30_000, steps=160, p_on_to_off=p_loss, p_off_to_on=0.0005, init_on=1.0)
        escapes = first_escape_times(hist)
        print(
            f"{barrier:.1f} {p_loss:.6f} {1.0 / p_loss:.1f} "
            f"{float(np.median(escapes)):.1f} {float(survival_curve(hist)[100]):.4f}"
        )


def main() -> None:
    rng = np.random.default_rng(26062118)
    print("NODE validation: epigenetic switched states can be metastable, not permanently locked")
    print("case p_loss p_gain surv20 surv_end median_escape q90_escape not_escaped_by_end")
    summarize_case("permanent_lock", p_loss=0.0, p_gain=0.0, init_on=1.0, steps=240, rng=rng)
    summarize_case("metastable_slow", p_loss=0.006, p_gain=0.0005, init_on=1.0, steps=240, rng=rng)
    summarize_case("washout_feedback", p_loss=0.035, p_gain=0.0000, init_on=1.0, steps=240, rng=rng)
    summarize_case("plastic_state", p_loss=0.045, p_gain=0.0200, init_on=1.0, steps=240, rng=rng)
    barrier_sweep(rng)
    print(
        "\nRead: metastable states can look locked over short assays but show finite "
        "escape on long horizons or after maintenance washout. Barrier height tunes "
        "lifetime continuously; permanent locking is the singular p_loss=0 case."
    )


if __name__ == "__main__":
    main()
