#!/usr/bin/env python3
"""Clean GPT-topic finding 53 candidate: observation-action gatekeeper coupling."""

from __future__ import annotations

import numpy as np


def node_symptom_detection_behavior(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    n = 6000
    symptomatic = rng.random(n) < 0.45
    base_contacts = rng.negative_binomial(3, 0.45, size=n) + 1
    infectivity = rng.gamma(shape=1.7, scale=0.55, size=n)
    detection_p = np.where(symptomatic, 0.82, 0.18)

    print("NODE: symptom status affects detectability and behavior")
    print("behavior_reduction true_R detected_R hidden_R detected_fraction")
    for reduction in [0.0, 0.25, 0.50, 0.75]:
        contacts = base_contacts.astype(float)
        contacts[symptomatic] *= 1.0 - reduction
        secondary = contacts * infectivity
        detected = rng.random(n) < detection_p
        print(
            f"{reduction:.2f} {float(np.mean(secondary)):.3f} "
            f"{float(np.mean(secondary[detected])):.3f} "
            f"{float(np.mean(secondary[~detected])):.3f} "
            f"{float(np.mean(detected)):.3f}"
        )
    print("constraint: observation is not passive when visibility is coupled to behavior")


def simulate_events(
    rng: np.random.Generator,
    steps: int,
    lanes: int,
    response_strength: float,
    passive: bool,
) -> np.ndarray:
    state = np.zeros((steps, lanes), dtype=bool)
    latent_pressure = rng.uniform(0.06, 0.11, size=lanes)
    cooldown = np.zeros(lanes, dtype=float)
    for t in range(1, steps):
        cluster_push = 0.22 * state[t - 1].astype(float)
        prob = latent_pressure + cluster_push
        if not passive:
            prob *= 1.0 - cooldown
            cooldown *= 0.55
        state[t] = rng.random(lanes) < np.clip(prob, 0.0, 0.95)
        if not passive:
            cooldown = np.maximum(cooldown, response_strength * state[t].astype(float))
    return state


def persistence_metrics(events: np.ndarray) -> tuple[float, float, float]:
    x = events[:-1].astype(float)
    y = events[1:].astype(float)
    same_lane = float(np.mean(y[x.astype(bool)])) if np.any(x) else 0.0
    base = float(np.mean(y))
    lag_gap = same_lane - base

    runs = []
    for lane in range(events.shape[1]):
        current = 0
        for bit in events[:, lane]:
            if bit:
                current += 1
            elif current:
                runs.append(current)
                current = 0
        if current:
            runs.append(current)
    mean_run = float(np.mean(runs)) if runs else 0.0

    a = np.c_[x, np.ones(len(x))]
    coef, *_ = np.linalg.lstsq(a, y, rcond=None)
    k = coef[:-1].T
    spectral = float(np.max(np.abs(np.linalg.eigvals(k))))
    return lag_gap, mean_run, spectral


def transfer_gatekeeper_coupling(seed: int = 20260622) -> None:
    rng = np.random.default_rng(seed)
    steps = 7000
    lanes = 8
    print()
    print("TRANSFER: ResearchNode #60 gatekeeper completeness")
    print("method #13 find a monotone quantity: active-vs-passive observation gap")
    print("response passive_lag active_lag lag_gap passive_run active_run passive_spectral active_spectral")
    for response in [0.0, 0.20, 0.40, 0.65, 0.85]:
        # Reuse the same seed stream pair shape per row to keep the comparison stable.
        passive_events = simulate_events(np.random.default_rng(seed + int(response * 1000)), steps, lanes, response, True)
        active_events = simulate_events(np.random.default_rng(seed + int(response * 1000)), steps, lanes, response, False)
        p_lag, p_run, p_spec = persistence_metrics(passive_events)
        a_lag, a_run, a_spec = persistence_metrics(active_events)
        print(
            f"{response:.2f} {p_lag:.4f} {a_lag:.4f} {p_lag - a_lag:.4f} "
            f"{p_run:.3f} {a_run:.3f} {p_spec:.3f} {a_spec:.3f}"
        )
    print()
    print("GATE SUMMARY")
    print(
        "a gatekeeper can change the event process it is meant to certify; passive sampling-retention "
        "does not catch active observation-action coupling"
    )
    print(
        "report an active/passive shadow passport: run the same detector with no intervention, "
        "then sweep response strength and require the claimed invariant to be stable"
    )


def main() -> None:
    node_symptom_detection_behavior()
    transfer_gatekeeper_coupling()


if __name__ == "__main__":
    main()
