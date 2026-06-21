#!/usr/bin/env python3
"""
Attempt 4 NODE experiment.

NODE: non-equivalence of time and ensemble averages on finite observation
windows in an ergodic-trap setting.

Constraint tested:
  Ergodicity identifies time and ensemble averages only in the infinite-time
  limit.  A finite trajectory can remain biased by a metastable component even
  when the stationary ensemble mean is already well defined.
"""

from __future__ import annotations

import numpy as np


def transition_matrix(epsilon: float) -> np.ndarray:
    """Four-state chain: two sticky components connected by rare jumps."""
    return np.array(
        [
            [0.93 - epsilon, 0.07, epsilon, 0.00],
            [0.07, 0.93 - epsilon, 0.00, epsilon],
            [epsilon, 0.00, 0.93 - epsilon, 0.07],
            [0.00, epsilon, 0.07, 0.93 - epsilon],
        ],
        dtype=float,
    )


def stationary(P: np.ndarray) -> np.ndarray:
    vals, vecs = np.linalg.eig(P.T)
    idx = int(np.argmin(np.abs(vals - 1)))
    v = np.real(vecs[:, idx])
    v = np.maximum(v, 0)
    return v / np.sum(v)


def simulate(P: np.ndarray, observable: np.ndarray, horizon: int, n_paths: int, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    states = np.zeros(n_paths, dtype=int)
    sums = np.zeros(n_paths)
    cdf = np.cumsum(P, axis=1)
    for _ in range(horizon):
        sums += observable[states]
        draws = rng.random(n_paths)
        states = np.array([np.searchsorted(cdf[s], u) for s, u in zip(states, draws)], dtype=int)
    return sums / horizon


def first_exit_times(P: np.ndarray, n_paths: int, max_steps: int, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    states = np.zeros(n_paths, dtype=int)
    cdf = np.cumsum(P, axis=1)
    exits = np.full(n_paths, max_steps, dtype=int)
    active = np.ones(n_paths, dtype=bool)
    for t in range(1, max_steps + 1):
        idxs = np.flatnonzero(active)
        if len(idxs) == 0:
            break
        draws = rng.random(len(idxs))
        new_states = np.array([np.searchsorted(cdf[states[i]], u) for i, u in zip(idxs, draws)], dtype=int)
        states[idxs] = new_states
        escaped = active & (states >= 2)
        exits[escaped] = t
        active[escaped] = False
    return exits


def summarize(epsilon: float, horizons: list[int]) -> None:
    P = transition_matrix(epsilon)
    obs = np.array([-1.0, -1.0, 1.0, 1.0])
    pi = stationary(P)
    ensemble = float(pi @ obs)
    second = sorted(np.linalg.eigvals(P), key=lambda z: abs(z), reverse=True)[1]
    gap = 1 - abs(second)
    print(f"epsilon={epsilon:g}")
    print(f"  stationary ensemble mean={ensemble:+.6f}")
    print(f"  spectral gap={gap:.6g}; mixing scale~{1/gap:.1f}")
    exits = first_exit_times(P, n_paths=5000, max_steps=20000, seed=123)
    print(f"  median first exit from initial component={np.median(exits):.0f}")
    for T in horizons:
        avgs = simulate(P, obs, horizon=T, n_paths=5000, seed=100 + T)
        print(
            f"  T={T:5d}: mean(time avg)={np.mean(avgs):+.4f}, "
            f"std={np.std(avgs):.4f}, "
            f"P(|avg-ensemble|>0.5)={np.mean(np.abs(avgs - ensemble) > 0.5):.3f}"
        )
    print()


def main() -> None:
    print("FINITE-WINDOW TIME AVERAGE VS ENSEMBLE AVERAGE")
    print("initial state is in the negative component; stationary ensemble is symmetric")
    print()
    summarize(epsilon=0.02, horizons=[25, 100, 500, 2000])
    summarize(epsilon=0.002, horizons=[25, 100, 500, 2000])


if __name__ == "__main__":
    main()
