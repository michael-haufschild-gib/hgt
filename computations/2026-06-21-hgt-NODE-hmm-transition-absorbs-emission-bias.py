#!/usr/bin/env python3
"""NODE test: HMM transition estimates absorb systematic observation bias."""

import argparse

import numpy as np


def simulate(n, trans, emit, rng):
    x = np.zeros(n, dtype=int)
    y = np.zeros(n, dtype=int)
    x[0] = rng.integers(0, 2)
    y[0] = rng.random() < emit[x[0], 1]
    for i in range(1, n):
        x[i] = rng.random() >= trans[x[i - 1], 0]
        y[i] = rng.random() < emit[x[i], 1]
    return x, y


def forward_loglik(y, trans, emit):
    alpha = np.array([0.5, 0.5]) * emit[:, y[0]]
    scale = float(alpha.sum())
    if scale <= 0:
        return -1e300
    loglik = np.log(scale)
    alpha /= scale
    for obs in y[1:]:
        alpha = alpha @ trans
        alpha *= emit[:, obs]
        scale = float(alpha.sum())
        if scale <= 0:
            return -1e300
        loglik += np.log(scale)
        alpha /= scale
    return float(loglik)


def grid_fit(y, emit_assumed, grid_size):
    best = (-1e300, None)
    for p01 in np.linspace(0.01, 0.35, grid_size):
        for p10 in np.linspace(0.01, 0.35, grid_size):
            trans = np.array([[1 - p01, p01], [p10, 1 - p10]])
            ll = forward_loglik(y, trans, emit_assumed)
            if ll > best[0]:
                best = (ll, (p01, p10))
    return best


def naive_observed_transition(y):
    counts = np.ones((2, 2))
    for a, b in zip(y[:-1], y[1:]):
        counts[a, b] += 1.0
    return counts / counts.sum(axis=1, keepdims=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=1800)
    parser.add_argument("--grid-size", type=int, default=29)
    parser.add_argument("--reps", type=int, default=4)
    parser.add_argument("--seed", type=int, default=20260621)
    args = parser.parse_args()
    rng = np.random.default_rng(args.seed)

    true_trans = np.array([[0.94, 0.06], [0.10, 0.90]])
    true_emit = np.array([[0.94, 0.06], [0.18, 0.82]])
    symmetric_emit = np.array([[0.90, 0.10], [0.10, 0.90]])
    too_clean_emit = np.array([[0.98, 0.02], [0.02, 0.98]])
    too_noisy_emit = np.array([[0.75, 0.25], [0.25, 0.75]])

    x, y = simulate(args.n, true_trans, true_emit, rng)
    true_p01, true_p10 = true_trans[0, 1], true_trans[1, 0]
    print("NODE: HMM transition estimates absorb systematic observation bias")
    print(f"true transition p01={true_p01:.4f} p10={true_p10:.4f}; true_emit={true_emit.tolist()}")
    naive = naive_observed_transition(y)
    print(f"naive observed transitions p01={naive[0,1]:.4f} p10={naive[1,0]:.4f}")
    for name, emit in [
        ("correct", true_emit),
        ("symmetric", symmetric_emit),
        ("too_clean", too_clean_emit),
        ("too_noisy", too_noisy_emit),
    ]:
        ll, (p01, p10) = grid_fit(y, emit, args.grid_size)
        print(
            f"fit emission={name:9s} p01_hat={p01:.4f} p10_hat={p10:.4f} "
            f"bias01={p01-true_p01:+.4f} bias10={p10-true_p10:+.4f} loglik={ll:.2f}"
        )

    print("\nReplicate stress")
    for fp1 in [0.02, 0.10, 0.22, 0.34]:
        emit = np.array([[1 - fp1, fp1], [0.18, 0.82]])
        biases = []
        for rep in range(args.reps):
            _, yy = simulate(args.n, true_trans, true_emit, rng)
            _, (p01, p10) = grid_fit(yy, emit, args.grid_size)
            biases.append((p01 - true_p01, p10 - true_p10))
        arr = np.array(biases)
        print(
            f"assumed_false_positive={fp1:.2f}: mean_bias01={arr[:,0].mean():+.4f} "
            f"mean_bias10={arr[:,1].mean():+.4f} sd01={arr[:,0].std():.4f} sd10={arr[:,1].std():.4f}"
        )


if __name__ == "__main__":
    main()
