#!/usr/bin/env python3
"""Workflow pass: feedback lock-in as a kill test for prime-built flows."""

from __future__ import annotations

import math

import mpmath as mp
import numpy as np


def node_ecosocial_feedback(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)

    def run(gamma: float, reverse_at: int = 80, steps: int = 180) -> tuple[float, float, float]:
        x = 0.18  # degraded ecological fraction
        y = 0.0  # social/economic lock-in to degraded practice
        for t in range(steps):
            stress = 0.78 if t < reverse_at else 0.18
            growth = stress + gamma * y - 0.55
            x = np.clip(x + 0.095 * x * (1.0 - x) * growth + rng.normal(0.0, 0.002), 0.0, 1.0)
            y = np.clip(y + 0.08 * (x - y), 0.0, 1.0)
        return float(x), float(y), float(stress)

    print("NODE: social/economic feedbacks can reinforce ecological degradation")
    print("gamma final_degraded final_lockin verdict")
    for gamma in [0.0, 0.8, 1.6, 2.4, 3.2, 4.0]:
        x, y, _ = run(gamma)
        verdict = "locked" if x > 0.5 else "recovered"
        print(f"{gamma:.1f} {x:.3f} {y:.3f} {verdict}")
    print("constraint: reversing the ecological driver is insufficient after feedback lock-in crosses a boundary")


def first_primes(n: int) -> np.ndarray:
    primes: list[int] = []
    candidate = 2
    while len(primes) < n:
        ok = True
        for p in primes:
            if p * p > candidate:
                break
            if candidate % p == 0:
                ok = False
                break
        if ok:
            primes.append(candidate)
        candidate += 1 if candidate == 2 else 2
    return np.asarray(primes, dtype=float)


def zero_ordinates(n: int) -> np.ndarray:
    vals = []
    for k in range(1, n + 1):
        vals.append(float(mp.im(mp.zetazero(k))))
    return np.asarray(vals)


def reversible_generator(logp: np.ndarray, sigma: float, beta: float, ell: float) -> tuple[np.ndarray, np.ndarray]:
    n = len(logp)
    base = np.exp(-sigma * logp)
    # Feedback rewards already dominant low-prime lanes; this is a monotone lock-in proxy.
    feedback = np.exp(beta * (base / base.max()))
    pi = base * feedback
    pi = pi / pi.sum()
    q = np.zeros((n, n), dtype=float)
    for i in range(n):
        for j in range(i + 1, n):
            conductance = math.exp(-abs(logp[i] - logp[j]) / ell) * math.sqrt(pi[i] * pi[j])
            q[i, j] = conductance / pi[i]
            q[j, i] = conductance / pi[j]
    q[np.diag_indices(n)] = -q.sum(axis=1)
    return q, pi


def entropy(pi: np.ndarray) -> float:
    p = pi[pi > 0]
    return float(-np.sum(p * np.log(p)) / math.log(len(pi)))


def affine_mse(x: np.ndarray, y: np.ndarray) -> float:
    a, b = np.polyfit(x, y, 1)
    fit = a * x + b
    scale = max(1e-12, float(np.std(y)))
    return float(np.mean(((fit - y) / scale) ** 2))


def spacing_mse(x: np.ndarray, y: np.ndarray) -> float:
    dx = np.diff(np.sort(x))
    dy = np.diff(np.sort(y))
    dx = (dx - dx.mean()) / max(dx.std(), 1e-12)
    dy = (dy - dy.mean()) / max(dy.std(), 1e-12)
    return float(np.mean((dx - dy) ** 2))


def transfer_prime_flow() -> None:
    print()
    print("TRANSFER: ResearchNode #1/#16 Conjecture E, scoped no prime-built generative flow")
    print(
        "method #23 classify boundary cases: positive/reversible prime-lane feedback may stabilize an internal regime; "
        "test whether it improves or worsens zero-spectral fit"
    )
    n = 42
    logp = np.log(first_primes(n))
    zeros = zero_ordinates(n - 1)
    print("sigma beta entropy spectral_gap affine_zero_mse spacing_mse lockin_score")
    rows = []
    for sigma in [0.3, 0.5, 0.8, 1.1]:
        for beta in [0.0, 1.0, 2.0, 4.0, 7.0, 10.0]:
            q, pi = reversible_generator(logp, sigma=sigma, beta=beta, ell=0.85)
            eig = np.sort(-np.linalg.eigvals(q).real)
            eig = eig[eig > 1e-9][: n - 1]
            gap = float(eig[0]) if len(eig) else 0.0
            a_mse = affine_mse(eig, zeros[: len(eig)])
            s_mse = spacing_mse(eig, zeros[: len(eig)])
            lock = float(pi.max() / np.median(pi))
            rows.append((sigma, beta, entropy(pi), gap, a_mse, s_mse, lock))
            print(f"{sigma:.1f} {beta:04.1f} {entropy(pi):.3f} {gap:.4e} {a_mse:.3f} {s_mse:.3f} {lock:.2f}")

    print()
    print("BOUNDARY SUMMARY")
    for sigma in [0.3, 0.5, 0.8, 1.1]:
        subset = [r for r in rows if abs(r[0] - sigma) < 1e-9]
        best_zero = min(subset, key=lambda r: r[4])
        strongest_lock = max(subset, key=lambda r: r[6])
        print(
            f"sigma={sigma:.1f}",
            f"best_zero_beta={best_zero[1]:.1f}",
            f"best_zero_mse={best_zero[4]:.3f}",
            f"strongest_lock_beta={strongest_lock[1]:.1f}",
            f"strongest_lock_mse={strongest_lock[4]:.3f}",
            f"strongest_lock_entropy={strongest_lock[2]:.3f}",
        )


def main() -> None:
    node_ecosocial_feedback()
    transfer_prime_flow()


if __name__ == "__main__":
    main()
