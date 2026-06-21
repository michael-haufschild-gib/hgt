#!/usr/bin/env python3
"""Workflow test for formula-node WD5 via beta-function diagnostics.

ResearchNode formula:
    [partial_s, M_p] = -log p; [partial_s, sigma_p] = 0

Random NODE:
    In renormalization and scale symmetries, the beta function diagnoses
    scale-symmetry breaking.
"""

from __future__ import annotations

import math

import numpy as np


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, start=1):
        cur = [i]
        for j, cb in enumerate(b, start=1):
            cur.append(
                min(
                    prev[j] + 1,
                    cur[-1] + 1,
                    prev[j - 1] + (ca != cb),
                )
            )
        prev = cur
    return prev[-1]


def euler_flow(beta, g0: float, steps: int = 2000, dt: float = 0.002) -> np.ndarray:
    g = g0
    out = [g]
    for _ in range(steps):
        g += dt * beta(g)
        out.append(g)
    return np.array(out)


def finite_diff_commutator(p: int, s: complex, h: float = 1e-6) -> complex:
    """Return normalized [d_s, M_p] 1 / (M_p 1)."""

    def m(z: complex) -> complex:
        return p ** (-z)

    deriv_m = (m(s + h) - m(s - h)) / (2 * h)
    return deriv_m / m(s)


def finite_diff_gauged_commutator(
    p: int, s: complex, a, h: float = 1e-6
) -> complex:
    """Normalized [d_s+a(s), M_p]1/(M_p1), with a multiplication counterterm."""

    def m(z: complex) -> complex:
        return p ** (-z)

    one = 1.0 + 0j
    left = ((m(s + h) * one - m(s - h) * one) / (2 * h)) + a(s) * m(s) * one
    right = m(s) * ((one - one) / (2 * h) + a(s) * one)
    return (left - right) / m(s)


def main() -> None:
    base_test = "compute beta(g)=dg/dlogmu and test beta=0 versus running"
    attempts = [
        (
            "A",
            "compute normalized commutator [partial_s,M_p]/M_p and test zero versus running",
        ),
        (
            "B",
            "compute finite Euler cutoff drift in zeta-prime and test cutoff stability",
        ),
        (
            "C",
            "compute scheme reparametrized beta and compare fixed point sets",
        ),
    ]
    print("STEP 8 Levenshtein transfer attempts")
    print("=" * 42)
    scored = [(tag, levenshtein(base_test, text), text) for tag, text in attempts]
    for tag, score, text in scored:
        print(f"{tag}: distance={score}, attempt={text}")
    chosen = min(scored, key=lambda row: row[1])
    print(f"chosen={chosen[0]} by minimum distance")
    print()

    print("NODE beta-function diagnostic")
    print("=" * 36)
    beta_zero = lambda g: 0.0
    beta_running = lambda g: g * g
    beta_fixed = lambda g: g * (1.0 - g)
    cases = [
        ("beta=0", beta_zero, 0.25),
        ("beta=g^2", beta_running, 0.25),
        ("beta=g(1-g)", beta_fixed, 0.25),
    ]
    for name, beta, g0 in cases:
        flow = euler_flow(beta, g0)
        drift = float(flow[-1] - flow[0])
        print(f"{name}: g0={g0:.6f}, g_end={flow[-1]:.6f}, drift={drift:+.6f}")

    print()
    print("Regular scheme reparametrization preserves fixed/nonfixed status")
    phi = lambda g: g + 0.3 * g * g
    dphi = lambda g: 1.0 + 0.6 * g
    for g in [0.0, 0.25, 1.0]:
        b = beta_fixed(g)
        b2 = dphi(g) * b
        print(f"g={g:.2f}, beta={b:+.6f}, phi(g)={phi(g):+.6f}, beta_phi={b2:+.6f}")

    print()
    print("ResearchNode transfer: WD5 as normalized scale generator")
    print("STEP 9 method 10: extreme cases, including p=1 and large p")
    for p in [1, 2, 3, 5, 11, 9973]:
        s = 0.7 + 14.2j
        raw = finite_diff_commutator(p, s)
        gauged = finite_diff_gauged_commutator(
            p, s, a=lambda z: 1000.13 - 700.07j + 0.01 * z
        )
        target = -math.log(p)
        print(
            f"p={p:2d}: comm={raw.real:+.12f}{raw.imag:+.2e}i, "
            f"gauged={gauged.real:+.12f}{gauged.imag:+.2e}i, "
            f"target={target:+.12f}, abs_err={abs(raw-target):.2e}, "
            f"gauge_err={abs(gauged-target):.2e}"
        )

    print()
    print("Interpretation:")
    print(
        "The beta diagnostic transfers only to the already-known universal "
        "curvature fact: a scalar zero-order counterterm added to partial_s "
        "does not change the normalized [partial_s,M_p] bracket. This does "
        "not produce a new HT-sensitive invariant."
    )


if __name__ == "__main__":
    main()
