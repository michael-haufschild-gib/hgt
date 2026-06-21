#!/usr/bin/env python3
"""THE-MACHINE tick: urban spatial autocorrelation -> APEX-A.

NODE:
  Spatial autocorrelation violates independence assumptions of many fitted models.

Consolidated target:
  APEX-A -- Schanuel-for-prime-logs / algebraic independence.

STEP 9 method:
  12. Find an invariant.
"""

from __future__ import annotations

import math

import numpy as np


NODE = "spatial autocorrelation violates the independence assumptions of many fitted models"

TRANSFER_ATTEMPTS = [
    "prime log monomial supports have autocorrelation so relation coordinates are not independent samples",
    "APEX A finite monomial tests need shared prime support autocorrelation audits",
    "Schanuel prime log searches should block by shared prime support not naive coordinates",
]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def moran_i(values: np.ndarray, adjacency: list[list[int]]) -> float:
    x = np.asarray(values, dtype=float)
    z = x - float(np.mean(x))
    denom = float(np.sum(z * z))
    if denom <= 1e-300:
        return 0.0
    wsum = 0
    num = 0.0
    for i, neigh in enumerate(adjacency):
        for j in neigh:
            num += z[i] * z[j]
            wsum += 1
    n = len(x)
    return float((n / max(wsum, 1)) * num / denom)


def node_rows() -> list[str]:
    rng = np.random.default_rng(2606215511)
    n_side = 24
    coords = np.array([(i, j) for i in range(n_side) for j in range(n_side)])
    n = len(coords)
    log_pop = rng.normal(size=n)
    white = rng.normal(scale=0.18, size=(n_side, n_side))
    smooth = white.copy()
    for _ in range(20):
        smooth = (
            smooth
            + np.roll(smooth, 1, axis=0)
            + np.roll(smooth, -1, axis=0)
            + np.roll(smooth, 1, axis=1)
            + np.roll(smooth, -1, axis=1)
        ) / 5.0
    eps_auto = smooth.ravel()
    eps_iid = rng.normal(scale=float(np.std(eps_auto)), size=n)
    y_auto = 1.15 * log_pop + eps_auto
    y_iid = 1.15 * log_pop + eps_iid
    xmat = np.column_stack([np.ones(n), log_pop])
    beta_auto = np.linalg.lstsq(xmat, y_auto, rcond=None)[0]
    beta_iid = np.linalg.lstsq(xmat, y_iid, rcond=None)[0]
    resid_auto = y_auto - xmat @ beta_auto
    resid_iid = y_iid - xmat @ beta_iid
    adjacency = []
    for i, (r, c) in enumerate(coords):
        neigh = []
        for j, (rr, cc) in enumerate(coords):
            if abs(r - rr) + abs(c - cc) == 1:
                neigh.append(j)
        adjacency.append(neigh)
    i_auto = moran_i(resid_auto, adjacency)
    i_iid = moran_i(resid_iid, adjacency)
    naive_se_auto = float(np.sqrt(np.sum(resid_auto**2) / (n - 2) / np.sum((log_pop - np.mean(log_pop)) ** 2)))
    block_factor = math.sqrt((1 + i_auto) / max(1 - i_auto, 1e-6))
    lines = ["STEP 6 NODE TEST: spatial autocorrelation survives a fitted scaling law"]
    lines.append("case beta_hat residual_moran_I naive_se autocorr_se_inflated")
    lines.append(f"iid_errors      {beta_iid[1]:.5f} {i_iid:+.5f} {naive_se_auto:.5f} {naive_se_auto:.5f}")
    lines.append(
        f"autocorr_errors {beta_auto[1]:.5f} {i_auto:+.5f} {naive_se_auto:.5f} {naive_se_auto * block_factor:.5f}"
    )
    lines.append(
        "NODE verdict: a fitted exponent can look ordinary while residual autocorrelation violates "
        "the independent-sample assumption."
    )
    return lines


def first_primes(n: int) -> list[int]:
    out = []
    c = 2
    while len(out) < n:
        ok = True
        for p in out:
            if p * p > c:
                break
            if c % p == 0:
                ok = False
                break
        if ok:
            out.append(c)
        c += 1 if c == 2 else 2
    return out


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Urban Moran-I formulas do not apply unchanged to APEX-A. The transfer keeps the invariant: "
        "audit whether finite monomial coordinates have dependence induced by shared prime supports."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    d, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")

    lines.append("\nSTEP 9 METHOD 12: FIND AN INVARIANT")
    rng = np.random.default_rng(2606215583)
    lines.append("n_primes nodes graph_edges moran_I shuffled_mean shuffled_sd z_score effective_independent_fraction")
    for n_primes in [8, 12, 16, 24, 32]:
        logs = np.log(np.array(first_primes(n_primes), dtype=float))
        nodes = []
        values = []
        for i in range(n_primes):
            for j in range(i, n_primes):
                nodes.append((i, j))
                values.append(float(logs[i] * logs[j]))
        adjacency = []
        edges = 0
        for a, (i, j) in enumerate(nodes):
            neigh = []
            support = {i, j}
            for b, (k, l) in enumerate(nodes):
                if a != b and support & {k, l}:
                    neigh.append(b)
            edges += len(neigh)
            adjacency.append(neigh)
        values = np.array(values)
        observed = moran_i(values, adjacency)
        shuffled = np.array([moran_i(rng.permutation(values), adjacency) for _ in range(300)])
        z = (observed - float(np.mean(shuffled))) / (float(np.std(shuffled)) + 1e-300)
        eff_frac = max(0.0, min(1.0, (1.0 - observed) / (1.0 + observed))) if observed < 1 else 0.0
        lines.append(
            f"{n_primes:02d} {len(nodes):04d} {edges:06d} {observed:+.5f} "
            f"{float(np.mean(shuffled)):+.5f} {float(np.std(shuffled)):.5f} {z:+.2f} {eff_frac:.4f}"
        )
    lines.append(
        "\nProvisional interpretation: degree-2 prime-log monomials have strong support autocorrelation "
        "under the shared-prime graph. This is an audit invariant for finite APEX-A experiments, but "
        "by itself it is dependence hygiene, not Schanuel content."
    )
    return lines


def main() -> None:
    out = []
    out.append("THE-MACHINE tick: urban spatial autocorrelation -> APEX-A")
    out.append(f"NODE: {NODE}")
    out.append("Standing-order target: 18/32 APEX-A Schanuel-for-prime-logs")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
