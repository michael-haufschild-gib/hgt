import importlib.util
import pathlib
from collections import defaultdict, deque

import numpy as np


BASE = pathlib.Path(__file__).with_name("2026-06-21-conway-thin-bridge-sampling.py")
spec = importlib.util.spec_from_file_location("thin_bridge", BASE)
thin_bridge = importlib.util.module_from_spec(spec)
spec.loader.exec_module(thin_bridge)


def node_detailed_balance(seed=20260621):
    rng = np.random.default_rng(seed)
    target = np.array([0.15, 0.70, 0.15])
    # Symmetric proposals with MH correction vs a biased accept-all proposal.
    prop = np.array([[0.8, 0.2, 0.0], [0.1, 0.8, 0.1], [0.0, 0.2, 0.8]])
    prop = (prop + prop.T) / 2
    k_bal = np.zeros_like(prop)
    for i in range(3):
        for j in range(3):
            if i == j:
                continue
            k_bal[i, j] = prop[i, j] * min(1.0, target[j] / target[i])
        k_bal[i, i] = 1.0 - np.sum(k_bal[i])
    biased_prop = np.array([[0.75, 0.25, 0.0], [0.05, 0.45, 0.50], [0.0, 0.05, 0.95]])
    exact_db_bal = 0.0
    exact_db_bad = 0.0
    for i in range(3):
        for j in range(i + 1, 3):
            exact_db_bal += abs(target[i] * k_bal[i, j] - target[j] * k_bal[j, i])
            exact_db_bad += abs(target[i] * biased_prop[i, j] - target[j] * biased_prop[j, i])
    x = 1
    counts_bal = np.zeros(3)
    trans_bal = np.zeros((3, 3))
    for _ in range(60000):
        y = rng.choice(3, p=prop[x] / prop[x].sum())
        a = min(1.0, target[y] / target[x])
        old = x
        if rng.random() < a:
            x = y
        trans_bal[old, x] += 1
        counts_bal[x] += 1
    x = 1
    counts_bad = np.zeros(3)
    trans_bad = np.zeros((3, 3))
    for _ in range(60000):
        y = rng.choice(3, p=biased_prop[x])
        old = x
        x = y
        trans_bad[old, x] += 1
        counts_bad[x] += 1
    pi_bal = counts_bal / counts_bal.sum()
    pi_bad = counts_bad / counts_bad.sum()
    # Pairwise detailed-balance residual on off-diagonal transitions.
    db_bal = abs(trans_bal[0, 1] - trans_bal[1, 0]) + abs(trans_bal[1, 2] - trans_bal[2, 1])
    db_bad = abs(trans_bad[0, 1] - trans_bad[1, 0]) + abs(trans_bad[1, 2] - trans_bad[2, 1])
    return pi_bal, pi_bad, exact_db_bal, exact_db_bad


def component_label(mask):
    labels, sizes = thin_bridge.components(mask)
    if not sizes:
        return labels, -1
    return labels, int(np.argmax(sizes))


def largest_component_cells(mask):
    labels, cid = component_label(mask)
    if cid < 0:
        return []
    return list(map(tuple, np.argwhere(labels == cid)))


def path_sample(mask, mode, chains=18, steps=900, seed=0):
    rng = np.random.default_rng(seed)
    cells = largest_component_cells(mask)
    if not cells:
        return np.zeros_like(mask, dtype=bool), 0.0
    cell_set = set(cells)
    visited = np.zeros_like(mask, dtype=bool)
    trans = defaultdict(int)
    for _ in range(chains):
        x, y = cells[int(rng.integers(0, len(cells)))]
        for _ in range(steps):
            visited[x, y] = True
            if mode == "balanced":
                dirs = [(-1, 0), (1, 0), (0, -1), (0, 1)]
            elif mode == "drift":
                dirs = [(0, 1), (0, 1), (0, 1), (1, 0), (-1, 0), (0, -1)]
            else:
                raise ValueError(mode)
            dx, dy = dirs[int(rng.integers(0, len(dirs)))]
            nx, ny = x + dx, y + dy
            old = (x, y)
            if (nx, ny) in cell_set:
                x, y = nx, ny
            trans[(old, (x, y))] += 1
    # approximate move-level asymmetry on visited neighbor pairs
    pairs = 0
    residual = 0
    for (a, b), c in trans.items():
        if a == b:
            continue
        rev = trans.get((b, a), 0)
        if a < b:
            residual += abs(c - rev)
            pairs += c + rev
    return visited, residual / max(1, pairs)


def uniform_sample(mask, occupied_fraction, seed):
    rng = np.random.default_rng(seed)
    if occupied_fraction <= 0:
        return np.zeros_like(mask, dtype=bool)
    return mask & (rng.random(mask.shape) < occupied_fraction)


def mask_for(kind, window, threshold, sigma_samples=17, t_samples=180, prime_count=160, seed=0):
    sigmas = np.linspace(0.2, 0.9, sigma_samples)
    ts = np.linspace(window[0], window[1], t_samples)
    primes = thin_bridge.first_primes(prime_count)
    rng = np.random.default_rng(seed)
    return thin_bridge.zero_shadow_mask(kind, sigmas, ts, primes, rng, threshold)


def row(kind, window, threshold, seed):
    mask = mask_for(kind, window, threshold, seed=seed)
    full = thin_bridge.bridge_stats(mask)
    bal, db_bal = path_sample(mask, "balanced", seed=seed + 10)
    drift, db_drift = path_sample(mask, "drift", seed=seed + 20)
    bal_occ = bal.sum() / max(1, mask.sum())
    uni = uniform_sample(mask, bal_occ, seed + 30)
    return {
        "full": full,
        "balanced": thin_bridge.bridge_stats(bal),
        "drift": thin_bridge.bridge_stats(drift),
        "uniform": thin_bridge.bridge_stats(uni),
        "balanced_occ_within_mask": bal_occ,
        "db_bal": db_bal,
        "db_drift": db_drift,
    }


def main():
    print("NODE: MD path ensembles / detailed balance must be checked at trajectory-move level")
    pi_bal, pi_bad, db_bal, db_bad = node_detailed_balance()
    print(
        "NODE_ROW",
        f"balanced_pi={np.round(pi_bal, 3).tolist()}",
        f"biased_pi={np.round(pi_bad, 3).tolist()}",
        f"balanced_db_resid={db_bal:.4f}",
        f"biased_db_resid={db_bad:.4f}",
    )
    print()
    print("TRANSFER: ResearchNode 27 zero-shadow topology")
    print("method #15 strengthen: not just full-grid spanning; spanning must survive reversible path-ensemble sampling and matched-occupancy controls")
    for kind in ["true", "finite", "random"]:
        for window in [(100.0, 170.0), (500.0, 570.0)]:
            r = row(kind, window, 1.00, seed=20260621 + int(window[0]) + len(kind))
            print(
                "ROW",
                kind,
                f"window={window}",
                f"full_span_t={r['full']['span_t']:.0f}",
                f"full_comp={r['full']['components']:.0f}",
                f"bal_span_t={r['balanced']['span_t']:.0f}",
                f"bal_comp={r['balanced']['components']:.0f}",
                f"uniform_span_t={r['uniform']['span_t']:.0f}",
                f"uniform_comp={r['uniform']['components']:.0f}",
                f"drift_span_t={r['drift']['span_t']:.0f}",
                f"bal_occ={r['balanced_occ_within_mask']:.3f}",
                f"db_bal={r['db_bal']:.3f}",
                f"db_drift={r['db_drift']:.3f}",
            )
    print()
    print("STEP12 coverage sweep for true full-spanning masks")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        mask = mask_for("true", window, 1.00, seed=3030 + int(window[0]))
        for chains, steps in [(12, 400), (18, 900), (32, 1200), (64, 2000), (96, 3000)]:
            sampled, asym = path_sample(mask, "balanced", chains=chains, steps=steps, seed=4040 + chains + steps)
            occ = sampled.sum() / max(1, mask.sum())
            st = thin_bridge.bridge_stats(sampled)
            print(
                " SWEEP",
                f"window={window}",
                f"chains={chains}",
                f"steps={steps}",
                f"occ={occ:.3f}",
                f"span_t={st['span_t']:.0f}",
                f"comp={st['components']:.0f}",
                f"asym={asym:.3f}",
            )


if __name__ == "__main__":
    main()
