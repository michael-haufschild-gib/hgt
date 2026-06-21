#!/usr/bin/env python3
import math
import random

import numpy as np


def node_gauge_copy_bias(n=400, eps=0.22, seed=20260621):
    rng = random.Random(seed)
    rows = []
    for i in range(n):
        sector = i % 4
        # Two gauge copies satisfy the same coarse gauge functional but give opposite residuals.
        # Uneven copy selection by sector creates gauge-variant sector bias while global mean cancels.
        copy = 1 if sector in (0, 1) else -1
        if rng.random() < 0.08:
            copy *= -1
        residual = copy * eps + rng.gauss(0.0, 0.015)
        rows.append((sector, copy, residual, math.sin(residual)))
    global_mean = sum(r[3] for r in rows) / n
    sector_means = {}
    for s in range(4):
        xs = [r[3] for r in rows if r[0] == s]
        sector_means[s] = sum(xs) / len(xs)
    return global_mean, sector_means


def commutator(A, B):
    return A @ B - B @ A


def research_copy_compatibility(n=200, seed=7):
    rng = random.Random(seed)
    A0 = np.array([[0.0, 1.0], [-1.0, 0.0]])
    B0 = np.array([[0.35, 0.20], [0.05, -0.35]])
    C0 = commutator(A0, B0)
    signed = []
    norms = []
    sectors = {1: [], -1: []}
    for i in range(n):
        # Two "gauge copies" flip the reported signed compatibility defect but preserve its norm.
        copy = 1 if i % 2 == 0 else -1
        # Add small object variation without changing the basic incompatibility.
        scale = 1.0 + rng.uniform(-0.08, 0.08)
        C = copy * scale * C0
        signed.append(C)
        norm = float(np.linalg.norm(C, ord="fro"))
        norms.append(norm)
        sectors[copy].append(C)
    mean_signed = sum(signed) / n
    sector_plus = sum(sectors[1]) / len(sectors[1])
    sector_minus = sum(sectors[-1]) / len(sectors[-1])
    return {
        "mean_signed_norm": float(np.linalg.norm(mean_signed, ord="fro")),
        "mean_object_norm": float(np.mean(norms)),
        "p95_object_norm": float(np.quantile(norms, 0.95)),
        "sector_plus_norm": float(np.linalg.norm(sector_plus, ord="fro")),
        "sector_minus_norm": float(np.linalg.norm(sector_minus, ord="fro")),
        "base_norm": float(np.linalg.norm(C0, ord="fro")),
    }


def tolerance_filter_effect(n=200, seed=9):
    rng = random.Random(seed)
    defects = []
    for i in range(n):
        # Rare high-defect objects are exactly the ones a lax stopping criterion may lose.
        defect = abs(rng.gauss(0.25, 0.04))
        if rng.random() < 0.08:
            defect += rng.uniform(0.6, 1.0)
        defects.append(defect)
    full = np.array(defects)
    kept = np.array([x for x in defects if x < 0.55])
    return {
        "full_mean": float(np.mean(full)),
        "full_p95": float(np.quantile(full, 0.95)),
        "kept_mean": float(np.mean(kept)),
        "kept_p95": float(np.quantile(kept, 0.95)),
        "dropped": len(full) - len(kept),
    }


def main():
    print("NODE test: gauge copy selection can preserve global mean while spoiling sector averages")
    global_mean, sector_means = node_gauge_copy_bias()
    print(f"  global gauge-variant mean={global_mean:+.6f}")
    for s, m in sector_means.items():
        print(f"  sector={s} mean={m:+.6f}")
    print("  Same gauge condition, uneven copy selection: global average hides sector bias.")

    print()
    print("ResearchNode mutation: native weld category objectwise/fiberwise compatibility")
    rep = research_copy_compatibility()
    print(f"  base commutator norm={rep['base_norm']:.6f}")
    print(f"  ensemble signed mean commutator norm={rep['mean_signed_norm']:.6e}")
    print(f"  mean objectwise commutator norm={rep['mean_object_norm']:.6f}")
    print(f"  p95 objectwise commutator norm={rep['p95_object_norm']:.6f}")
    print(f"  copy-sector + mean norm={rep['sector_plus_norm']:.6f}")
    print(f"  copy-sector - mean norm={rep['sector_minus_norm']:.6f}")

    filt = tolerance_filter_effect()
    print("  tolerance-filter artifact:")
    print(
        f"    full mean/p95={filt['full_mean']:.6f}/{filt['full_p95']:.6f}; "
        f"kept mean/p95={filt['kept_mean']:.6f}/{filt['kept_p95']:.6f}; dropped={filt['dropped']}"
    )

    print()
    print("Finding:")
    print("  Ensemble-zero compatibility can be a copy-selection artifact. A native weld category needs")
    print("  a copy-resolved fiberwise passport: per-object commutator norm, copy-sector means, and")
    print("  tolerance/dropout accounting, not just the signed ensemble average.")


if __name__ == "__main__":
    main()
