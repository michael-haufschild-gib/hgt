#!/usr/bin/env python3
"""NODE test: modern descendant tolerance may not match extinct-relative tolerance."""

import argparse

import numpy as np


def corr(a, b):
    if np.std(a) < 1e-12 or np.std(b) < 1e-12:
        return 0.0
    return float(np.corrcoef(a, b)[0, 1])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=120000)
    parser.add_argument("--seed", type=int, default=20260621)
    args = parser.parse_args()
    rng = np.random.default_rng(args.seed)

    ancestral_tol = rng.normal(0.0, 1.0, args.n)
    refuge = rng.normal(0.0, 1.0, args.n)
    crisis_exposure = rng.normal(0.0, 1.0, args.n)
    survival_score = 0.75 * ancestral_tol + 1.25 * refuge - 0.95 * crisis_exposure
    survived = survival_score > np.quantile(survival_score, 0.70)

    print("NODE: descendant environmental tolerance can misrepresent extinct relatives")
    print("columns: drift adaptation survivor_frac corr_ancestor_modern mean_ancestor mean_modern infer_bias")
    for drift in [0.0, 0.4, 0.9, 1.5]:
        for adaptation in [-0.8, 0.0, 0.8]:
            descendant_tol = (
                ancestral_tol[survived]
                + drift * rng.normal(size=int(np.sum(survived)))
                + adaptation * refuge[survived]
            )
            anc = ancestral_tol[survived]
            c = corr(anc, descendant_tol)
            bias = float(np.mean(descendant_tol) - np.mean(anc))
            print(
                f"drift={drift:.1f} adaptation={adaptation:+.1f} survivor_frac={float(np.mean(survived)):.4f} "
                f"corr_ancestor_modern={c:+.5f} mean_ancestor={float(np.mean(anc)):+.5f} "
                f"mean_modern={float(np.mean(descendant_tol)):+.5f} infer_bias={bias:+.5f}"
            )

    print("\nBoundary controls")
    nonsurv = ~survived
    print(f"source_corr_ancestor_refuge={corr(ancestral_tol, refuge):+.5f}")
    print(f"survivor_corr_ancestor_refuge={corr(ancestral_tol[survived], refuge[survived]):+.5f}")
    print(f"nonsurvivor_mean_ancestor={float(np.mean(ancestral_tol[nonsurv])):+.5f}")
    print(f"survivor_mean_ancestor={float(np.mean(ancestral_tol[survived])):+.5f}")


if __name__ == "__main__":
    main()
