#!/usr/bin/env python3
"""Workflow test for PA5 via bare/regulator-dependent quantities.

ResearchNode formula:
    Q_W = D, signature (1|infty) / finite-rank (1,rho-1); V_arch=Re psi.

Random NODE:
    Bare quantities are regulator-dependent bookkeeping devices, not directly
    measurable physical quantities.
"""

from __future__ import annotations

import numpy as np


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, start=1):
        cur = [i]
        for j, cb in enumerate(b, start=1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def inertia(mat: np.ndarray, tol: float = 1e-10) -> tuple[int, int, int]:
    eig = np.linalg.eigvalsh(mat)
    return (
        int(np.sum(eig < -tol)),
        int(np.sum(np.abs(eig) <= tol)),
        int(np.sum(eig > tol)),
    )


def main() -> None:
    base_test = "bare regulator dependent quantity is not directly observable"
    attempts = [
        ("A", "bare finite-rank quadratic form inertia depends on cutoff"),
        ("B", "renormalized Weil form signature requires fixed condition"),
        ("C", "counterterm subtraction is not a congruence invariant operation"),
    ]
    print("STEP 8 Levenshtein transfer attempts")
    print("=" * 42)
    scored = [(tag, levenshtein(base_test, text), text) for tag, text in attempts]
    for tag, score, text in scored:
        print(f"{tag}: distance={score}, attempt={text}")
    chosen = min(scored, key=lambda row: row[1])
    print(f"chosen={chosen[0]} by minimum distance")
    print()

    print("NODE toy: regulator-dependent bare mass with fixed physical condition")
    print("=" * 72)
    target = 1.0
    for cutoff in [10, 100, 1000]:
        bare = target - 0.25 * cutoff
        loop = 0.25 * cutoff
        physical = bare + loop
        print(
            f"cutoff={cutoff:4d}: bare={bare:+.3f}, loop={loop:+.3f}, "
            f"physical={physical:+.3f}"
        )

    print()
    print("STEP 9 method 15: strengthen to inertia under subtraction vs congruence")
    print("=" * 78)
    q_phys = np.diag([1.0, -0.25, -2.0])
    print(f"physical Q inertia={inertia(q_phys)}, eig={np.linalg.eigvalsh(q_phys)}")
    for cutoff in [1, 10, 100]:
        divergent = cutoff * np.eye(3)
        bare = q_phys + divergent
        ren = bare - divergent
        scale = np.diag([cutoff, 1.0, 1.0 / cutoff])
        congr = scale.T @ q_phys @ scale
        bad_sub = bare - cutoff * np.diag([1.0, 0.0, 0.0])
        print(f"cutoff={cutoff}")
        print(
            f"  bare inertia={inertia(bare)}, renormalized inertia={inertia(ren)}, "
            f"congruence inertia={inertia(congr)}, bad-sub inertia={inertia(bad_sub)}"
        )

    print()
    print("Interpretation:")
    print(
        "The observable PA5 datum is the source-built form/signature, not a bare "
        "finite-rank matrix before the renormalization condition. Additive "
        "counterterms can change inertia unless they reconstruct the canonical "
        "form; congruence changes preserve inertia. This repeats existing PA5/"
        "kappa-minus congruence discipline."
    )


if __name__ == "__main__":
    main()
