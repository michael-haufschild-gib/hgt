#!/usr/bin/env python3
"""Workflow test for PS12 through random-matrix normalization scale.

ResearchNode formula:
    zeta(2k+1)=int y^k dnu(y), H_FID=[zeta(2(i+j)+3)] PSD unconditionally.

Random NODE:
    The normalization convention for matrix entries changes the limiting
    spectral scale.
"""

from __future__ import annotations

import math
import numpy as np
import mpmath as mp


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


def fid_moment(k: int) -> mp.mpf:
    return mp.zeta(2 * k + 3)


def hankel(d: int, scale: mp.mpf = mp.mpf(1)) -> mp.matrix:
    return mp.matrix([[scale ** (i + j) * fid_moment(i + j) for j in range(d)] for i in range(d)])


def eigvals_mp(mat: mp.matrix) -> list[mp.mpf]:
    vals = mp.eigsy(mat, eigvals_only=True)
    return [vals[i] for i in range(vals.rows)]


def main() -> None:
    mp.mp.dps = 80
    base_test = "change matrix entry normalization and observe limiting spectral scale"
    attempts = [
        ("A", "change moment variable normalization y to cy and observe Hankel scale"),
        ("B", "normalize Hankel kernel to unit diagonal and observe conditioning"),
        ("C", "change support endpoint normalization and compare integer versus zero scale"),
    ]
    print("STEP 8 Levenshtein transfer attempts")
    print("=" * 42)
    scored = [(tag, levenshtein(base_test, text), text) for tag, text in attempts]
    for tag, score, text in scored:
        print(f"{tag}: distance={score}, attempt={text}")
    chosen = min(scored, key=lambda row: row[1])
    print(f"chosen={chosen[0]} by minimum distance")
    print()

    print("NODE sanity: Wigner entry normalization changes spectral scale")
    print("=" * 64)
    rng = np.random.default_rng(20260621)
    n = 220
    raw = rng.normal(size=(n, n))
    sym = (raw + raw.T) / 2
    for denom in [1, math.sqrt(n), math.sqrt(2 * n)]:
        vals = np.linalg.eigvalsh(sym / denom)
        print(
            f"denom={denom:.6f}: min={vals[0]:+.4f}, max={vals[-1]:+.4f}, "
            f"std={vals.std():.4f}"
        )

    print()
    print("STEP 9 method 15: strengthen from PSD to determinants/conditioning")
    print("=" * 72)
    d = 7
    base = hankel(d, mp.mpf(1))
    base_det = mp.det(base)
    base_eigs = eigvals_mp(base)
    print(
        f"base: min_eig={mp.nstr(base_eigs[0], 8)}, "
        f"max_eig={mp.nstr(base_eigs[-1], 8)}, "
        f"cond={mp.nstr(base_eigs[-1]/base_eigs[0], 8)}, "
        f"log10det={mp.nstr(mp.log10(base_det), 12)}"
    )
    for c in [mp.mpf("0.01"), mp.mpf("0.1"), mp.mpf("10"), mp.mpf("100")]:
        h = hankel(d, c)
        det = mp.det(h)
        eigs = eigvals_mp(h)
        exponent = d * (d - 1)
        predicted = c ** exponent * base_det
        diag = np.diag([float(c ** i) for i in range(d)])
        arr_base = np.array([[float(base[i, j]) for j in range(d)] for i in range(d)])
        congr = diag @ arr_base @ diag
        arr_h = np.array([[float(h[i, j]) for j in range(d)] for i in range(d)])
        print(
            f"c={mp.nstr(c, 5)}: min_eig={mp.nstr(eigs[0], 8)}, "
            f"cond={mp.nstr(eigs[-1]/eigs[0], 8)}, "
            f"log10det={mp.nstr(mp.log10(det), 12)}, "
            f"det/(c^{exponent}det0)={mp.nstr(det/predicted, 8)}, "
            f"congruence_err={np.linalg.norm(arr_h-congr):.3e}"
        )

    print()
    print("Interpretation:")
    print(
        "Moment-scale normalization changes determinant size and conditioning by "
        "diagonal congruence while preserving PSD. For PS12 this repeats the known "
        "FID lesson: reconditioning is not RH content without a source-built "
        "integer-to-zero support transfer."
    )


if __name__ == "__main__":
    main()
