#!/usr/bin/env python3
"""
Workflow NODE: RKHS kernel normalization changes conditioning but should not
change the abstract square-test form.

Proof-route transfer: define the finite shifted square-test kernel exactly by
diagonal congruence:

    K_r(i,j) = T_{i+j+r} / sqrt(T_{2i+r} T_{2j+r}),  r in {1,2}.

When the diagonal moments are positive, H_r=[T_{i+j+r}] is PSD/PD iff K_r is
PSD/PD.  K_r is the normalized Gram kernel of monomials for Q_r, with unit
diagonal. This is a certificate-level definition, not a smoothing/ridge.
"""

from __future__ import annotations

import mpmath as mp

mp.mp.dps = 90


def zeta_recip_atoms(n: int) -> list[mp.mpf]:
    return [1 / (mp.im(mp.zetazero(k)) ** 2) for k in range(1, n + 1)]


def moments(atoms: list[mp.mpf], max_k: int) -> list[mp.mpf]:
    return [mp.fsum(a**k for a in atoms) for k in range(max_k + 1)]


def mat(ms: list[mp.mpf], d: int, shift: int) -> mp.matrix:
    return mp.matrix([[ms[i + j + shift] for j in range(d + 1)] for i in range(d + 1)])


def normalized(ms: list[mp.mpf], d: int, shift: int) -> mp.matrix:
    return mp.matrix(
        [
            [
                ms[i + j + shift] / mp.sqrt(ms[2 * i + shift] * ms[2 * j + shift])
                for j in range(d + 1)
            ]
            for i in range(d + 1)
        ]
    )


def cholesky_pivots(a: mp.matrix) -> list[mp.mpf]:
    n = a.rows
    pivots: list[mp.mpf] = []
    l = mp.zeros(n)
    for i in range(n):
        s = mp.fsum(l[i, k] ** 2 for k in range(i))
        pivot = a[i, i] - s
        pivots.append(pivot)
        if pivot <= 0:
            break
        l[i, i] = mp.sqrt(pivot)
        for j in range(i + 1, n):
            s2 = mp.fsum(l[j, k] * l[i, k] for k in range(i))
            l[j, i] = (a[j, i] - s2) / l[i, i]
    return pivots


def condition_proxy(a: mp.matrix) -> mp.mpf:
    vals = mp.eigsy(a, eigvals_only=True)
    return max(vals) / min(vals)


def main() -> None:
    atoms = zeta_recip_atoms(90)
    max_d = 6
    ms = moments(atoms, 2 * max_d + 3)

    print("=== shifted square-test RKHS normalization ===")
    print("atoms: first 90 observed zeta reciprocal atoms 1/gamma_n^2")
    print("K_r(i,j)=T_{i+j+r}/sqrt(T_{2i+r}T_{2j+r}); positivity is exact congruence-equivalent.")
    print()

    for shift in [1, 2]:
        print(f"shift r={shift}")
        for d in range(1, max_d + 1):
            h = mat(ms, d, shift)
            k = normalized(ms, d, shift)
            det_h = mp.det(h)
            det_k = mp.det(k)
            piv_h = cholesky_pivots(h)
            piv_k = cholesky_pivots(k)
            cond_h = condition_proxy(h)
            cond_k = condition_proxy(k)
            print(
                f"  d={d}: log10(det H)={mp.nstr(mp.log10(det_h), 8):>12s} "
                f"log10(det K)={mp.nstr(mp.log10(det_k), 8):>12s} "
                f"condH~1e{mp.nstr(mp.log10(cond_h), 5):>8s} "
                f"condK~1e{mp.nstr(mp.log10(cond_k), 5):>8s} "
                f"lastPivotK={mp.nstr(piv_k[-1], 7)}"
            )
        print()

    print("interpretation:")
    print("- K_r has unit diagonal and is exactly congruent to H_r, so it preserves PSD/PD.")
    print("- Raw shifted Hankel determinants live at extreme volume scales; K_r separates")
    print("  the square-test positivity question from monomial norm growth.")
    print("- This gives a canonical finite certificate object for Q_0/Q_1: Cholesky")
    print("  pivots of K_1 and K_2, not raw determinant volume or any ridge/smoothing.")


if __name__ == "__main__":
    main()
