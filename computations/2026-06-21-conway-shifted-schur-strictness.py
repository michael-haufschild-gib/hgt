#!/usr/bin/env python3
"""
Workflow NODE: singular Schur complements require range-inclusion conditions.

Proof-route transfer: strip this to the shifted reciprocal-seam target.
If the shifted Stieltjes theorem holds for xi, the finite Hankel blocks should
not merely be PSD: they should be positive definite. A singular finite Hankel
block is the flat-extension/finite-atomic branch of the moment problem.

This script contrasts:
  (1) a finite atomic Stieltjes measure, where Schur complements become zero;
  (2) an infinite support toy y_n=1/n^2, where shifted Hankels stay strict;
  (3) the observed on-line zeta reciprocal atoms 1/gamma_n^2, truncated, where
      shifted Hankels are strict but rapidly ill-conditioned.
"""

from __future__ import annotations

import mpmath as mp

mp.mp.dps = 80


def moments(atoms: list[mp.mpf], max_n: int) -> list[mp.mpf]:
    return [mp.fsum(a**n for a in atoms) for n in range(max_n + 1)]


def shifted_hankel(ms: list[mp.mpf], d: int, shift: int) -> mp.matrix:
    return mp.matrix([[ms[i + j + shift] for j in range(d + 1)] for i in range(d + 1)])


def schur_sequence(ms: list[mp.mpf], max_d: int, shift: int) -> list[mp.mpf]:
    out: list[mp.mpf] = []
    for d in range(max_d + 1):
        h = shifted_hankel(ms, d, shift)
        if d == 0:
            out.append(h[0, 0])
        else:
            a = shifted_hankel(ms, d - 1, shift)
            b = mp.matrix([[ms[i + d + shift]] for i in range(d)])
            c = ms[2 * d + shift]
            out.append(c - (b.T * (a**-1) * b)[0])
    return out


def print_case(name: str, atoms: list[mp.mpf], max_d: int) -> None:
    ms = moments(atoms, 2 * max_d + 3)
    print(f"=== {name} ===")
    for shift in [1, 2]:
        vals = schur_sequence(ms, max_d, shift)
        signs = "".join("+" if v > mp.mpf("1e-45") else "0" if abs(v) <= mp.mpf("1e-45") else "-" for v in vals)
        dets = [mp.det(shifted_hankel(ms, d, shift)) for d in range(max_d + 1)]
        print(f"shift={shift}: Schur signs {signs}")
        print("  Schur values:", ", ".join(mp.nstr(v, 7) for v in vals))
        print("  det signs:   ", "".join("+" if v > 0 else "0" if abs(v) <= mp.mpf('1e-45') else "-" for v in dets))
    print()


def main() -> None:
    finite_atoms = [mp.mpf("0.60"), mp.mpf("0.25"), mp.mpf("0.08")]
    print_case("finite 3-atom support: flat branch appears", finite_atoms, max_d=5)

    infinite_toy = [mp.mpf(1) / (n * n) for n in range(1, 400)]
    print_case("infinite toy support y_n=1/n^2 (400-term truncation)", infinite_toy, max_d=5)

    zeta_atoms = [1 / (mp.im(mp.zetazero(n)) ** 2) for n in range(1, 80)]
    print_case("observed zeta reciprocal atoms 1/gamma_n^2 (first 79)", zeta_atoms, max_d=5)

    print("interpretation:")
    print("- Singular Schur/range-inclusion is the finite-flat branch.")
    print("- The shifted xi target, if Stieltjes-positive, should be strict at every finite d")
    print("  because the reciprocal zero divisor has infinitely many nonzero distinct atoms.")
    print("- Therefore the shifted square-test calculus can target ordinary positive")
    print("  Schur complements; generalized inverses are numerical/truncation hygiene, not")
    print("  part of the final infinite-divisor theorem.")


if __name__ == "__main__":
    main()
