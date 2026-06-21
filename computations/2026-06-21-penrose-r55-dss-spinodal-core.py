#!/usr/bin/env python3
"""R55: spinodal-core discipline as a DSS-cross gatekeeper.

NODE: in spinodal decomposition, the unstable composition range lies inside
the spinodal, not merely inside the miscibility gap.

Target: DSS-cross (3b), modulo GPC: DSS iff the Stieltjes constants are
algebraically independent over the period field.

The transfer being tested is deliberately modest: relation-search evidence
is only the broad "miscibility" zone.  The right theorem/core is the existing
corank-to-trdeg statement for finite Euler truncations, not a generic
"period/non-period" plausibility test.
"""

from __future__ import annotations

from itertools import product
from math import factorial, sqrt
from random import Random
from typing import Iterable, List, Sequence, Tuple

import mpmath as mp
import numpy as np


def lev(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def spinodal_demo(a: float = 1.0) -> None:
    """Symmetric double-well: miscibility gap contains smaller spinodal core."""
    misc_left, misc_right = -sqrt(a), sqrt(a)
    spin_left, spin_right = -sqrt(a / 3.0), sqrt(a / 3.0)
    misc_len = misc_right - misc_left
    spin_len = spin_right - spin_left

    print("\nNODE validation: double-well free-energy geometry")
    print(f"  f(c)=c^4/4 - {a:.1f} c^2/2")
    print(f"  miscibility gap       : [{misc_left:.6f}, {misc_right:.6f}]")
    print(f"  spinodal core f''<0   : [{spin_left:.6f}, {spin_right:.6f}]")
    print(f"  spinodal/miscibility length ratio = {spin_len / misc_len:.6f}")


def mp_dot(coeffs: Sequence[int], vals: Sequence[mp.mpf]) -> mp.mpf:
    total = mp.mpf("0")
    for c, v in zip(coeffs, vals):
        total += c * v
    return total


def exhaustive_integer_relation_floor(
    vals: Sequence[mp.mpf], height: int
) -> Tuple[mp.mpf, Tuple[int, ...]]:
    best = mp.inf
    best_coeffs: Tuple[int, ...] = tuple()
    for coeffs in product(range(-height, height + 1), repeat=len(vals)):
        if all(c == 0 for c in coeffs):
            continue
        residual = abs(mp_dot(coeffs, vals))
        if residual < best:
            best = residual
            best_coeffs = tuple(coeffs)
            if residual == 0:
                break
    return best, best_coeffs


def relation_search_demo() -> None:
    """Show broad residual floors are not the same as a relation core."""
    mp.mp.dps = 80
    actual = [mp.mpf(1), mp.stieltjes(0), mp.stieltjes(1), mp.pi**2]
    rng = Random(55)
    random_control = [mp.mpf(1)] + [mp.mpf(rng.random()) for _ in range(3)]
    alpha = mp.sqrt(2)
    beta = mp.pi
    planted = [mp.mpf(1), alpha, beta, 2 * alpha - 3 * beta + 5]

    print("\nBroad relation-search zone, height <= 12, four-coordinate probes")
    for label, vals in [
        ("actual cross set [1,gamma0,gamma1,pi^2]", actual),
        ("random control [1,u1,u2,u3]", random_control),
        ("planted relation [1,a,b,2a-3b+5]", planted),
    ]:
        residual, coeffs = exhaustive_integer_relation_floor(vals, height=12)
        print(f"  {label:42s} min_residual={float(residual):.3e} coeffs={coeffs}")


def bernoulli_plus(n: int) -> mp.mpf:
    if n == 1:
        return mp.mpf("0.5")
    return mp.bernoulli(n)


def euler_truncated_coeffs(logs: Sequence[mp.mpf], nmax: int) -> List[mp.mpf]:
    """Coefficients of prod_i x_i/(1-exp(-x_i)), x_i=s log p_i."""
    coeffs = [mp.mpf(1)] + [mp.mpf(0)] * nmax
    for logp in logs:
        factor = [bernoulli_plus(n) * (logp**n) / factorial(n) for n in range(nmax + 1)]
        nxt = [mp.mpf(0)] * (nmax + 1)
        for i in range(nmax + 1):
            for j in range(nmax + 1 - i):
                nxt[i + j] += coeffs[i] * factor[j]
        coeffs = nxt
    return coeffs


def coeff_vector_float(logs: Sequence[mp.mpf], order: int) -> np.ndarray:
    coeffs = euler_truncated_coeffs(logs, order)
    return np.array([float(coeffs[i]) for i in range(1, order + 1)], dtype=float)


def finite_difference_jacobian(logs: Sequence[mp.mpf], order: int) -> np.ndarray:
    base = np.array([float(x) for x in logs], dtype=float)
    eps = 1e-6
    cols = []
    for j in range(len(base)):
        plus = base.copy()
        minus = base.copy()
        plus[j] += eps
        minus[j] -= eps
        col = (coeff_vector_float([mp.mpf(x) for x in plus], order) - coeff_vector_float([mp.mpf(x) for x in minus], order)) / (2 * eps)
        cols.append(col)
    return np.column_stack(cols)


def right_theorem_demo() -> None:
    """Numerically illustrate the finite Euler theorem's local core."""
    mp.mp.dps = 80
    logs = [mp.log(2), mp.log(3), mp.log(5)]
    jac = finite_difference_jacobian(logs, order=6)
    svals = np.linalg.svd(jac, compute_uv=False)

    one_frob_logs = [mp.log(2)]
    one_coeffs = euler_truncated_coeffs(one_frob_logs, 4)
    ratios = []
    for n in range(1, 5):
        ratios.append(one_coeffs[n] / (mp.log(2) ** n))

    print("\nRight-theorem diagnostic: finite Euler Stieltjes/corank core")
    print("  S={2,3,5}: Jacobian singular values for first 6 regular coefficients")
    print("  " + ", ".join(f"{s:.6e}" for s in svals))
    print("  one-Frobenius S={2}: coeff_n/(log 2)^n for n=1..4")
    print("  " + ", ".join(mp.nstr(x, 12) for x in ratios))
    print("  Reading: the exact core is corank/trdeg of the prime-log lattice;")
    print("  relation-search residuals are only the outer plausibility zone.")


def main() -> None:
    node = "the unstable composition range lies inside the spinodal, not merely inside the miscibility gap"
    attempts = [
        "period/nonperiod plausibility is only the miscibility gap",
        "DSS-cross relation failure is the smaller algebraic-dependence core",
        "corank-to-trdeg is the spinodal core inside DSS-cross heuristics",
    ]
    print("R55 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    spinodal_demo()
    relation_search_demo()
    right_theorem_demo()

    print("\nInterpretation:")
    print("  The spinodal analogy does not add a new DSS-cross theorem.")
    print("  It is a gatekeeper: do not count low-height PSLQ/null evidence as the")
    print("  true instability core; the right theorem is the existing finite")
    print("  Euler corank = Stieltjes-trdeg equality plus the open monotonicity rung.")


if __name__ == "__main__":
    main()
