#!/usr/bin/env python3
"""R47 candidate: ergodicity passport for value-axis corank numerics.

ResearchNode 22: Value apex (Conjecture A).

NODE: ensemble-averaged and time-averaged MSD can disagree in nonergodic gels.

Transfer: random ensemble sampling of coefficient vectors is not the same as
pathwise/shell-wise Diophantine risk.  A value-axis numerical certificate must
report exact shell minima or a coverage proof, not only ensemble residuals.
"""

from __future__ import annotations

import bisect
import itertools
import math
from statistics import median

import numpy as np


NODE = (
    "ensemble-averaged and time-averaged mean-squared displacements may "
    "disagree especially in nonergodic or weakly ergodicity-breaking systems"
)


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def ctrw_node_test(seed: int = 47022) -> None:
    rng = np.random.default_rng(seed)
    n_particles = 600
    t_max = 400
    lag = 20
    alpha = 0.62
    positions = np.zeros((n_particles, t_max + 1), dtype=float)
    for p in range(n_particles):
        t = 0.0
        x = 0.0
        next_record = 0
        while next_record <= t_max:
            wait = (1.0 + rng.pareto(alpha))
            jump = rng.normal()
            while next_record <= min(t + wait, t_max):
                positions[p, next_record] = x
                next_record += 1
            t += wait
            x += jump
        positions[p, next_record:] = x

    ensemble_msd = float(np.mean(positions[:, -1] ** 2))
    increments = positions[:, lag:] - positions[:, :-lag]
    tamsd = np.mean(increments**2, axis=1)
    eb = float(np.var(tamsd) / (np.mean(tamsd) ** 2 + 1e-300))
    print("NODE weak-ergodicity test")
    print(
        f"ensemble_msd_T={ensemble_msd:.6f} "
        f"median_time_averaged_msd_lag{lag}={median(tamsd):.6f} "
        f"mean_time_averaged_msd={np.mean(tamsd):.6f} EB={eb:.3f}"
    )
    print(
        "NODE verdict: ensemble and time/path averages disagree; a single "
        "average MSD is not a mechanism certificate."
    )


def degree2_values(logs: list[float]) -> np.ndarray:
    out = []
    for i in range(len(logs)):
        for j in range(i, len(logs)):
            out.append(logs[i] * logs[j])
    return np.asarray(out, dtype=float)


def half_sums(values: np.ndarray, bound: int):
    coeffs = list(itertools.product(range(-bound, bound + 1), repeat=len(values)))
    sums = np.array([sum(c * v for c, v in zip(coeff, values)) for coeff in coeffs], dtype=float)
    order = np.argsort(sums)
    return sums[order], [coeffs[int(i)] for i in order]


def exact_box_min(values: np.ndarray, bound: int) -> tuple[float, tuple[int, ...]]:
    left = values[:3]
    right = values[3:]
    sums_l, coeff_l = half_sums(left, bound)
    sums_r, coeff_r = half_sums(right, bound)
    best = float("inf")
    best_coeff = None
    for sl, cl in zip(sums_l, coeff_l):
        j = bisect.bisect_left(sums_r, -sl)
        for k in [j - 1, j, j + 1]:
            if 0 <= k < len(sums_r):
                coeff = tuple(cl) + tuple(coeff_r[k])
                if all(c == 0 for c in coeff):
                    continue
                residual = abs(float(sl + sums_r[k]))
                if residual < best:
                    best = residual
                    best_coeff = coeff
    assert best_coeff is not None
    return best, best_coeff


def random_residual_stats(values: np.ndarray, bound: int, rng: np.random.Generator, samples: int = 30_000):
    coeffs = rng.integers(-bound, bound + 1, size=(samples, len(values)))
    zero = np.all(coeffs == 0, axis=1)
    while np.any(zero):
        coeffs[zero] = rng.integers(-bound, bound + 1, size=(int(np.sum(zero)), len(values)))
        zero = np.all(coeffs == 0, axis=1)
    residuals = np.abs(coeffs @ values)
    return {
        "min": float(np.min(residuals)),
        "q001": float(np.quantile(residuals, 0.001)),
        "q01": float(np.quantile(residuals, 0.01)),
        "median": float(np.median(residuals)),
    }


def transfer_audit() -> None:
    attempts = [
        "prime-log corank numerics need ensemble versus path ergodicity passport",
        "reverse random residual sampling into exact coefficient-shell minima",
        "value apex tests must compare ensemble residuals to time-like coefficient paths",
    ]
    print()
    print("STEP8 transfer attempts by Levenshtein distance")
    for text in sorted(attempts, key=lambda item: levenshtein(NODE, item)):
        print(f"distance={levenshtein(NODE, text):3d}  {text}")

    print()
    print("STEP9 method #3: reverse it")
    print("reverse inference: ensemble random residuals do not imply pathwise shell coverage")

    values = degree2_values([math.log(2.0), math.log(3.0), math.log(5.0)])
    rng = np.random.default_rng(47023)
    print()
    print("HGT transfer: value-axis ensemble/path residual passport")
    print("bound exact_min random_min random_q001 random_q01 random_median q01_over_exact argmin_coeff")
    rows = []
    for bound in [4, 6, 8, 10, 12, 16]:
        exact, coeff = exact_box_min(values, bound)
        stats = random_residual_stats(values, bound, rng)
        ratio = stats["q01"] / max(exact, 1e-300)
        rows.append((bound, exact, stats["min"], stats["q01"], ratio, coeff))
        print(
            f"{bound:5d} {exact:.6e} {stats['min']:.6e} {stats['q001']:.6e} "
            f"{stats['q01']:.6e} {stats['median']:.6e} {ratio:.3e} {list(coeff)}"
        )

    miss_rows = sum(1 for _, exact, random_min, _, _, _ in rows if random_min > 10.0 * exact)
    print()
    print("Summary gates")
    print(f"random_min_misses_exact_by_10x={miss_rows}/{len(rows)}")
    print(
        "max_q01_over_exact="
        f"{max(row[4] for row in rows):.3e} at bound={max(rows, key=lambda row: row[4])[0]}"
    )
    print(
        "passport_rule=value-axis numerics must report pathwise shell minima "
        "or a coverage theorem; random ensemble residuals alone are nonergodic"
    )


def main() -> None:
    print("Penrose R47: value-axis ergodicity passport")
    print(f"NODE: {NODE}")
    ctrw_node_test()
    transfer_audit()


if __name__ == "__main__":
    main()
