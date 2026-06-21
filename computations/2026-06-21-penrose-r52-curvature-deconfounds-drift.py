#!/usr/bin/env python3
"""R52: drift-confounding transfer to zero-curvature hierarchy.

NODE: selection and assortment can be statistically confounded in inferred
drift terms.

Target: transverse curvature near zeros.  Test small cases where first
derivative / drift features are confounded by background affine terms, while
second curvature separates on-line zeros from off-line FE quartets.
"""

from __future__ import annotations

from math import log
from random import Random
from statistics import mean
from typing import Callable, List, Sequence, Tuple


def lev(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(
                min(
                    prev[j] + 1,
                    cur[-1] + 1,
                    prev[j - 1] + (ca != cb),
                )
            )
        prev = cur
    return prev[-1]


def node_confounding_demo() -> None:
    rng = Random(52)
    n = 200
    s_true = 0.8
    a_true = 0.8
    xs = [rng.uniform(-1, 1) for _ in range(n)]
    # Selection and assortment covariates are almost collinear.
    assort = [x + rng.gauss(0, 0.08) for x in xs]
    y = [s_true * x + a_true * z + rng.gauss(0, 0.15) for x, z in zip(xs, assort)]
    beta_selection_only = sum(x * yy for x, yy in zip(xs, y)) / sum(x * x for x in xs)
    print("\nNODE validation: drift confounding")
    print(f"  true selection={s_true:.3f}, true assortment={a_true:.3f}")
    print(f"  one-covariate inferred selection={beta_selection_only:.3f}")


def off_line_curvature(a: float, tau: float) -> float:
    return 2 * (a * a - tau * tau) / (a * a + tau * tau) ** 2


def on_line_curvature(tau: float, eps: float = 1e-9) -> float:
    return -1.0 / (tau * tau + eps)


def on_line_log_abs(tau: float, eps: float = 1e-9) -> float:
    return 0.5 * log(tau * tau + eps)


def off_line_log_abs(a: float, tau: float) -> float:
    return log((a * a + tau * tau) ** 0.5)


def finite_diff_slope(values: Sequence[float], h: float) -> List[float]:
    return [(values[i + 1] - values[i - 1]) / (2 * h) for i in range(1, len(values) - 1)]


def main() -> None:
    node = "selection and assortment can be statistically confounded in inferred drift terms"
    attempts = [
        "curvature deconfounds off-line source from affine drift",
        "first derivative zero drift is confounded but second derivative sign is not",
        "curvature hierarchy separates selection-like source displacement from background assortment",
    ]
    print("R52 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    node_confounding_demo()

    taus = [(-0.2 + 0.01 * i) for i in range(41)]
    h = 0.01
    a = 0.08
    affine_backgrounds = [-5.0, 0.0, 5.0]

    print("\nSmall curvature cases:")
    for b in affine_backgrounds:
        online_vals = [on_line_log_abs(t) + b * t for t in taus]
        offline_vals = [off_line_log_abs(a, t) + b * t for t in taus]
        online_slopes = finite_diff_slope(online_vals, h)
        offline_slopes = finite_diff_slope(offline_vals, h)
        online_center_curv = on_line_curvature(0.0)
        offline_center_curv = off_line_curvature(a, 0.0)
        print(
            f"  affine drift b={b:+.1f}: "
            f"median_slope_online={mean(online_slopes):+.4f}, "
            f"median_slope_offline={mean(offline_slopes):+.4f}, "
            f"center_curv_online={online_center_curv:+.4e}, "
            f"center_curv_offline={offline_center_curv:+.4e}"
        )

    print("\nBoundary sign check for off-line quartet:")
    for tau in [0.0, 0.04, 0.08, 0.12, 0.20]:
        print(f"  tau/a={tau/a:.2f}: C_a(tau)={off_line_curvature(a, tau):+.6f}")

    print("\nInterpretation:")
    print("  Affine drift shifts first-derivative features, but second derivative removes it.")
    print("  Positive center curvature is a local off-line source signature; this is already the target theorem shape.")


if __name__ == "__main__":
    main()
