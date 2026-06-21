#!/usr/bin/env python3
"""Bridge variable w = rho - 1/2 versus cycle resets.

Research node:
    w = rho - 1/2, the seam-centered zero coordinate from bridge-theorem.md.

Random NODE:
    Rare extreme events in Lotka-Volterra ecosystems can restart a cycle.

Constraint:
    The neutral Lotka-Volterra orbit is confined to a conserved level set.
    A shock does not merely advance phase; it jumps to a new level set.

Method 14:
    Weaken the problem. On the bridge side, test only the minimal FE-pair
    folding constraint under a shifted center c = 1/2 + eps.
"""

from __future__ import annotations

from math import log
from typing import Callable


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, start=1):
        cur = [i]
        for j, cb in enumerate(b, start=1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def lv_rhs(x: float, y: float, alpha: float, beta: float, delta: float, gamma: float) -> tuple[float, float]:
    return alpha * x - beta * x * y, delta * x * y - gamma * y


def lv_invariant(x: float, y: float, alpha: float, beta: float, delta: float, gamma: float) -> float:
    return delta * x - gamma * log(x) + beta * y - alpha * log(y)


def rk4_step(
    x: float,
    y: float,
    h: float,
    rhs: Callable[[float, float], tuple[float, float]],
) -> tuple[float, float]:
    k1x, k1y = rhs(x, y)
    k2x, k2y = rhs(x + 0.5 * h * k1x, y + 0.5 * h * k1y)
    k3x, k3y = rhs(x + 0.5 * h * k2x, y + 0.5 * h * k2y)
    k4x, k4y = rhs(x + h * k3x, y + h * k3y)
    return x + h * (k1x + 2 * k2x + 2 * k3x + k4x) / 6, y + h * (k1y + 2 * k2y + 2 * k3y + k4y) / 6


def simulate_lv(shock: bool) -> tuple[float, float, float, float]:
    alpha, beta, delta, gamma = 1.2, 0.8, 0.7, 1.0
    x, y = 1.8, 0.65
    h = 0.01
    steps = 5000
    rhs = lambda a, b: lv_rhs(a, b, alpha, beta, delta, gamma)
    h_values = []
    jump_before = jump_after = None
    for n in range(steps):
        if shock and n == steps // 2:
            jump_before = lv_invariant(x, y, alpha, beta, delta, gamma)
            x *= 0.55
            y *= 1.35
            jump_after = lv_invariant(x, y, alpha, beta, delta, gamma)
        x, y = rk4_step(x, y, h, rhs)
        h_values.append(lv_invariant(x, y, alpha, beta, delta, gamma))
    return min(h_values), max(h_values), jump_before or h_values[0], jump_after or h_values[0]


def y_from_shifted_center(w: complex, eps: float, sign: int) -> complex:
    # FE pair rho = 1/2 +/- w, but centered at c = 1/2 + eps.
    z = sign * w - eps
    return -1.0 / (z * z)


def fold_mismatch(w: complex, eps: float) -> complex:
    y_plus = y_from_shifted_center(w, eps, +1)
    y_minus = y_from_shifted_center(w, eps, -1)
    return y_plus - y_minus


def fold_mismatch_formula(w: complex, eps: float) -> complex:
    return -4.0 * w * eps / ((w * w - eps * eps) ** 2)


def odd_pair_sum(w: complex, eps: float, power: int) -> complex:
    z_plus = w - eps
    z_minus = -w - eps
    return z_plus**power + z_minus**power


def print_header(title: str) -> None:
    print("\n" + title)
    print("-" * len(title))


def main() -> None:
    node_constraint = "rare extreme event resets a neutral cycle level"
    attempts = [
        "cycle reset changes conserved level to test seam origin reset",
        "off center recentering breaks FE pair folding in w coordinate",
        "rare shock in orbit becomes shifted seam coordinate c not equal one half",
    ]

    print_header("Step 8 transfer attempts")
    scored = []
    for label, attempt in zip("ABC", attempts):
        d = levenshtein(node_constraint, attempt)
        scored.append((d, label, attempt))
        print(f"{label}: distance={d:2d} :: {attempt}")
    distance, label, chosen = min(scored)
    print(f"chosen={label}, distance={distance}")

    print_header("NODE test: rare shock jumps the Lotka-Volterra invariant")
    no_min, no_max, _, _ = simulate_lv(shock=False)
    sh_min, sh_max, before, after = simulate_lv(shock=True)
    print(f"unshocked invariant range: min={no_min:.12f} max={no_max:.12f} drift={no_max - no_min:.3e}")
    print(f"shock invariant: before={before:.12f} after={after:.12f} jump={after - before:+.6f}")
    print(f"post-shock full-run invariant range: min={sh_min:.12f} max={sh_max:.12f}")

    print_header("Bridge transfer: resetting the seam center breaks FE folding")
    w = complex(0.23, 14.13)
    for eps in (0.0, 0.01, 0.05, -0.05):
        mismatch = fold_mismatch(w, eps)
        formula = fold_mismatch_formula(w, eps)
        odd1 = odd_pair_sum(w, eps, 1)
        odd3 = odd_pair_sum(w, eps, 3)
        print(
            f"eps={eps:+.3f} |y_plus-y_minus|={abs(mismatch):.6e} "
            f"formula_error={abs(mismatch - formula):.3e} "
            f"odd1={odd1.real:+.6e}{odd1.imag:+.2e}i "
            f"odd3={odd3.real:+.6e}{odd3.imag:+.2e}i"
        )

    print_header("Weakened theorem")
    print(
        "For a nonzero FE pair +/-w, the shifted-center reciprocal atoms "
        "-(w-eps)^(-2) and -(-w-eps)^(-2) are equal iff eps=0. "
        "The same condition makes all odd centered pair sums vanish."
    )
    print(
        "Thus w=rho-1/2 is not a resettable origin for the bridge coordinate; "
        "it is forced by the FE fixed seam."
    )
    print(
        "verdict_hint: likely reduce-to-known via FE centered parity / Xi(w) even, "
        "unless treated as a separate bridge-coordinate guardrail."
    )


if __name__ == "__main__":
    main()
