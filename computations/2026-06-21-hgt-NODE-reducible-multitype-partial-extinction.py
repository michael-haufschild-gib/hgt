#!/usr/bin/env python3
"""NODE test: reducible multi-type branching partial extinction.

NODE:
    Reducible multi-type systems can have partial extinction distinct from
    global extinction.

Constraint:
    Extinction is vector-valued in reducible multi-type systems. A vulnerable
    source type can die out while a downstream/self-sustaining type survives,
    so scalar "any population alive" global survival hides partial extinction.
"""

from __future__ import annotations

import argparse

import numpy as np


def simulate(mu_a: float, mu_b: float, transfer: float, gens: int, reps: int, seed: int) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    a_alive = []
    b_alive = []
    global_alive = []
    a_counts_final = []
    b_counts_final = []
    for _ in range(reps):
        a = 3
        b = 0
        for _g in range(gens):
            a_to_a = rng.poisson(mu_a, size=a).sum() if a else 0
            a_to_b = rng.binomial(a, transfer) if a else 0
            b_to_b = rng.poisson(mu_b, size=b).sum() if b else 0
            a, b = int(a_to_a), int(a_to_b + b_to_b)
            if a + b > 100000:
                scale = 100000 / (a + b)
                a = int(a * scale)
                b = int(b * scale)
        a_alive.append(a > 0)
        b_alive.append(b > 0)
        global_alive.append((a + b) > 0)
        a_counts_final.append(a)
        b_counts_final.append(b)
    a_alive_arr = np.asarray(a_alive)
    b_alive_arr = np.asarray(b_alive)
    global_arr = np.asarray(global_alive)
    return {
        "mu_a": mu_a,
        "mu_b": mu_b,
        "transfer": transfer,
        "A_survival": float(np.mean(a_alive_arr)),
        "B_survival": float(np.mean(b_alive_arr)),
        "global_survival": float(np.mean(global_arr)),
        "partial_B_only": float(np.mean((~a_alive_arr) & b_alive_arr)),
        "partial_A_only": float(np.mean(a_alive_arr & (~b_alive_arr))),
        "mean_A_final": float(np.mean(a_counts_final)),
        "mean_B_final": float(np.mean(b_counts_final)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--gens", type=int, default=42)
    parser.add_argument("--reps", type=int, default=2400)
    args = parser.parse_args()

    cases = [
        (0.78, 1.10, 0.02),
        (0.78, 1.10, 0.08),
        (0.78, 1.10, 0.18),
        (0.98, 1.10, 0.08),
        (1.08, 0.78, 0.08),
        (1.08, 1.08, 0.00),
    ]
    print("NODE: reducible multi-type branching partial extinction")
    print("mu_A mu_B transfer A_survival B_survival global_survival partial_B_only partial_A_only mean_A_final mean_B_final")
    for i, (mu_a, mu_b, transfer) in enumerate(cases):
        out = simulate(mu_a, mu_b, transfer, args.gens, args.reps, seed=20260621 + i)
        print(
            f"{out['mu_a']:.2f} {out['mu_b']:.2f} {out['transfer']:.2f} "
            f"{out['A_survival']:.6f} {out['B_survival']:.6f} {out['global_survival']:.6f} "
            f"{out['partial_B_only']:.6f} {out['partial_A_only']:.6f} "
            f"{out['mean_A_final']:.6f} {out['mean_B_final']:.6f}"
        )
    print(
        "\nInterpretation key: partial_B_only demonstrates partial extinction: "
        "type A died but global extinction did not occur because type B survived."
    )


if __name__ == "__main__":
    main()
