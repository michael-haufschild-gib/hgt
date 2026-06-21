#!/usr/bin/env python3
"""THE-MACHINE tick: survey masks -> APEX-B faithful positivity.

NODE:
  Survey masks, dust extinction, and incomplete sky coverage can create or hide
  apparent clustering.

Consolidated target:
  19/32 APEX-B faithful positivity.

STEP 9 method:
  16. Use a minimal counterexample.
"""

from __future__ import annotations

import math

import numpy as np


NODE = "The effect of survey masks, dust extinction, and incomplete sky coverage on apparent clustering"
TARGET = "19/32 APEX-B faithful positivity"
METHOD = "16. Use a minimal counterexample"

TRANSFER_ATTEMPTS = [
    "faithful positivity tests need mask certificates for sparse off-line curvature windows",
    "survey masks become height-coverage masks for all-degree positivity defects",
    "incomplete coverage can hide APEX-B no-margin positivity counterexamples",
]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_rows() -> list[str]:
    rng = np.random.default_rng(2606216509)
    n = 16000
    pts = rng.uniform(size=(n, 2))
    # A dust/mask band removes the middle of the survey. If ignored, left and
    # right caps look clustered because cross-band pairs are absent.
    mask = np.abs(pts[:, 0] - 0.5) > 0.08
    kept = pts[mask]
    sample = kept[rng.choice(len(kept), size=3000, replace=False)]
    d = np.sqrt(np.sum((sample[:, None, :] - sample[None, :, :]) ** 2, axis=2))
    tri = d[np.triu_indices_from(d, k=1)]
    close = float(np.mean(tri < 0.08))
    far = float(np.mean(tri > 0.55))
    # Correct reference: apply the same mask to a fresh random catalog.
    ctrl = rng.uniform(size=(n, 2))
    ctrl = ctrl[np.abs(ctrl[:, 0] - 0.5) > 0.08]
    ctrl = ctrl[rng.choice(len(ctrl), size=3000, replace=False)]
    cd = np.sqrt(np.sum((ctrl[:, None, :] - ctrl[None, :, :]) ** 2, axis=2))
    ctri = cd[np.triu_indices_from(cd, k=1)]
    close_ctrl = float(np.mean(ctri < 0.08))
    far_ctrl = float(np.mean(ctri > 0.55))
    lines = ["STEP 5/6 NODE TEST: survey mask creates false clustering if the mask is ignored"]
    lines.append(
        "Constraint: apparent pair statistics must be compared against the same angular/selection mask, "
        "not an unmasked reference."
    )
    lines.append("stat masked_catalog same_mask_reference unmasked_naive_reference")
    # The unmasked close/far rates are approximated by all pts sample.
    all_sample = pts[rng.choice(len(pts), size=3000, replace=False)]
    ad = np.sqrt(np.sum((all_sample[:, None, :] - all_sample[None, :, :]) ** 2, axis=2))
    atri = ad[np.triu_indices_from(ad, k=1)]
    lines.append(f"close_pair_frac {close:.6f} {close_ctrl:.6f} {float(np.mean(atri < 0.08)):.6f}")
    lines.append(f"far_pair_frac {far:.6f} {far_ctrl:.6f} {float(np.mean(atri > 0.55)):.6f}")
    lines.append(
        "NODE verdict: the masked catalog differs from the unmasked naive reference, but agrees with "
        "a same-mask random reference. Coverage belongs in the null model."
    )
    return lines


def quartet_curvature(tau: np.ndarray, a: float) -> np.ndarray:
    return 2.0 * (a * a - tau * tau) / ((a * a + tau * tau) ** 2)


def random_block_mask(grid: np.ndarray, rng, keep_frac: float, block_width: float) -> np.ndarray:
    mask = np.ones_like(grid, dtype=bool)
    domain = float(grid[-1] - grid[0])
    remove_target = (1.0 - keep_frac) * domain
    removed = 0.0
    attempts = 0
    while removed < remove_target and attempts < 200:
        attempts += 1
        center = float(rng.uniform(grid[0], grid[-1]))
        half = block_width / 2.0
        before = int(np.sum(mask))
        mask &= ~((grid >= center - half) & (grid <= center + half))
        after = int(np.sum(mask))
        removed += (before - after) / max(len(grid) - 1, 1) * domain
    return mask


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Galaxy-mask formulas do not apply unchanged to APEX-B. The transfer keeps only the "
        "constraint: a measured positivity/curvature detector is invalid without a coverage mask."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    _, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")
    lines.append("\nSTEP 9 METHOD 16: MINIMAL MASK COUNTEREXAMPLE")
    lines.append(
        "Use the local APEX-B detector: an off-line FE quartet contributes "
        "C_a(tau)=2(a^2-tau^2)/(a^2+tau^2)^2, positive exactly for |tau|<a. "
        "Find how little height coverage can be missing while hiding the positive core."
    )
    lines.append("a domain_half mask_half removed_fraction observed_max observed_mean positive_visible")
    for a in [0.04, 0.08, 0.16, 0.32]:
        L = 8.0 * a
        grid = np.linspace(-L, L, 4001)
        curv = quartet_curvature(grid, a)
        for mask_half in [0.0, 0.25 * a, 0.50 * a, 0.75 * a, 1.00 * a, 1.25 * a]:
            keep = np.abs(grid) > mask_half
            removed = 1.0 - float(np.mean(keep))
            obs = curv[keep]
            visible = int(float(np.max(obs)) > 0.0)
            lines.append(
                f"{a:.3f} {L:.3f} {mask_half:.4f} {removed:.4f} "
                f"{float(np.max(obs)):.6f} {float(np.mean(obs)):.6f} {visible}"
            )

    rng = np.random.default_rng(2606216617)
    lines.append("\nrandom_block_masks a keep_frac block_width/a detect_prob mean_observed_max")
    for a in [0.08, 0.16]:
        L = 8.0 * a
        grid = np.linspace(-L, L, 4001)
        curv = quartet_curvature(grid, a)
        for keep_frac in [0.70, 0.80, 0.90, 0.95]:
            for bw_mult in [0.5, 1.0, 2.0]:
                detected = []
                maxes = []
                for _ in range(120):
                    keep = random_block_mask(grid, rng, keep_frac, bw_mult * a)
                    obsmax = float(np.max(curv[keep])) if np.any(keep) else float("-inf")
                    maxes.append(obsmax)
                    detected.append(obsmax > 0.0)
                lines.append(
                    f"{a:.3f} {keep_frac:.2f} {bw_mult:.1f} {float(np.mean(detected)):.3f} "
                    f"{float(np.mean(maxes)):.6f}"
                )
    lines.append(
        "\nInterpretation: a centered mask of only about 1/8 of the tested height interval hides "
        "the whole off-line positive core. Random masks usually detect it at high coverage, but "
        "adversarial or structured masks can create a false positivity pass. APEX-B numerics need "
        "height-coverage certificates for sparse no-margin defects."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("THE-MACHINE tick: survey masks -> APEX-B faithful positivity")
    out.append(f"NODE: {NODE}")
    out.append(f"Standing-order target: {TARGET}")
    out.append(f"STEP 9 method: {METHOD}")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
