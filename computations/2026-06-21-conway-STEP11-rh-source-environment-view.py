#!/usr/bin/env python3
"""STEP 11 viewpoint change for genotype degeneracy -> RH Translation.

Change the viewpoint from source-centered equivalence to environment-centered
explanation. If the "same source mass but different neighborhood" effect is
mostly predicted by nearby zero spacing, it reduces to known local source
geometry rather than a new RH Translation constraint.
"""

from __future__ import annotations

import itertools
import runpy

import numpy as np


BASE = runpy.run_path("computations/2026-06-21-conway-genotype-degeneracy-rh-translation.py")

zeta_zero_heights = BASE["zeta_zero_heights"]
rh_signature = BASE["rh_signature"]


def neighbor_model_signature(index: int, heights: list[float]) -> np.ndarray:
    t = heights[index]
    rho = complex(0.5, t)
    residual_mags = []
    left_right = []
    up_down = []
    for r in [0.025, 0.05, 0.1]:
        values = {}
        for name, dz in {
            "right": complex(r, 0),
            "left": complex(-r, 0),
            "up": complex(0, r),
            "down": complex(0, -r),
        }.items():
            s = rho + dz
            residual = 0j
            # Change viewpoint: only the neighboring source environment, not
            # the central source, is allowed to explain the residual.
            for j, tj in enumerate(heights):
                if j == index:
                    continue
                distance_rank = abs(j - index)
                if distance_rank <= 4:
                    residual += 1 / (s - complex(0.5, tj))
            values[name] = abs(residual)
            residual_mags.append(values[name])
        left_right.append(abs(values["right"] - values["left"]))
        up_down.append(abs(values["up"] - values["down"]))

    arr = np.array(residual_mags, dtype=float)
    return np.array(
        [
            float(np.mean(arr)),
            float(np.std(arr)),
            float(np.mean(left_right)),
            float(np.mean(up_down)),
            float(max(arr)),
        ],
        dtype=float,
    )


def pairwise(values: list[np.ndarray]) -> np.ndarray:
    return np.array(
        [float(np.linalg.norm(a - b)) for a, b in itertools.combinations(values, 2)],
        dtype=float,
    )


def corr(a: np.ndarray, b: np.ndarray) -> float:
    if np.std(a) == 0 or np.std(b) == 0:
        return float("nan")
    return float(np.corrcoef(a, b)[0, 1])


def main() -> None:
    heights = zeta_zero_heights(16)
    # Use interior zeros so left/right neighbor environment is well-defined.
    indices = list(range(2, 14))
    completed_rows = [rh_signature(heights[i]) for i in indices]
    completed = [r["signature"] for r in completed_rows]
    neighbor = [neighbor_model_signature(i, heights) for i in indices]

    completed_mean = np.array([x[0] for x in completed], dtype=float)
    neighbor_mean = np.array([x[0] for x in neighbor], dtype=float)
    completed_ud = np.array([x[3] for x in completed], dtype=float)
    neighbor_ud = np.array([x[3] for x in neighbor], dtype=float)

    left_gap = np.array([heights[i] - heights[i - 1] for i in indices], dtype=float)
    right_gap = np.array([heights[i + 1] - heights[i] for i in indices], dtype=float)
    gap_intensity = 1 / left_gap + 1 / right_gap

    print("STEP 11 METHOD 4: CHANGE THE VIEWPOINT")
    print(
        "Viewpoint change: source-centered non-equivalence -> neighboring-source "
        "environment explanation."
    )
    print(
        "Question: are equal-source neighborhood differences mostly predicted "
        "by nearby zero spacing, hence reducible to local source geometry?"
    )
    print()
    for label, i, comp, neigh, lg, rg in zip(
        [f"zero={i + 1:02d}" for i in indices],
        indices,
        completed,
        neighbor,
        left_gap,
        right_gap,
    ):
        print(
            f"{label} t={heights[i]:.6f} gaps=L{lg:.4f}/R{rg:.4f} "
            f"completed_mean={comp[0]:.5g} neighbor_mean={neigh[0]:.5g} "
            f"completed_ud={comp[3]:.5g} neighbor_ud={neigh[3]:.5g}"
        )

    print()
    print(f"corr(completed_mean, neighbor_mean)={corr(completed_mean, neighbor_mean):.5f}")
    print(f"corr(completed_ud, neighbor_ud)={corr(completed_ud, neighbor_ud):.5f}")
    print(f"corr(completed_mean, gap_intensity)={corr(completed_mean, gap_intensity):.5f}")
    print(
        "pairwise_distance_corr(completed_signature, neighbor_signature)="
        f"{corr(pairwise(completed), pairwise(neighbor)):.5f}"
    )
    print()
    print(
        "Interpretation: if correlations are high, the false missing lemma is "
        "not new RH Translation content. It says equal unit source mass does "
        "not erase the surrounding source environment, which is already the "
        "local pole/source-measure picture."
    )


if __name__ == "__main__":
    main()
