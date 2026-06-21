#!/usr/bin/env python3
"""NODE test: allometric exponents depend on included range and stage.

NODE:
    The fitted allometric exponent often changes with the taxonomic range,
    body-size range, and life stage included in the dataset.

Constraint:
    A claimed allometric exponent is not a property of the trait alone unless
    it is stable under biologically meaningful dataset restrictions.
"""

from __future__ import annotations

import numpy as np


SEED = 20260621


def fit_slope(x: np.ndarray, y: np.ndarray) -> float:
    return float(np.polyfit(x, y, 1)[0])


def simulate_dataset(
    rng: np.random.Generator,
    heterogeneous: bool,
    slope_spread: float = 1.0,
    shared_offsets: bool = False,
) -> dict[str, np.ndarray]:
    clades = [
        ("micro", -3.0, 0.0, 0.68, -0.35, 220),
        ("meso", -0.6, 2.0, 0.75, 0.00, 260),
        ("large", 1.0, 5.0, 0.88, 0.45, 220),
    ]
    xs: list[np.ndarray] = []
    ys: list[np.ndarray] = []
    clade_labels: list[str] = []
    stage_labels: list[str] = []
    for clade, lo, hi, base_slope, intercept, n in clades:
        for stage, stage_shift, stage_slope_shift, frac in [
            ("juvenile", -0.20, 0.18, 0.35),
            ("adult", 0.10, 0.00, 0.65),
        ]:
            m = int(n * frac)
            x = rng.uniform(lo, hi, size=m)
            if heterogeneous:
                slope = 0.75 + slope_spread * (base_slope - 0.75) + (stage_slope_shift if stage == "juvenile" else 0.0)
            else:
                slope = 0.75
            local_intercept = 0.0 if shared_offsets else intercept
            local_stage_shift = 0.0 if shared_offsets else stage_shift
            y = local_intercept + local_stage_shift + slope * x + rng.normal(0.0, 0.18, size=m)
            xs.append(x)
            ys.append(y)
            clade_labels.extend([clade] * m)
            stage_labels.extend([stage] * m)
    return {
        "x": np.concatenate(xs),
        "y": np.concatenate(ys),
        "clade": np.asarray(clade_labels),
        "stage": np.asarray(stage_labels),
    }


def subset_slopes(data: dict[str, np.ndarray]) -> dict[str, float]:
    x = data["x"]
    y = data["y"]
    clade = data["clade"]
    stage = data["stage"]
    rows: dict[str, float] = {"all": fit_slope(x, y)}
    for label in ["micro", "meso", "large"]:
        mask = clade == label
        rows[f"clade_{label}"] = fit_slope(x[mask], y[mask])
    for label in ["juvenile", "adult"]:
        mask = stage == label
        rows[f"stage_{label}"] = fit_slope(x[mask], y[mask])
    qs = np.quantile(x, [0.0, 0.33, 0.67, 1.0])
    for i, (lo, hi) in enumerate(zip(qs[:-1], qs[1:]), start=1):
        mask = (x >= lo) & (x <= hi)
        rows[f"size_tertile_{i}"] = fit_slope(x[mask], y[mask])
    return rows


def print_rows(name: str, rows: dict[str, float]) -> None:
    vals = np.asarray(list(rows.values()), dtype=float)
    print(f"\nMODEL {name}: all={rows['all']:.4f} slope_range={float(np.max(vals)-np.min(vals)):.4f} slope_sd={float(np.std(vals)):.4f}")
    for key in sorted(rows):
        print(f"{key:16s} {rows[key]:8.4f}")


def sweep(rng: np.random.Generator) -> None:
    print("\nSLOPE HETEROGENEITY SWEEP")
    print("spread all_slope subset_range subset_sd juvenile adult micro meso large")
    for spread in [0.0, 0.25, 0.50, 0.75, 1.00, 1.25]:
        data = simulate_dataset(rng, heterogeneous=True, slope_spread=spread)
        rows = subset_slopes(data)
        vals = np.asarray(list(rows.values()), dtype=float)
        print(
            f"{spread:5.2f} {rows['all']:9.4f} {float(np.max(vals)-np.min(vals)):12.4f} {float(np.std(vals)):9.4f} "
            f"{rows['stage_juvenile']:8.4f} {rows['stage_adult']:8.4f} "
            f"{rows['clade_micro']:8.4f} {rows['clade_meso']:8.4f} {rows['clade_large']:8.4f}"
        )


def main() -> None:
    rng = np.random.default_rng(SEED)
    print("NODE: allometric exponent sensitivity to taxonomic range, body-size range, and life stage")
    print(f"seed={SEED}")
    print("criterion: a clean universal-slope null should be stable; biological offsets and slope heterogeneity should make subset-dependent fits")

    universal = simulate_dataset(rng, heterogeneous=False, shared_offsets=True)
    offset_mixture = simulate_dataset(rng, heterogeneous=False, shared_offsets=False)
    heterogeneous = simulate_dataset(rng, heterogeneous=True, slope_spread=1.0)
    print_rows("clean_universal_slope_control", subset_slopes(universal))
    print_rows("universal_slope_with_offsets", subset_slopes(offset_mixture))
    print_rows("heterogeneous_clade_stage", subset_slopes(heterogeneous))
    sweep(rng)


if __name__ == "__main__":
    main()
