#!/usr/bin/env python3
"""
Attempt 6 NODE experiment.

NODE: sex bias in rare X/Y variants and sex-biased phenotypes.

Constraint tested:
  Rare-variant effect estimates must model sex/dosage/baseline strata.  Pooled
  estimates can hide or invert stratum-specific effects when carrier rates and
  phenotype baselines differ across strata.
"""

from __future__ import annotations

import numpy as np


def make_counts(
    n_male: int,
    n_female: int,
    p_carrier_male: float,
    p_carrier_female: float,
    base_male: float,
    base_female: float,
    effect_male: float,
    effect_female: float,
    seed: int,
) -> dict[str, np.ndarray]:
    rng = np.random.default_rng(seed)
    sex = np.r_[np.ones(n_male, dtype=int), np.zeros(n_female, dtype=int)]
    carrier = np.r_[
        rng.random(n_male) < p_carrier_male,
        rng.random(n_female) < p_carrier_female,
    ].astype(int)
    risk = np.where(sex == 1, base_male, base_female)
    risk += np.where(sex == 1, effect_male * carrier, effect_female * carrier)
    risk = np.clip(risk, 0.001, 0.999)
    phenotype = (rng.random(n_male + n_female) < risk).astype(int)
    return {"sex": sex, "carrier": carrier, "phenotype": phenotype}


def risk_difference(mask: np.ndarray, carrier: np.ndarray, phenotype: np.ndarray) -> tuple[float, int, int]:
    c = mask & (carrier == 1)
    n = mask & (carrier == 0)
    if c.sum() == 0 or n.sum() == 0:
        return float("nan"), int(c.sum()), int(n.sum())
    return float(phenotype[c].mean() - phenotype[n].mean()), int(c.sum()), int(n.sum())


def summarize(label: str, data: dict[str, np.ndarray]) -> None:
    sex = data["sex"]
    carrier = data["carrier"]
    phenotype = data["phenotype"]
    pooled = np.ones_like(sex, dtype=bool)
    male = sex == 1
    female = sex == 0
    print(label)
    for name, mask in [("pooled", pooled), ("male", male), ("female", female)]:
        rd, c, n = risk_difference(mask, carrier, phenotype)
        print(f"  {name:6s}: risk-diff={rd:+.4f}, carriers={c}, noncarriers={n}")
    print(
        f"  carrier male share={sex[carrier == 1].mean():.3f}; "
        f"population male share={sex.mean():.3f}"
    )
    print()


def main() -> None:
    print("RARE-VARIANT EFFECT: POOLED VS SEX-STRATIFIED")
    print()
    data = make_counts(
        n_male=60000,
        n_female=60000,
        p_carrier_male=0.010,
        p_carrier_female=0.001,
        base_male=0.08,
        base_female=0.20,
        effect_male=0.08,
        effect_female=0.08,
        seed=11,
    )
    summarize("same positive effect in each stratum, carrier-rate imbalance", data)

    data = make_counts(
        n_male=60000,
        n_female=60000,
        p_carrier_male=0.015,
        p_carrier_female=0.001,
        base_male=0.05,
        base_female=0.28,
        effect_male=0.10,
        effect_female=0.10,
        seed=12,
    )
    summarize("stronger baseline imbalance: pooled effect diluted by composition", data)


if __name__ == "__main__":
    main()
