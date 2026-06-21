#!/usr/bin/env python3
"""THE-MACHINE NODE test: enzyme crowding can block active-site access.

NODE:
    Enzyme crowding can promote nonspecific interactions that reduce active-site
    accessibility.

Constraint tested:
    Condensate enrichment/effective molarity is not equivalent to usable
    catalytic activity. Increasing crowding can raise local enzyme density while
    reducing diffusion and active-site accessibility through nonspecific
    interactions, producing an optimum and then decline.
"""

from __future__ import annotations

import argparse
import numpy as np


def model(crowding: np.ndarray, nonspecific_strength: float) -> dict[str, np.ndarray]:
    enrichment = 1.0 + 6.0 * crowding / (1.0 + crowding)
    diffusion = 1.0 / (1.0 + 0.22 * crowding**1.4)
    accessibility = 1.0 / (1.0 + nonspecific_strength * crowding**2.2)
    rate = enrichment * diffusion * accessibility
    return {
        "enrichment": enrichment,
        "diffusion": diffusion,
        "accessibility": accessibility,
        "rate": rate,
    }


def first_decrease(values: np.ndarray) -> int:
    diffs = np.diff(values)
    hits = np.flatnonzero(diffs < 0)
    return int(hits[0] + 1) if hits.size else -1


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--points", type=int, default=81)
    args = parser.parse_args()

    crowding = np.linspace(0.0, 8.0, args.points)
    print("NODE: condensate crowding enrichment versus active-site accessibility")
    print(f"points={args.points}")
    print("strength optimum_crowding max_rate rate_at_high enrichment_high accessibility_high first_rate_decrease monotone_enrichment monotone_accessibility_decrease")
    for strength in [0.0, 0.04, 0.10, 0.22, 0.45, 0.90]:
        row = model(crowding, strength)
        idx = int(np.argmax(row["rate"]))
        monotone_enrichment = int(np.all(np.diff(row["enrichment"]) >= -1e-12))
        monotone_access_down = int(np.all(np.diff(row["accessibility"]) <= 1e-12))
        print(
            f"{strength:8.2f} {crowding[idx]:16.3f} {row['rate'][idx]:8.5f} "
            f"{row['rate'][-1]:12.5f} {row['enrichment'][-1]:15.5f} "
            f"{row['accessibility'][-1]:18.5f} {first_decrease(row['rate']):19d} "
            f"{monotone_enrichment:19d} {monotone_access_down:33d}"
        )

    print("\nSample curve for nonspecific_strength=0.22")
    print("crowding enrichment diffusion accessibility rate")
    row = model(crowding, 0.22)
    for idx in [0, 5, 10, 20, 30, 45, 60, 80]:
        print(
            f"{crowding[idx]:8.3f} {row['enrichment'][idx]:10.5f} "
            f"{row['diffusion'][idx]:9.5f} {row['accessibility'][idx]:13.5f} "
            f"{row['rate'][idx]:9.5f}"
        )

    print(
        "\nInterpretation: the NODE is validated if enrichment is monotone while "
        "accessibility is monotone decreasing and total rate has an optimum/decline "
        "under nonspecific interactions."
    )


if __name__ == "__main__":
    main()
