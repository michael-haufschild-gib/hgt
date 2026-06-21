#!/usr/bin/env python3
"""NODE test: alternans / period-doubling before propagation failure.

NODE:
    Alternans or period-doubling before overt propagation failure.

Constraint:
    In an excitable medium with restitution, a 1:1 propagated response can
    become unstable to alternating large/small responses before outright
    conduction block. Alternans is a precursor state distinct from failure.
"""

from __future__ import annotations

import argparse

import numpy as np


def iterate(pacing: float, slope: float, beats: int = 240) -> dict[str, float]:
    apd = 0.55
    responses = []
    blocked = []
    for _ in range(beats):
        di = pacing - apd
        if di <= 0.06:
            blocked.append(True)
            apd = 0.20
            responses.append(0.0)
            continue
        blocked.append(False)
        next_apd = 0.24 + slope * di / (0.18 + di)
        responses.append(next_apd)
        apd = 0.72 * next_apd + 0.28 * apd
    tail = np.asarray(responses[-80:])
    block_frac = float(np.mean(blocked[-80:]))
    even = tail[::2]
    odd = tail[1::2]
    alternans = float(abs(np.mean(even) - np.mean(odd)))
    return {
        "pacing": pacing,
        "slope": slope,
        "block_frac": block_frac,
        "alternans_amp": alternans,
        "tail_mean": float(np.mean(tail)),
        "period2": float(alternans > 0.015 and block_frac < 0.20),
        "failure": float(block_frac >= 0.20),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    args = parser.parse_args()

    print("NODE: alternans before propagation failure")
    print("pacing slope block_frac alternans_amp tail_mean period2 failure")
    for slope in [0.30, 0.50, 0.70, 0.95, 1.25]:
        for pacing in [0.42, 0.50, 0.58, 0.68, 0.80, 0.95]:
            out = iterate(pacing, slope)
            print(
                f"{out['pacing']:.2f} {out['slope']:.2f} {out['block_frac']:.6f} "
                f"{out['alternans_amp']:.6f} {out['tail_mean']:.6f} "
                f"{int(out['period2'])} {int(out['failure'])}"
            )
    print(
        "\nInterpretation key: period2=1 with failure=0 is the precursor window: "
        "alternation without overt propagation block."
    )


if __name__ == "__main__":
    main()
