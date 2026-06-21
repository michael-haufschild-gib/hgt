#!/usr/bin/env python3
"""NODE test: heat release coupled to autocatalytic concentration growth.

NODE:
    Heat release and concentration growth are coupled, so thermal runaway and
    chemical autocatalysis can amplify each other.

Constraint:
    The runaway is not just concentration growth and not just heating. The
    reaction rate raises temperature, temperature raises the reaction rate, and
    cooling competes with this coupled positive feedback.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def simulate(seed: float, heat_loss: float, beta: float, coupled: bool, steps: int = 900, dt: float = 0.01) -> dict[str, float]:
    c = seed
    temp = 0.0
    runaway_t = -1
    max_rate = 0.0
    for t in range(steps):
        temp_factor = math.exp(beta * temp) if coupled else 1.0
        rate = temp_factor * c * (1.0 - c)
        c += dt * rate
        temp += dt * (1.7 * rate - heat_loss * temp)
        c = min(max(c, 0.0), 1.0)
        max_rate = max(max_rate, rate)
        if runaway_t < 0 and c > 0.70 and temp > 0.45:
            runaway_t = t
    return {
        "seed": seed,
        "heat_loss": heat_loss,
        "beta": beta,
        "coupled": float(coupled),
        "runaway": float(runaway_t >= 0),
        "runaway_t": float(runaway_t),
        "final_c": float(c),
        "final_temp": float(temp),
        "max_rate": float(max_rate),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    args = parser.parse_args()

    print("NODE: thermal/autocatalytic positive feedback coupling")
    print("seed heat_loss beta coupled runaway runaway_t final_c final_temp max_rate")
    for seed in [0.005, 0.015, 0.035]:
        for loss in [0.8, 1.2, 1.8, 2.6]:
            for beta in [0.0, 1.0, 2.0]:
                coupled = beta > 0.0
                out = simulate(seed, loss, beta, coupled)
                print(
                    f"{out['seed']:.3f} {out['heat_loss']:.2f} {out['beta']:.1f} {int(out['coupled'])} "
                    f"{int(out['runaway'])} {out['runaway_t']:.0f} {out['final_c']:.6f} "
                    f"{out['final_temp']:.6f} {out['max_rate']:.6f}"
                )
    print(
        "\nInterpretation key: coupled beta should move cases from no-runaway "
        "or late runaway into earlier runaway when heat loss is not too high."
    )


if __name__ == "__main__":
    main()
