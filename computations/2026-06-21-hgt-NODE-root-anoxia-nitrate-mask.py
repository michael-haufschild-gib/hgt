#!/usr/bin/env python3
import numpy as np


def metabolism(o2, nitrate):
    aerobic = 32.0 * o2 / (0.12 + o2)
    nitrate_sink = 6.0 * nitrate / (0.20 + nitrate) * (1.0 / (1.0 + 8.0 * o2))
    redox_relief = o2 + 0.65 * nitrate_sink / 6.0
    atp = aerobic + nitrate_sink
    return atp, redox_relief, nitrate_sink


def main():
    print("NODE: nitrate can mask oxygen stress without replacing aerobic ATP")
    print("o2 nitrate ATP ATP_frac_of_oxic redox_relief nitrate_sink stress_masked energy_deficit")
    oxic_atp, _, _ = metabolism(1.0, 0.0)
    for o2 in [0.00, 0.02, 0.05, 0.10, 0.30, 1.00]:
        for nitrate in [0.0, 0.1, 0.3, 1.0, 3.0]:
            atp, redox, sink = metabolism(o2, nitrate)
            masked = float(redox > 0.45)
            deficit = float(atp < 0.55 * oxic_atp)
            print(
                f"{o2:.2f} {nitrate:.1f} {atp:.6f} {atp/oxic_atp:.6f} "
                f"{redox:.6f} {sink:.6f} {masked:.0f} {deficit:.0f}"
            )


if __name__ == "__main__":
    main()
