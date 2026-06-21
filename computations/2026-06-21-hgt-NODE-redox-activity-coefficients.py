#!/usr/bin/env python3
import math


def davies_log_gamma(z, ionic_strength):
    root = math.sqrt(ionic_strength)
    return -0.51 * z * z * (root / (1.0 + root) - 0.3 * ionic_strength)


def potential(oxidized, reduced, z_ox, z_red, ionic_strength, n=1):
    ideal = math.log(oxidized / reduced) / n
    log_g_ox = davies_log_gamma(z_ox, ionic_strength)
    log_g_red = davies_log_gamma(z_red, ionic_strength)
    activity = math.log(oxidized / reduced) + math.log(10.0) * (log_g_ox - log_g_red)
    return ideal, activity / n


def main():
    print("NODE: activity coefficients shift redox potential away from concentration ratio")
    print("I z_ox z_red ideal_potential activity_potential shift")
    for ionic in [0.001, 0.01, 0.05, 0.10, 0.50, 1.00]:
        for z_ox, z_red in [(1, 0), (2, 1), (3, 2), (2, -1)]:
            ideal, active = potential(0.8, 0.2, z_ox, z_red, ionic)
            print(f"{ionic:.3f} {z_ox:4d} {z_red:5d} {ideal:.6f} {active:.6f} {active-ideal:.6f}")


if __name__ == "__main__":
    main()
