#!/usr/bin/env python3
import numpy as np


def normalize(density, dx):
    return density / (density.sum() * dx)


def delayed_density(source, x, tau):
    if tau == 0:
        return source.copy()
    dx = x[1] - x[0]
    u = x - x[0]
    kernel = np.exp(-u / tau) / tau
    kernel = normalize(kernel, dx)
    conv = np.convolve(source, kernel, mode="full")[: len(x)] * dx
    return normalize(conv, dx)


def mass(density, x, lo, hi):
    dx = x[1] - x[0]
    mask = (x >= lo) & (x <= hi)
    return float(density[mask].sum() * dx)


def main():
    print("NODE test: floodplains store and delay water rather than creating a new upstream source")
    print("ResearchNode mutation: bridge detection needs retention/memory mass balance")
    print()
    x = np.linspace(0.0, 1.0, 5001)
    dx = x[1] - x[0]
    source = np.exp(-0.5 * ((x - 0.24) / 0.025) ** 2)
    source = normalize(source, dx)
    local_band = (0.20, 0.28)
    far_window = (0.0, 0.80)
    print("Off-seam source at x=0.24; local detector band [0.20,0.28].")
    print("tau | local observed mass | cumulative mass to 0.80 | peak location")
    print("----|---------------------|-------------------------|--------------")
    for tau in [0.0, 0.015, 0.04, 0.08, 0.16]:
        observed = delayed_density(source, x, tau)
        peak_x = float(x[np.argmax(observed)])
        print(
            f"{tau:3.3f} | {mass(observed, x, *local_band):19.6f} | "
            f"{mass(observed, x, *far_window):23.6f} | {peak_x:12.4f}"
        )
    print()
    print("Finding:")
    print("  Retention can make a true off-seam source fail a local-band detector even while")
    print("  cumulative nested mass still certifies the source. The detection half needs a")
    print("  memory-kernel / retention passport: prove conservation across nested windows or")
    print("  deconvolve the detector, instead of treating one local shell as decisive.")


if __name__ == "__main__":
    main()
