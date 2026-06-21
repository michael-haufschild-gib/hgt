#!/usr/bin/env python3
"""R49 candidate: annular boundary-layer passport for contour moments.

ResearchNode 10: Certified contour-moment calculus v1.0.

NODE: hydrodynamic boundary-layer thickness controls transport into and out of
biofilms.

Transfer: contour moments M_k/D2/kappa need an annular guard-band certificate.
If a source sits in the contour boundary layer, tiny contour-thickness/radius
changes flip the enclosed moment data even with accurate quadrature.
"""

from __future__ import annotations

import cmath
import math

import numpy as np


NODE = "hydrodynamic boundary-layer thickness and its effect on transport into and out of the biofilm"


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_boundary_layer_test() -> None:
    bulk = 1.0
    diffusivity = 1.0
    surface_k = 2.0
    print("NODE boundary-layer flux test")
    print("delta flux relative_to_delta_0.02")
    base = None
    for delta in [0.02, 0.05, 0.10, 0.20, 0.50]:
        flux = bulk / (delta / diffusivity + 1.0 / surface_k)
        if base is None:
            base = flux
        print(f"{delta:.3f} {flux:.6f} {flux / base:.3f}")
    print(
        "NODE verdict: same bulk concentration and surface kinetics give very "
        "different flux when the boundary-layer thickness changes."
    )


def moment_circle(sources: list[complex], radius: float, k: int, n: int = 4096) -> complex:
    theta = np.linspace(0.0, 2.0 * math.pi, n, endpoint=False)
    z = radius * np.exp(1j * theta)
    logderiv = np.zeros_like(z)
    for rho in sources:
        logderiv += 1.0 / (z - rho)
    # (1/2πi)∮ z^k f'/f dz on z=R exp(iθ): mean z^(k+1) f'/f.
    return complex(np.mean((z ** (k + 1)) * logderiv))


def true_moment(sources: list[complex], radius: float, k: int) -> complex:
    return sum(rho**k for rho in sources if abs(rho) < radius)


def transfer_audit() -> None:
    attempts = [
        "contour moments need an annular boundary-layer guard passport",
        "M_k calculus must certify source clearance from contour boundary",
        "biofilm boundary thickness becomes contour collar admissibility",
    ]
    print()
    print("STEP8 transfer attempts by Levenshtein distance")
    for text in sorted(attempts, key=lambda item: levenshtein(NODE, item)):
        print(f"distance={levenshtein(NODE, text):3d}  {text}")

    print()
    print("STEP9 method #16: minimal counterexample")
    print("one stable interior source plus one source in the contour boundary layer")

    cases = {
        "clear_annulus": [0.20 + 0.05j, 0.70 + 0.00j],
        "boundary_layer": [0.20 + 0.05j, 0.995 + 0.00j],
    }
    radii = [0.970, 0.990, 1.000, 1.010, 1.030]

    print()
    print("HGT transfer: contour-moment annular guard-band audit")
    print("case radius clearance M0_num M0_true M1_num_real M1_true_real abs_M1_error")
    for name, sources in cases.items():
        for radius in radii:
            clearance = min(abs(radius - abs(rho)) for rho in sources)
            m0 = moment_circle(sources, radius, 0)
            m1 = moment_circle(sources, radius, 1)
            t0 = true_moment(sources, radius, 0)
            t1 = true_moment(sources, radius, 1)
            print(
                f"{name:14s} {radius:.3f} {clearance:.5f} "
                f"{m0.real:.6f} {t0.real:.0f} {m1.real:.6f} {t1.real:.6f} "
                f"{abs(m1 - t1):.3e}"
            )

    print()
    print("Summary gates")
    for name, sources in cases.items():
        true_m0s = [round(true_moment(sources, radius, 0).real) for radius in radii]
        true_m1s = [true_moment(sources, radius, 1).real for radius in radii]
        print(
            f"{name:14s} unique_M0={sorted(set(true_m0s))} "
            f"M1_range={max(true_m1s) - min(true_m1s):.6f}"
        )
    print(
        "passport_rule=certified contour moments must include an annular "
        "source-clearance bound; quadrature accuracy alone is not admissibility"
    )


def main() -> None:
    print("Penrose R49: contour boundary-layer passport")
    print(f"NODE: {NODE}")
    node_boundary_layer_test()
    transfer_audit()


if __name__ == "__main__":
    main()
