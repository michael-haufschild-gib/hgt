#!/usr/bin/env python3
"""Workflow test for GA2 through coordinate artifacts in information geometry.

ResearchNode formula:
    psi(s/2 + 1) = psi(s/2) + 2/s

Random NODE:
    Difference between parametric coordinate artifacts and coordinate-invariant
    geometric quantities.
"""

from __future__ import annotations

import mpmath as mp


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, start=1):
        cur = [i]
        for j, cb in enumerate(b, start=1):
            cur.append(
                min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb))
            )
        prev = cur
    return prev[-1]


def main() -> None:
    mp.mp.dps = 80
    base_test = "separate coordinate artifact from coordinate invariant geometry"
    attempts = [
        ("A", "separate half-coordinate 2/s artifact from unit-step digamma recurrence"),
        ("B", "separate gamma multiplier log-derivative from parameter s artifact"),
        ("C", "separate Fisher metric coordinate terms from invariant recurrence residue"),
    ]
    print("STEP 8 Levenshtein transfer attempts")
    print("=" * 42)
    scored = [(tag, levenshtein(base_test, text), text) for tag, text in attempts]
    for tag, score, text in scored:
        print(f"{tag}: distance={score}, attempt={text}")
    chosen = min(scored, key=lambda row: row[1])
    print(f"chosen={chosen[0]} by minimum distance")
    print()

    print("NODE model: Fisher information changes coordinates by pullback")
    print("=" * 62)
    theta = mp.mpf("1.7")
    # Exponential(rate theta): Fisher in theta is 1/theta^2.
    fisher_theta = 1 / theta**2
    # Coordinate phi=log(theta): pullback metric is I_theta*(dtheta/dphi)^2 = 1.
    fisher_phi = fisher_theta * theta**2
    print(f"I(theta)=1/theta^2 at theta={theta}: {mp.nstr(fisher_theta, 12)}")
    print(f"I(phi=log theta) via pullback: {mp.nstr(fisher_phi, 12)}")
    print("The component changes; the line element is the invariant object.")
    print()

    print("STEP 9 method 8: similar scaled-coordinate digamma recurrences")
    print("=" * 70)
    s = mp.mpc("0.73", "4.2")
    for a in [1, 2, 3, 5]:
        lhs = mp.digamma(s / a + 1) - mp.digamma(s / a)
        coord_term = a / s
        invariant = (1 / a) * lhs
        multiplier_log_deriv = 1 / s
        print(
            f"a={a}: psi(s/a+1)-psi(s/a)={mp.nstr(lhs, 18)}, "
            f"a/s={mp.nstr(coord_term, 18)}, "
            f"(1/a)diff={mp.nstr(invariant, 18)}, "
            f"1/s={mp.nstr(multiplier_log_deriv, 18)}, "
            f"err={mp.nstr(abs(invariant-multiplier_log_deriv), 5)}"
        )

    print()
    print("Interpretation:")
    print(
        "The coefficient 2/s in GA2 is the s-coordinate expression of the "
        "unit-step recurrence in z=s/2. The invariant archimedean compatibility "
        "is already the log-derivative of the Gamma_R shift multiplier: "
        "1/2*(psi(s/2+1)-psi(s/2)) = d_s log(s/2pi) = 1/s."
    )


if __name__ == "__main__":
    main()
