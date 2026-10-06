# Nested-order zero separation of minimal Toeplitz eigenpolynomials: a positivity detector

**Question.** The CCM ground states of the restricted Weil form satisfy a Sturm-type separation law in
the aperture (loop row 501): between consecutive zeros at aperture a there is a zero at every a' > a.
Is this a general Toeplitz fact, which feature produces it, and does it survive loss of positivity?

**Model.** Discrete analogue (double precision, numpy):
- Hermitian Toeplitz matrices `T_n = (c_{j−k})` from moments of a measure on the circle, orders n = 4…41 (sep, sep2) or 4…61 (sep3);
- the eigenpolynomial of the minimal eigenvalue (zeros on |z| = 1 by Delsarte–Genin–Kamp when simple);
- check: between cyclically consecutive zero-arguments of `p_n` lies a zero-argument of `p_{n'}`, n < n'.

**Results.**

| measure (30–40 seeds each) | violations / order pairs |
|---|---|
| random atoms (60, non-symmetric) | 121 / 3120 |
| random smooth positive density | 135 / 3120 |
| symmetric random atoms on (0.05, π) | 165 / 2340 |
| zeta-like atoms, density 2(1+6t), **no gap** at 0 | 189 / 2340 |
| zeta-like, **gap** (−0.3, 0.3) | 0 / 2340 (also 0 / 3120 in sep.py) |
| gap + decreasing density | 0 / 2340 |
| gap + uniform spacing | 0 / 2340 |
| gap + random weights | 0 / 2340 |
| gap, asymmetric | 0 / 2340 |
| smooth density 1 + α(1 − cos θ) (minimum at 0) | 0 / 2340 |

The responsible feature is a gap (or minimum) of the spectral measure at θ = 0. Symmetry, density profile and weights are irrelevant. The minimal eigenvector concentrates in the gap, and its zeros sample the support.

**Loss of positivity** (sep3: gapped zeta-like atoms plus one off-line pair `t₀ ± id` and mirror):
- With d = 0.1 the minimal eigenvalue turns negative at order n_c = 38 (t₀ = 1.5) or 44 (t₀ = 2.5).
- Zeros remain on the unit circle (error ≤ 1e-12).
- Separation holds for all pairs below n_c (0 violations). It fails for pairs above n_c (3–4 of 66, and 7 of 36), and for some pairs straddling it (t₀ = 2.5: 5–7 of 180).
- For d ≤ 0.05 contact is not reached by n = 60, and there are no violations.

**Interpretation.**
- Unit-circle (real) zeros are positivity-blind; nested-order separation is not.
- For ζ, the unconditional zero-free window |γ| < 14.13 is the gap. Under RH the zeta spectral measure is positive and gapped, and the CCM separation law (row 501) is the gap phenomenon. Under ¬RH, separation is expected to fail once the first off-line pair is resolved.
- Conjecture (C502): CCM separation for all apertures ⟺ RH. Separation is a zero-flow reformulation that does not involve the sign of the energy.
