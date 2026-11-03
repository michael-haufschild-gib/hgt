# Joint pole payment extends the critical ratio

- **ID:** joint-pole-payment-extends-the-critical-ratio
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [critical-ratio continuation](../1-in-progress/critical-ratio-continuation.md)

For p>1 and a compact C² window test H supported in [-A,0], put

    B_p(H) = ∫ exp(-py) H(y)² dy,
    d(p) = 1/(sqrt(p+1) sqrt(p-1)) − 1/p,
    Cjoint(p) = |gammaBracket(0)| + 2 exponentialPrimeMass(p) + d(p).

The complete Weil form satisfies Q(H)≥−Cjoint(p) B_p(H), independently
of aperture A. The pole cost d(p) is positive and strictly smaller than
the previous separate-moment cost 1/(p+1)+1/(p−1).

For the tilted spline, let aφ=(∫φ)²/∫φ² and J=tiltedJordanOne. Then

    Rjoint = 7J/(aφ Cjoint(8)) > Rold = 7J/(aφ Cold(8)) > 0.

Every compact profile has nonnegative compensated limit for 0<R≤Rjoint.
Every independent finite window family has a strictly positive pencil
for 0<R<Rjoint, and eventually a strictly positive horizon Gram along
each critical schedule c_N⁸/log N→R. That horizon threshold may depend
on the family and schedule. The midpoint (Rold+Rjoint)/2 gives an explicit
ratio beyond the old natural weighted-floor threshold.

The proof keeps the Gram correlation of the two Laplace moments. In the
B_p norm their unit representing vectors have inner product
sqrt(p+1)sqrt(p−1)/p. Cauchy–Schwarz on their difference, together with
nonnegativity of the complementary square, bounds the complete pole
product below by −d(p) B_p(H). The existing prime, diagonal and
archimedean-jump bounds give the complete floor; polarization and
finite-dimensional limit inheritance give the matrix statements.

Lean sources:

- `WindowTowerOfSpecZ/TheAliasingNormRetainsTheJointPole.lean`:
  `laplacePair_sq_le_exponentialMass`, `pole_ge_neg_jointExponentialMass`,
  `weilQuad_ge_neg_jointExponentialMass`.
- `ArithmeticHodgeTheoryOfDegenerations/JointPolePaymentExtendsTheCriticalRatio.lean`:
  `separatePoleCriticalRatio_lt_joint`,
  `tilted_secondOrderLimit_nonneg_below_jointPoleCriticalRatio`,
  `exists_larger_critical_ratio_for_all_window_pencils`,
  `tilted_horizonGram_posDef_below_jointPoleCriticalRatio`.

Kernel checks passed; the displayed theorem audits report exactly
`[propext, Classical.choice, Quot.sound]`. Both modules are wired into
their programme umbrellas; no umbrella was compiled.

**Scope:** a bounded-range bridge. It does not remove compensation,
give a larger whole-space critical band, compare Rjoint with the
independently constructed whole-space threshold, or reach unbounded R.
The pole calculation is elementary; no claim of scientific novelty
beyond the local corpus audit is made.
