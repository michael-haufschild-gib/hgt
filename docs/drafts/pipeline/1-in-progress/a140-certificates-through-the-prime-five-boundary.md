# Weil certificates through the prime-five boundary

- **ID:** A140-larger-apertures
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Target:** Positive Weil floors above `log(3)/2`, above `log(2)`, and
  through `log(5)/2`, uniformly in block size.

## Analytic reduction

The regional logarithmic form is diagonal in Legendre moments. Retaining
finitely many low moments reduces each parity to a weighted capacity problem;
the tail has the next harmonic gap. At these apertures the prime reflections
for `2`, `3`, and `4` must be retained together.

Immediately above `log(3)/2`, put `d₂=log(2)/a`, `d₃=log(3)/a`.
When `a<log(2)` and `d₂+2<2d₃`, a prime-three overlap component is the
four-vertex path `d₂−x, x, d₃−x, d₂−d₃+x`, with successive weights
`w₂,w₃,w₂`. Eliminating the two outer vertices leaves a two-by-two inverse;
the other components are the existing prime-two pairs. Its capacity bound
is still an open obligation.

A strict floor at `a=log(3)/2` suffices for the first new target:
`RHTower.continuous_ccmRestrictedWeilGroundEnergy` extends it to a larger
aperture. At this boundary the prime-three correlation vanishes. The exact
Gamma tail is
`Ω(log 3)=log(2+√3)/2+π/6`.
The identity and the normalized Gamma mass lower bound `−4546/2500`
are formalized in `TheGammaMassAtThePrimeThreeBoundaryIsCertified.lean`.
Direct Lean checks and transitive axiom audits passed using only
`propext`, `Classical.choice`, and `Quot.sound`.
Likewise, a strict floor at `a=log(2)` extends above the ratio-four boundary.
The prime-four term vanishes there; the prime-two/prime-three components
are still four-vertex paths, together with isolated prime-two pairs.

For the even sector, the next capacity candidate retains Legendre degrees
`0,2,4,6` and harmonic gap `H₈=761/280`. The proposed diagonal potential is
`449/500−log(1−x²)/2`. A polynomial reciprocal majorant, with `z=x²`, is
`500/449−31z/50+7z²/200−27z³/500−3z⁴/200−z⁸/10`.
Its pointwise certificate passed Lean. Reflected products are at most `4/5`
when `63/50≤x+y≤127/100`, keeping the weighted pair ratio at most `1/5`.
The three audited declarations are `primeThreeEvenReciprocal_bound`,
`primeThreeEvenPotential_le_log`, and `primeThreeEvenReciprocal_pair_bound`
in `ThePrimeThreeBoundaryHasAPolynomialReciprocalBound.lean`; their axioms
are only `propext`, `Classical.choice`, `Quot.sound`.
The proposed charges `(0.7235,6.089,5.705,3.483)` with cross charge `0.06735`
do not pass the polynomial capacity bound: its second principal minor is
negative. This rejects that coarse bound, not the actual Weil floor.
Raising the potential to `1799/2000`, reducing the cross charge to `0.06681`,
and tightening the geometric tail still leaves its second minor negative.
The next candidate retains degree eight, with harmonic gap `H₁₀`.
The four-moment capacity matrix remains unproved.

A stronger quartic Gamma reserve follows from the exact fourth correlation moment.
For a unit-window source, with full-window Legendre moments `r₀,…,r₄`, it is
`8r₀²/15+40r₀r₂/21+8r₀r₄/35+4r₂²/3−12r₁²/5−8r₁r₃/5`.
Bessel's inequality and square completions bound this by `17/10` times mass,
or `1/10` for odd sources. Scaling gives quartic lag reserves `47a⁵/10`
and `63a⁵/10` times mass, respectively. All seven transitive audits in
`WindowJumpCounts/TheQuarticLagDeficitRetainsAMassReserve.lean` passed with
only `propext`, `Classical.choice`, and `Quot.sound`. Its final plain-file
audit passed.

The Gamma comparison previously retained its polynomial moments only for
lag radius `r≤1`. The larger windows require `r≤log(5)<2`. The extension
uses, for `0<z≤1`,

`z/sinh(z) ≥ 1−z²/6+z⁴/64`,
`1/cosh(z) ≥ 1−z²/2+z⁴/7`.

Consequently the same exact Gamma remainder satisfies
`R(t)≥t³/1024+t⁴/224` for `0<t≤2`. These inequalities follow from the
existing degree-six exponential bounds and polynomial inequalities on `[0,1]`.

`retainedGammaRemainderWeight_ge_higher_lags_to_two` and
`local_gamma_terms_integrable_to_two` passed direct Lean checks and
transitive audits, with only `propext`, `Classical.choice`, `Quot.sound`.
They are in `TheGammaRemainderRetainsHigherLagsThroughRadiusTwo.lean`.

The exact decomposition, including the mean and both correlation moments,
now holds for `0<r≤2`:
`gamma_eq_logarithmic_lag_correlation_moments_and_remainder_to_two`.
Its lower-bound corollary is
`gamma_ge_logarithmic_lag_and_correlation_moments_to_two`.
Both passed direct Lean checks and standard-only transitive axiom audits in
`TheGammaComparisonRetainsItsChargesThroughRadiusTwo.lean`.

The degree-fourteen reciprocal polynomials now give a lower kernel through
`r=2`, with pointwise error at most `1/10000000` for `r≤11/10`:
`archLevySinhWeight_ge_polynomial14` and
`archLevySinhWeight_polynomial14_error` in
`TheGammaKernelHasAFourteenthOrderPolynomialLowerBound.lean`.
Direct checks and standard-only axiom audits passed. Multiplication by
degree-sixteen exponential bounds certifies the polynomial signs.

The integrated comparison `gammaPolynomialLower14_error` bounds the Gamma
energy between the retained polynomial form and that form plus
`r/5000000` times mass for `r≤11/10`. Its direct Lean check and both
transitive axiom audits passed in
`TheGammaPolynomialComparisonHasAUniformError.lean`.

The quartic primitive projection retains
`(m₀−m₂)²/3+(m₂−m₄)²/7+m₄²/11−2m₄m₆/11`, with Wirtinger cost
`π⁻²(M−m₀²−5m₂²−9m₄²)` only on residual mass.
`LatticeSectionTheory.primitive_mass_le_quartic_projection` passed its
direct Lean check and standard-only transitive axiom audit in
`WindowJumpCounts/TheQuarticProjectionRetainsThePrimitiveMass.lean`.

Three Newton updates `q↦q(2−Tq)`, with Taylor upper denominator `T`,
give kernel error at most `3/10¹⁷` throughout `0<t≤2`.
`gamma_reciprocal_newton3_errors` and `archLevySinhWeight_newton3_error`
passed direct Lean checks and standard-only transitive axiom audits in
`NewtonRefinementControlsTheGammaKernelThroughRadiusTwo.lean`.
The exact update error is `U(1/U−q)²+(T−U)q²`.

The integrated form `gammaPolynomialLowerNewton3_error` has error at most
`6r/10¹⁷` times mass for `0<r≤2`. It and
`local_gamma_remainder_sub_newton3` passed direct Lean checks and standard-only
transitive axiom audits in
`TheRefinedGammaPolynomialHasAUniformErrorThroughRadiusTwo.lean`.

## Open obligations

- Prove positive finite-moment capacities for the simultaneous prime reflections,
  including both parities. No such certificate is claimed here.
- Transfer the resulting floors to all block sizes.
