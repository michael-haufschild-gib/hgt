# Theta-cusp two-channel Robertson certificate

- **ID:** theta-cusp-two-channel-robertson-certificate
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Trifonov--Donev characteristic uncertainty relations, arXiv:quant-ph/9809026; formal theta-cusp radial state
- **Statement:** The upper first-radial moment inequality follows if one linear combination of the dilation and quadratic-monomial Stein generators satisfies the source energy-response certificate; the existing quadratic-field certificate is one witness.

## Goal

Replace the single fixed generator hypothesis by a variational two-channel hypothesis that can be optimized using the finite source moments.  The result must feed the existing first-radial and prime--archimedean Hankel consumers without changing their conclusions.

## Gates

- [x] 0 → 1 in-progress: source-pure two-channel score family and exact Gram-determinant attack
- [x] 1 → 2 fully-proven: Gram determinant, source integrability, boundary currents, and moment response closed
- [x] 2 → 3 formalized: module builds, standard axioms only, formal lint passes
- [ ] 3 → 4 publication-ready: standalone theorem, physics provenance, and Lean certificate

## Approach

Use the two generator fields `x` and `x^2`.  Their linear combinations contain the existing field `x-x^2/2`.  The three-vector Gram determinant is the two-channel Robertson inequality.  For each linear combination, the Stein integration-by-parts law converts its response to a finite source-moment value, and Cauchy--Schwarz converts an energy-response certificate into the existing upper first-radial moment inequality.

## Formal result

`HTGeometry.twoChannelRobertsonGram` and `HTGeometry.twoChannelIntegralRobertson` formalize the reusable multi-observable determinant.  `RHTower.thetaCuspFirstRadialTwoChannelRobertsonGram` specializes it to the dilation and quadratic-monomial score channels.  `RHTower.thetaCuspFirstRadialTwoChannelSteinCoupling_eq_moments` gives the exact finite response `a M2 + b M3`.  `RHTower.twoChannelSteinEnergyCertificate_of_quadraticSteinEnergyCertificate` proves that the old fixed certificate supplies the witness `(1,-1/2)`.  `RHTower.thetaCusp_firstRadial_upper_of_twoChannelSteinEnergyCertificate` and `RHTower.forall_primeArchSourceTraceHankel_linear_nonneg_of_twoChannelSteinEnergy` wire the weaker existential certificate into the existing consumers.  `RHTower.riemannHypothesis_of_twoChannelSteinEnergy_of_primeArchDegreeTwoTail` directly reaches the corpus RH interface; its remaining assumptions are the unchanged relaxed theta condition and the integer-polynomial Hankel tail of degree at least two.

## Remaining research target

Discharge the variational certificate by bounding or exactly reducing the `2×2` score-energy matrix.  The third radial power moment is now an explicit response coordinate rather than an implicit integral.
