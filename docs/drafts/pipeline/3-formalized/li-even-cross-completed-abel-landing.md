# LI even-cross completed Abel landing

- **ID:** LI-CAB3
- **Stage:** 3-formalized
- **Lean module:** `GaloisForLFunctions.RHTower.LiEvenCrossCompletedAbelLanding`
- **Corpus sources:** `LiEvenCrossAllModeLaguerreClock`, `XiShiftedHardEdgeCompletedDensity`, `ReciprocalAtomTestSpaceClosure`, `LiEvenSquarePrimeGammaCrossBalanceCriterion`

## Result

For every mode `n` and every mass `a > 1/2`, Lean constructs reciprocal hard-edge lifts of the LI common-reversal pair and polarizes the completed-density identity. The Fourier reporter is exactly

`(pi*a/2) exp(-a*|xi|) Q_n(2*a*|xi|)`,

and its von-Mangoldt prime series is summable. The completed arithmetic value is the joint expression

`2*polar + arch/pi - prime/pi`.

It equals an absolutely convergent divisor sum for `a > 1/2`. A mode-uniform reciprocal-square majorant proves continuity of that divisor sum through `a = 1/2`, so the completed expression has a rigorous right limit without assigning separate critical values to divergent pieces.

Lean then proves the exact endpoint normalization

`Re(divisorValue_(n,1/2)) = Re(liPrimeArchEvenSquareSource_n) / 8`

and the closed capstone

`RiemannHypothesis <-> forall n, 0 <= Re(divisorValue_(n,1/2))`.

## Proof-burden reduction and route test

This closes the critical regularization problem completely. Endpoint existence, prime summability before the endpoint, joint polar--Gamma--prime cancellation, and normalization to the LI source are no longer conjectural.

Remaining producer is exact and route-decisive: prove nonnegativity of every explicit completed Abel endpoint. That theorem closes the LI route and RH; one negative mode kills this route.

## RH chain

`completed Abel endpoint nonnegative for every mode`
`=> LI prime--archimedean square source nonnegative for every mode`
`=> positive even paired Li coefficients nonnegative`
`=> RiemannHypothesis`.

The formal capstone proves the first and last propositions equivalent, so no intermediate regularization lemma remains open.

## Main Lean theorems

- `routeUFourierIntegral_liEvenCrossCauchyDensityAtMass`
- `summable_liEvenCrossPrimeAbelTerm`
- `liEvenCrossDivisorAbelValue_eq_completedArithmetic`
- `tendsto_liEvenCrossCompletedArithmeticAbelValue_half`
- `re_liEvenCrossDivisorAbelValue_half_eq_liSource_div_eight`
- `riemannHypothesis_iff_liEvenCompletedAbelClockNonnegative`

## Novelty boundary

Classical Li/Weil arithmetic formulas already use Laguerre and Chebyshev weights. Novelty claim is limited to this corpus-specific common-reversal hard-edge polarization, its divisor-level dominated Abel landing, and the exact one-eighth normalization linking that landing to the formal LI square source. No claim is made that classical Li, Weil, Chebyshev, Laguerre, or Abel ingredients are new.

## Audit

- `lake env lean GaloisForLFunctions/RHTower/LiEvenCrossCompletedAbelLanding.lean`: passed.
- `lake build GaloisForLFunctions.RHTower.LiEvenCrossCompletedAbelLanding`: passed (12,509 jobs; target built in 34s).
- Umbrella import added to `GaloisForLFunctions/RHTower.lean`.
- Capstone axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Global static lint reports unrelated pre-existing unreachable owned modules; it does not report this module as unreachable.
