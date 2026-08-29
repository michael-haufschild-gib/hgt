# LI completed-Abel interior first-zero reduction

- **ID:** LI-CAB6
- **Stage:** 3-formalized
- **Lean module:** `GaloisForLFunctions.RHTower.LiEvenCrossCompletedAbelInteriorFirstZero`
- **Corpus sources:** `SquaredXiCompleteMonotonicity`, `SuzukiCoalescingXiSourceRate`, `XiSquaredEulerApertureHilbertCorrelation`, `XiShiftedAdaptiveArithmeticSourceArcsineAdmissionMargin`

## Closed premise

For every mode `n`, the completed-Abel adjacent current has exact positive right trace

`Phi_n(v) -> 2(n+1)^2 normalizedPrimeArchMoment(0) > 0`

as `v -> 0+`. Its unit flux quotient is exactly

`-(n+1)(1-X) U_(2n+1)(2X-1)`.

Lean proves continuity through zero and on every positive-mass interval. Therefore every nonpositive
current value on `(0,1/4]` forces an actual current zero at positive mass. Equivalently, absence of
positive-mass zeros is exactly strict current positivity on this interval.

## RH chain

`no zero of Phi_n on (0,1/4] for every n`
`=>` strict all-mode current positivity by the positive trace and first crossing
`=>` nonnegative completed-Abel endpoint values
`=>` LI-CAB3 endpoint criterion
`=>` RH.

The module proves this implication in `riemannHypothesis_of_no_liEvenCrossInteriorCurrent_zero`.
It does not prove zero-exclusion. Remaining LI burden is now the explicit positive-mass zero-exclusion
theorem; a witnessed zero followed by a negative crossing would kill the monotone-flow route.

## Main Lean theorems

- `liEvenCrossUnitFluxQuotient_eq_oddChebyshev`
- `tendsto_xiShiftedPolynomialMoment_zero`
- `tendsto_liEvenCrossSquareMassAdjacentCurrent_zero`
- `exists_liEvenCrossInteriorCurrent_zero_of_nonpos`
- `liEvenCrossInteriorCurrent_pos_iff_no_zero`
- `liEvenCrossEndpoint_nonneg_of_no_interiorCurrent_zero`
- `riemannHypothesis_of_no_liEvenCrossInteriorCurrent_zero`

## Audit

- `lake env lean GaloisForLFunctions/RHTower/LiEvenCrossCompletedAbelInteriorFirstZero.lean`: passed.
- Umbrella import added to `GaloisForLFunctions/RHTower.lean`.
- `lake build GaloisForLFunctions.RHTower.LiEvenCrossCompletedAbelInteriorFirstZero`: passed (135s; one targeted module build; 12562 jobs).
- Axiom audit of algebraic normal form, moment landing, positive trace, first-zero theorem, endpoint theorem, and RH capstone: `propext`, `Classical.choice`, `Quot.sound` only.
- No computation or numerical zero data enters any proof.
