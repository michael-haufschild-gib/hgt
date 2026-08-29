# LI even-cross completed Abel exterior-flow no-go

- **ID:** LI-CAB4.NG
- **Stage:** 3-formalized
- **Lean module:** `GaloisForLFunctions.RHTower.LiEvenCrossCompletedAbelExteriorFlowNoGo`
- **Corpus sources:** `LiEvenCrossCompletedAbelMassFlow`, `XiShiftedHankelFarRightPositiveDefinite`, `XiShiftedMomentFarRightAsymptotic`, `XiShiftedCanonicalAdmissionAdaptiveArithmeticSourceFlow`, `HorizonScalingSymmetry`

## Killed RH chain

Corpus-guided conjecture:

`exterior adjacent current <= 0 for every mode and w>1/2`
`=> propagate a far-right zero anchor backward to v=1/4`
`=> completed-Abel endpoint nonnegative`
`=> LI-CAB3`
`=> RiemannHypothesis`.

This chain is impossible at its first line. Lean proves that every fixed-mode exterior current is eventually strictly positive. The required far-right zero anchor is also absent after the natural current normalization.

## Exact classification and positive survivor

For unit coordinate `t=v*xiShiftedReciprocalSquare(v,q)`, the completed-Abel atom is evaluation of

`P_n(X) = (1-T_(n+1)(2X-1)^2)/2 = 2X(1-X)U_n(2X-1)^2`.

Its adjacent flux is exactly

`xiShiftedReciprocalSquare(v,q) * ((1-X)P_n')(t)`.

The complete real flux is therefore one finite Xi moment functional. With `v=w^2`, normalization by `2w/log(w)` converges to the arcsine moment functional. Lean proves the finite arcsine integration-by-parts law

`2 L_arc((1-X)(X P)') = L_arc(P)`.

Applied to `P=P_n/X`, it identifies twice the limiting flux energy with

`L_arc(2(1-X)U_n(2X-1)^2) > 0`.

Thus every mode has eventually positive exterior current. For `w>1/2`, the same current is exactly the literal completed rational--Gamma-minus-von-Mangoldt source, so source-side exterior nonpositivity fails too.

Strongest survivor is this strictly positive universal arcsine current energy. Remaining route-closing conjecture is interior LI-CAB5 only:

`Phi_n(v) >= 0` for every `n` and `0<v<=1/4`
`=> endpoint sign`
`=> LI-CAB3`
`=> RiemannHypothesis`.

## Main Lean theorems

- `liEvenCrossUnitDefect_eq_weightedSquare`
- `two_mul_momentFunctional_normalizedCentralBinom_one_sub_X_derivative_X_mul`
- `momentFunctional_liEvenCrossUnitFluxQuotient_pos`
- `liEvenCrossSquareMassAdjacentFlux_eq_unitFluxQuotient`
- `re_tsum_liEvenCrossSquareMassAdjacentFlux_eq_momentFunctional`
- `tendsto_normalized_liEvenCrossSquareMassAdjacentFlux`
- `eventually_re_tsum_liEvenCrossSquareMassAdjacentFlux_square_pos`
- `re_tsum_liEvenCrossSquareMassAdjacentFlux_sq_eq_arithmeticSource`
- `not_forall_liEvenCrossFluxArithmeticSource_nonpos`

## Novelty boundary

Classical Li/Weil literature supplies positivity criteria and explicit formulas; the arcsine measure and Chebyshev identities are classical separately. Literature audit found no exact squared-mass Xi adjacent-current identity, all-mode arcsine current limit, or literal completed-source exterior sign reversal above. Novelty claim is limited to this corpus-specific synthesis and its decisive no-go classification, not to those classical ingredients in isolation.

## Audit

- `lake env lean GaloisForLFunctions/RHTower/LiEvenCrossCompletedAbelExteriorFlowNoGo.lean`: passed.
- `lake build GaloisForLFunctions.RHTower.LiEvenCrossCompletedAbelExteriorFlowNoGo`: passed (15s; one final targeted module build; 12557 jobs).
- Umbrella import added to `GaloisForLFunctions/RHTower.lean`.
- Axiom audit of arcsine integration by parts, atom-current identity, normalized limit, eventual positivity, and arithmetic-source no-go: `propext`, `Classical.choice`, `Quot.sound` only.
