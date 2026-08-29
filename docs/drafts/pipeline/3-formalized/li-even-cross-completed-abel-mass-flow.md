# LI even-cross completed Abel mass flow

- **ID:** LI-CAB4
- **Stage:** 3-formalized
- **Lean module:** `GaloisForLFunctions.RHTower.LiEvenCrossCompletedAbelMassFlow`
- **Corpus sources:** `LiEvenCrossCompletedAbelLanding`, `SquaredXiCompleteMonotonicity`, `LiEvenCrossCayleySquareDefectPrimeSignWall`, `TraceHankelConverse`

## Result

In squared-mass time `v=a^2`, every multiplicity-labelled Xi atom of the LI completed-Abel value is exactly

`(1 - T_(2n+2)(c_q(v))) / 4`,

where `c_q(v)=2v*xiShiftedReciprocalSquare(v,q)-1`. Lean proves the actual Xi-resolvent transport law

`c_q'(v)=(1-c_q(v)^2)/(2v)=2*lambda_q(v)*(1-v*lambda_q(v))`.

The module proves from the corpus recurrences that `T_m'=m U_(m-1)`. Therefore atom velocity is the adjacent-mode current

`((n+1)/(8v))*(T_(2n+3)(c_q(v))-T_(2n+1)(c_q(v)))`.

A locally uniform reciprocal-square majorant makes that current summable and justifies differentiation of the complete Xi divisor sum. Its real part is the exact derivative of the real completed-Abel flow. The aggregate value is zero at `v=0` and tends to zero as `v -> 0+`.

## Proof-burden reduction

LI-CAB3 left endpoint sign as the RH-equivalent burden. LI-CAB4 removes atom algebra, formal differentiation, infinite-sum interchange, and zero-anchor continuity. One route-closing source theorem remains:

`Re(sum_q adjacentFlux(v,n,q)) >= 0` for every `n` and `0 < v <= 1/4`.

That sign makes the flow nondecreasing from zero, gives endpoint nonnegativity at `v=1/4`, and closes RH through LI-CAB3. An actual-Xi negative integrated crossing kills this mass-flow mechanism. Generic proxy or finite-moment counterexamples are irrelevant.

## Main Lean theorems

- `liEvenCrossDivisorAbelTerm_eq_singleChebyshevDefect`
- `hasDerivAt_liEvenCrossCayleyAtSquareMass`
- `derivative_chebyshevT_succ`
- `hasDerivAt_liEvenCrossSquareMassAtom_adjacentFlux`
- `norm_liEvenCrossSquareMassAtomVelocity_le_majorant`
- `hasDerivAt_re_liEvenCrossSquareMassValue_adjacentFlux`
- `tendsto_liEvenCrossSquareMassValue_zero_right`

## Novelty boundary

Bombieri--Lagarias relates Li coefficients to Weil positivity and the explicit formula; generalized Li criteria also vary the evaluation parameter. The literature audit found no statement of this corpus-specific squared-mass common-reversal Xi-divisor flow, its exact adjacent Chebyshev generator, or the complete-divisor differentiation theorem. Novelty claim is limited to those identities and the resulting single-current proof reduction, not to Li's criterion, generalized Li parameters, Chebyshev recurrences, or termwise differentiation in isolation.

## Audit

- `lake env lean GaloisForLFunctions/RHTower/LiEvenCrossCompletedAbelMassFlow.lean`: passed.
- `lake build GaloisForLFunctions.RHTower.LiEvenCrossCompletedAbelMassFlow`: passed (65s; single final targeted module build).
- Umbrella import added to `GaloisForLFunctions/RHTower.lean`.
- Atom normal form, Chebyshev derivative, complex/real aggregate derivative, zero anchor, and right-limit axioms in scratch: `propext`, `Classical.choice`, `Quot.sound` only.
