# Cayley–Li and Suzuki receivers

- **ID:** cayley-li-and-suzuki-receivers
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** review-0411 §2.1, A32.

## Existing statements

`ArithmeticLorentzianGeometry.riemannHypothesis_iff_cayleyLadder_nonpos`
identifies RH with the nonpositive Cayley–Li quadratic form on every primitive
vector. The reflection formula retains multiplicities; the vectors `e_n−e_0`
recover Li positivity in the converse.

`RHTower.tendsto_suzukiCriticalSourcePairing_firstVariation_of_lipschitz`
identifies the literal Suzuki difference quotient with the complete Weil form.
`riemannHypothesis_iff_factorialTentPattern_suzukiFirstVariation_nonneg`
gives both the nonnegative-limit and no-linear-overshoot receivers on an
RH-complete family. The same module proves transfer uniform in the grid scale.

The related `liEvenCrossActualClockPrimitive_rh_criteria` identifies RH with
nonnegativity, eventual nonnegativity, or an eventual lower bound for the actual
clock primitive. Off RH its negative values escape to minus infinity.

## Audit

These are existing results, not new mathematics. Direct source checks passed for:

- `ArithmeticLorentzianGeometry/RHIsReflectionPositivityOfTheCayleyLadder.lean`;
- `RHTower/LiEvenCrossActualClockPrimitiveNegative.lean`;
- `RHTower/Suzuki/SuzukiCriticalRHCompleteFamilyTransfer.lean`.

All nine transitive axiom audits contain only `propext`, `Classical.choice`, and
`Quot.sound`. All three modules already have umbrella imports. These are exact
receivers and RH equivalences; they do not prove their RH-equivalent sign.
