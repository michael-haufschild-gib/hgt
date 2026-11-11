# Robust finite comb index counts right zeros

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Targets:** A80/A94; Γ216.
- **Lean:** `HodgeTheoryOfAFixedPart.nat_le_rightZeros_iff_eventual_robustCombIndex` in `TheRobustCombIndexCountsRightZeros.lean`.

For every natural `r`, zeta has at least `r` distinct right zeros iff some
`K≥1` and `η>0` give at least `r` negative directions for
`combForm + η Σ|c_n|²` on `(N,N+3KN]` at every sufficiently large scale.
The complex comb form is the sum of its real and imaginary forms.

## Proof

Pontryagin supplies a finite negative smooth packet family. One common
translation preserves its Weil Gram and puts it inside a sampling window.
Sampling converges simultaneously for the full Weil form and coefficient
mass, preserving its index with a fixed positive margin.

Conversely, pad a comb window into complete blocks. Block compression and
uniform step-form convergence each spend part of the margin. The resulting
linear map injects every robust negative comb subspace into a fixed step
Gram. Simultaneous mollification preserves the full form: Jensen domination
controls jump energy, while pole terms and contacts converge. The smooth
Pontryagin bound then excludes additional negative directions.

This proves both transfers, including the upper bound against finite-comb
artifacts. Unshifted index convergence at a fixed indefinite window remains
separate.

## Formalization

Capstone passed `lake --old env lean`; all supporting modules passed,
required oleans exist, and umbrella imports are wired. Supports:

- `AbsoluteGeometryOfSpecZ/WeilsFormIsContinuousUnderPacketSmoothing`
- `AbsoluteGeometryOfSpecZ/BoundedPacketIndexCountsNoExtraZeros`
- `HodgeTheoryOfAFixedPart/TheRobustIndexOfTheFiniteComb`
- `HodgeTheoryOfAFixedPart/TheRobustCombDirectionsTransferToStepPackets`
- `HodgeTheoryOfAFixedPart/RobustCombIndexCreatesNoExtraZeros`
- `HodgeTheoryOfAFixedPart/FiniteCombSamplingGrams`
