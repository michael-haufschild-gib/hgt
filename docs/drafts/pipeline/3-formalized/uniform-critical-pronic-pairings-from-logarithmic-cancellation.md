# Uniform critical pronic pairings from logarithmic cancellation

- **ID:** uniform-critical-pronic-pairings-from-logarithmic-cancellation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../2-fully-proven/uniform-half-damping-vaughan-harmonic-gram.md
- **Statement:** A common two-logarithm saving at the square-root prefix scale gives a summable envelope for both pronic energy and absolute smooth pairings.

For a family `f_i(n)`, assume a common linear bound on positive cells and a
common eventual bound `|f_i(n)|≤B sqrt(n)/(log n)²`, with nonnegative constants.
One nonnegative summable sequence dominates

`[sqrt(n)|f_i(n)|+f_i(n)²]/[n(n+1)]`

for every i and n. Beyond the common threshold this cell is at most
`(B+B²)/(n(log n)²)`. A finite head is bounded using the linear estimate.
Consequently every finite pronic energy and every absolute smooth pairing
has one uniform bound, the sum of that envelope.

## Lean audit

Module: [UniformCriticalPronicPairingsFromLogarithmicCancellation.lean](../../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformCriticalPronicPairingsFromLogarithmicCancellation.lean).

- `critical_pronic_mixed_add_square_le`
- `exists_summable_critical_pronic_envelope`
- `exists_uniform_critical_pronic_mixed_and_energy_bound`

Corrected producing and final direct `lake --old env lean` checks passed.
All three transitive axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`. Mathlib summability APIs passed their separate scratch check.
The BVI umbrella import is present; the owned theorem scratch was removed.
This certifies the generic summation step. Its actual five-row Vaughan
specialization remains pending on the source card until its own checks pass.
