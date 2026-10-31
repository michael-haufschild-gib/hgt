# The elliptic additive domain has jointly measurable addition

- **Stage:** 3-formalized
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** The actual compact elliptic additive domain is second countable;
  its addition is measurable for the product of its inherited Borel structures.

## Proof

The affine integer ring is countable and Noetherian. Every ideal is generated
by a finite set, so its ideals, and hence its finite places, form countable sets.
Each actual local completion has the audited proper metric and is second
countable. This includes the actual infinity completion.

The compact additive domain maps continuously and injectively to the product
of all finite completions and the infinity completion by retaining every local
component. Compactness and the Hausdorff target make this a closed embedding.
The target is a countable product of second-countable spaces, so the domain
is second countable. Continuous addition is then measurable for the product
Borel structure.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticGapTopology.lean`:
`finitePlace_countable`, `ellipticAdditiveDomain_secondCountable`,
`ellipticAdditiveDomain_measurableAdd₂`. Direct Lean check passed. All transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.
