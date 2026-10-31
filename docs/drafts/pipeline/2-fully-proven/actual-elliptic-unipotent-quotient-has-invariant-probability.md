# Actual elliptic unipotent quotient has invariant probability

- **Stage:** 2-fully-proven
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** The literal restricted adelic positive unipotent group modulo
  its actual arithmetic intersection, with its coefficient quotient topology,
  is homeomorphic to the countable product of additive fundamental domains.
  It carries a probability invariant under every actual left translation.

## Proof

The audited multiplicative isomorphism from the uniform coefficient group
identifies its rational subgroup with the literal arithmetic intersection.
Thus it identifies the relations `a⁻¹b ∈ H`, without requiring normality.
Give the actual carrier the transported coefficient topology. The isomorphism
is a homeomorphism and induces a quotient homeomorphism. Composing its inverse
with the audited coefficient normalization identifies the actual quotient
with the product of additive domains.

Push the audited coefficient quotient probability through this homeomorphism.
Conjugate the coefficient quotient action by the same map. On representatives
multiplicativity gives `[h] ↦ [gh]`, so this is actual left multiplication.
Continuity follows from the three continuous factors. Pushforward composition
and the audited coefficient invariance prove invariance; total mass remains
one. No ambient infinite-dimensional Haar measure or rational discreteness
is used.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticUnipotentAdelicQuotient.lean`.
Direct check pending.
