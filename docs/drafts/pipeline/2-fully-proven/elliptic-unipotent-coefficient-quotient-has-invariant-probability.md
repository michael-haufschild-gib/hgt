# Elliptic unipotent coefficient quotient has invariant probability

- **Stage:** 2-fully-proven
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** The rational coefficient quotient carries a probability
  measure invariant under actual left multiplication by every uniformly
  integral unipotent adele matrix.

## Proof

Push the proved domain product probability through the inverse quotient
homeomorphism. Conjugate the proved normalized domain action by that
homeomorphism. Decoding a domain stream and multiplying on the left gives
the same rational coset as first normalizing the product. Consequently this
conjugated action sends `[x]` to `[gx]`; it is the actual quotient action.

The action is continuous, and its composition with the domain-to-quotient
map equals that map composed with the normalized domain action. Pushforward
composition and the proved domain invariance therefore give invariance of
the quotient measure. Its total mass is one because the original product
measure has total mass one.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticUnipotentQuotientProbability.lean`:
`unipotentCoefficientQuotientLeft_mk`,
`measurePreserving_unipotentCoefficientQuotientLeft`. Direct check pending.
