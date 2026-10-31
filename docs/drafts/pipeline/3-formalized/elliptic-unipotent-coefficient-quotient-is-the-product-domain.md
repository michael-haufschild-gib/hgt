# Elliptic unipotent coefficient quotient is the product domain

- **Stage:** 3-formalized
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** The quotient of uniformly integral unipotent adele
  matrices by uniformly integral diagonal rational unipotents is
  homeomorphic to the countable product of actual additive domains,
  for the explicitly specified coefficient-stream topology.

## Proof

Use the topology induced by the injective free-stream coordinate map on
the uniform matrix group. Canonical normalization is continuous and is
constant on right rational cosets, so it descends continuously to the
quotient. Decoding a domain-valued stream is uniformly integral at every
finite place, and its coefficient stream is the original stream. Thus
decoding followed by the quotient map is continuous.

Normalization fixes every domain stream. Conversely, a matrix and its
canonical reduction differ by its unique rational correction, which
remains uniformly integral. Hence the two continuous maps are inverse.
No claim that the infinite product domain is open is needed.

The separate carrier and arithmetic-intersection identifications connect
this coefficient quotient to the actual restricted central-loop quotient.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticUnipotentQuotient.lean`:
`unipotentCoefficientQuotientHomeomorph`. Direct Lean check passed; both axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
