# Elliptic adelic Haar has exact finite-cylinder products

- **Stage:** 2-fully-proven
- **Parent:** [Arithmetic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** On the open subgroup integral outside any finite place set
  `S`, actual adelic Haar pulls back to normalized Haar on the completed
  fields in `S`, Haar probability on the remaining integer rings, and
  normalized infinity Haar.

## Proof

Coordinate assembly is an additive open embedding of
`(Π_(v∈S) K_v × Π_(v∉S) O_v) × K_∞` into the actual adeles. The
[audited finite-cylinder homeomorphism](../3-formalized/elliptic-finite-cylinders-split-as-local-fields-and-integers.md)
gives its finite part; infinity is unchanged.
Its image contains the full integral adelic product.

The ambient Haar pullback and the stated product are additive Haar measures.
The coordinate space is locally compact and second countable: its finite
field factors are locally compact and second countable, and its integral
tail is a countable product of compact second-countable integer rings.

The preimage of the full integral adelic product is exactly
`(Π_(v∈S) O_v × Π_(v∉S) O_v) × O_∞`. Ambient normalization assigns this
box mass one. Finite product measure, local normalization and tail probability
assign it mass one under the product measure. Haar uniqueness identifies the
two measures: evaluation on this box forces the scalar multiplier to one.

This proves the measure identity. Finite-product kernel integrals, exhaustion
by cylinders, the global Euler-product integral and arbitrary-idele Jacobians
remain separate assertions.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticCylinderHaar.lean`:
`ellipticCylinderAssembly_isOpenEmbedding`,
`ellipticCylinderAmbientHaar_eq_product`. Direct audit pending.
