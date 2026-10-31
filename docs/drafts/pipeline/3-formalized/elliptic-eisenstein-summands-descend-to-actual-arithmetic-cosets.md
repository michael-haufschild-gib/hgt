# Elliptic Eisenstein summands descend to actual arithmetic cosets

- **Stage:** 3-formalized
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** The actual spectral section evaluated on `gγ` depends
  only on `γ(Γ∩B)`. Its coset sum therefore has an independent arithmetic
  definition before any constant-term calculation.

## Proof

The arithmetic Borel is the preimage of the actual adelic Borel under the
faithful restricted arithmetic embedding. If `γ₁⁻¹γ₂` belongs to this
subgroup, write `γ₂=γ₁b`. Right-Borel equivariance of the spectral section
and its proved trivial character on arithmetic Borel give
`Φ(gγ₂)=Φ(gγ₁)`. This descends the summand to the quotient by right
multiplication with arithmetic Borel elements.

The sum is defined from these arithmetic cosets and the independently
constructed Iwasawa section. Summability, countability of the coset set,
and unfolding are not asserted here.

Left multiplication by a restricted rational loop permutes the arithmetic
cosets. The Iwasawa summand at `gγ` is the summand at `g` evaluated on that
permuted coset. Reindexing the sum proves right arithmetic invariance of the
independently defined series. This algebraic identity does not assert
convergence.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticEisensteinCosets.lean`:
`adelicIwasawaSection_arithmetic_coset`, `ellipticEisensteinSummand`,
`ellipticEisensteinSeries`, `ellipticEisensteinSummand_right_arithmetic`,
`ellipticEisensteinSeries_right_arithmetic`. Direct Lean and transitive axiom
audits passed; only `propext`, `Classical.choice`, and `Quot.sound` occur.
