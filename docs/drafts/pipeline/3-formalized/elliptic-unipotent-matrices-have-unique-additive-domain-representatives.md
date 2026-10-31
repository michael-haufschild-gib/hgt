# Elliptic unipotent matrices have unique additive-domain representatives

- **Stage:** 3-formalized
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** Every completed unipotent matrix over the actual elliptic
  adele ring has exactly one right rational correction whose entire
  coefficient stream lies in the compact additive domain.

## Proof

Write the actual additive splitting as `a=f(q(a))+ρ(a)`, where `f` is
the diagonal field embedding, `q(f(r))=r`, and `q(D)=0`. The proved
triangular multiplication law is
`(xy)ₙ=xₙ+yₙ+Pₙ(x_{<n},y_{<n})`.

For the stream `x` of a given matrix, define recursively
`rₙ=−q(xₙ+Pₙ(x_{<n},f(r_{<n})))`. Every right-hand side uses strictly
earlier coefficients, so this defines a full rational stream. The actual
stream equivalence decodes it into one completed rational matrix.
Its right product with the original matrix has coordinate
`ρ(xₙ+Pₙ(x_{<n},f(r_{<n})))`, hence lies in `D` in every coordinate.

For any other rational correction with this property, assume its earlier
coordinates equal `r`. Applying `q` to its current product coordinate
gives `0=q(xₙ)+r'ₙ+q(Pₙ)`, forcing `r'ₙ=rₙ`. Strong induction and the
stream equivalence prove uniqueness.

This theorem concerns matrices over the adele ring. The common finite
exceptional set required by the restricted loop carrier is a separate
integrality assertion.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticUnipotentReduction.lean`:
`adeleUnipotentReduced_mem`, `adeleUnipotentRationalCorrection_unique`,
`existsUnique_adeleUnipotentRationalCorrection`. Direct `lake --old env lean` check passed. All three transitive axiom audits
contain only `propext`, `Classical.choice`, and `Quot.sound`.
