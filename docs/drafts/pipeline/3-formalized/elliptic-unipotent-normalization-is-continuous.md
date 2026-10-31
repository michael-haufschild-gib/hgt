# Elliptic unipotent normalization is continuous

- **Stage:** 3-formalized
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** Canonical unipotent normalization is continuous from the
  product of actual adele coefficient spaces to the product of additive
  fundamental domains.

## Proof

The embedded rational projection satisfies `f(q(a))=a−ρ(a)`. It is
continuous because the actual gap projection is continuous. This proves
the needed continuity without any topological assumption on the abstract
rational function field.

At coordinate `n`, the embedded correction equals
`−f(q(xₙ+Pₙ(x_{<n},f(r_{<n})))))`. Strong induction, continuity of the finite
triangular correction, and continuity of the embedded additive projection
prove its continuity. Each normalized coordinate is the continuous gap
projection of the same input. Coordinatewise continuity gives continuity
into the product domain. The triangular reduction identity identifies
this map with normalization of the actual completed matrix.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticUnipotentContinuity.lean`:
`continuous_adeleUnipotentCorrectionValue`,
`continuous_adeleUnipotentNormalization`. Direct Lean check passed; all three axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
