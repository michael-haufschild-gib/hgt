# Elliptic unipotent normalization is rationally invariant

- **Stage:** 2-fully-proven
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** Canonical reduction is invariant under right rational
  multiplication, fixes domain-valued matrices, and is triangular in the
  free stream with diagonal coefficient one on additive-domain increments.

## Proof

Write `f` for the rational matrix embedding and `c(g)` for the unique
correction. The correction `r⁻¹c(g)` sends `gf(r)` to `gf(c(g))`, so
uniqueness gives `c(gf(r))=r⁻¹c(g)`. Hence both inputs have the same reduced
matrix. If the original stream lies in the domain, the identity is already
a correction, so reduction fixes the matrix.

Induction on the recursive coordinate proves that equal stream prefixes
through index `n` have equal rational corrections through that index. Thus
inputs agreeing below `n` have identical nonlinear corrections at `n`.
If their current coordinates differ by `d` in the additive domain, their
triangular inputs differ by `d`. The gap projection is additive and fixes
the domain, so their normalized coordinates also differ by exactly `d`.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticUnipotentNormalization.lean`:
`adeleUnipotentReduced_mul_rational`, `adeleUnipotentReduced_of_domain`,
`adeleUnipotentNormalization_coordinate_add`. Direct check pending.
