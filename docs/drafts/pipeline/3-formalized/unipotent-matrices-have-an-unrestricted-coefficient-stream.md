# Unipotent matrices have an unrestricted coefficient stream

- **Stage:** 3-formalized
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** Over every commutative ring `R`, the actual completed unipotent
  coefficient group is in bijection with `ℕ→R`, ordered as
  `b₀,c₁,a₁,b₁,c₂,a₂,…`.

## Proof

The audited free-entry equivalence gives arbitrary series `a,b,c`, with
`a₀=1,c₀=0`. Define `bₙ=x₃ₙ`, `cₙ₊₁=x₃ₙ₊₁`, `aₙ₊₁=x₃ₙ₊₂`.
Reading coefficients at the three residue classes modulo three reverses
this construction. Equality of all coefficients proves both inverse laws.
The lower-right series is still the determinant-forced `a⁻¹(1+bc)`.

This bijection is purely algebraic; triangular multiplication and arithmetic
quotient reduction require separate proofs.

## Lean

`HTGeometry/LoopEisenstein/UnipotentCoefficientStream.lean`:
`unipotentCoefficientStreamEquiv`. Direct Lean check passed. Transitive axiom audit: `propext`, `Classical.choice`, `Quot.sound`.
