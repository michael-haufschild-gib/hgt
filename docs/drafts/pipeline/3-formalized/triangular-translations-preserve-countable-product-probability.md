# Triangular translations preserve countable product probability

- **Stage:** 3-formalized
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** For an additive commutative group with jointly measurable addition and translation-invariant
  probability `μ`, every measurable triangular map
  `T(x)ₙ=xₙ+φₙ(x₀,…,xₙ₋₁)` preserves the actual product probability `μ^ℕ`.

## Proof

Split each finite tuple into its head and last coordinate. The finite triangular
map is conjugate to `(x,t)↦(T(x),t+φ(x))`. Induction preserves the head law;
translation invariance preserves the conditional last-coordinate law.
The measurable skew-product theorem therefore preserves every finite product.

The first `N` coordinates of the countable map are exactly the finite map
applied to the first `N` input coordinates. Every finite marginal is consequently
unchanged. Each cylinder supported on a finite set of indices is the inverse
image of a measurable set in a sufficiently long initial segment.
Equality on these cylinders determines the countable product measure.
No Haar measure on the ambient completed unipotent group is asserted.

## Lean

`HTGeometry/LoopEisenstein/TriangularHaarProbability.lean`:
`measurePreserving_triangularFinite`, `measurePreserving_triangularSequence`.
Direct Lean check passed. Transitive axiom audit: `propext`, `Classical.choice`, `Quot.sound`.
