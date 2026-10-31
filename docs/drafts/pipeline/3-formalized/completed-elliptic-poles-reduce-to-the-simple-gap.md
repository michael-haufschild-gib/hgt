# Completed elliptic poles reduce to the simple gap

- **ID:** completed-elliptic-poles-reduce-to-the-simple-gap
- **Stage:** 3-formalized
- **Statement:** Every element of the completed infinity field of
  `F₃(x,y)`, `y²=x³−x`, is an affine function plus `c(x/y)⁻¹`, `c∈F₃`,
  plus an element of the maximal ideal.

## Proof

Bound the valuation of `z` by `exp(n)` for a nonnegative integer `n`.
For `n≥2`, the proved affine pole semigroup supplies `a` of valuation
`exp(n)`. The quotient `z/a` is integral. Its residue is a constant `c`,
so `v(z−ca)<exp(n)`. Discreteness gives `v(z−ca)≤exp(n−1)`.
Strong induction therefore leaves a remainder of valuation at most `exp(1)`.

The element `u=(x/y)⁻¹` has valuation `exp(1)`. Apply the same residue
cancellation to the remainder divided by `u`. The resulting valuation is
less than `exp(1)`, hence at most one. Subtract its constant residue and
absorb that constant into the affine part. The final remainder has valuation
less than one.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticCompletedPoleReduction.lean`:
`completedInfinity_reduce_poles`, `completedInfinity_affine_simplePole_remainder`.
Both passed direct `lake --old env lean` and transitive axiom audits;
only `propext`, `Classical.choice`, and `Quot.sound` occur. This is the local
reduction needed for the additive adelic fundamental domain.
