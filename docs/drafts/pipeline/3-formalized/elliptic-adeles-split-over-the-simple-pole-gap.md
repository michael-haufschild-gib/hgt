# The elliptic adeles split over the simple-pole gap

- **ID:** elliptic-adeles-split-over-the-simple-pole-gap
- **Stage:** 3-formalized
- **Statement:** For `K=F₃(x,y)`, `y²=x³−x`, the additive subgroup
  `D=(∏finite O_v)×(F₃(x/y)⁻¹+m∞)` meets every coset of diagonal `K`
  in exactly one point.

## Proof

Finite approximation supplies `z∈K` with all finite coordinates of `a−z`
integral. Completed infinity pole reduction supplies an affine function `b`
such that the infinity coordinate of `a−z−b` lies in
`F₃(x/y)⁻¹+m∞`. Affine functions are integral at every finite place, so
`a−z−b∈D`.

If diagonal `z∈D`, all its finite valuations are at most one. The Dedekind
integrality criterion and the canonical integral-closure identification make
`z` affine. Its infinity value is at most `exp(1)`, hence its pole degree is
at most one. The affine pole-semigroup gap makes it constant. A nonzero
simple-pole coefficient has value `exp(1)`; an element of `m∞` has value
less than one. Thus a member of `D` with value at most one lies in `m∞`.
Every nonzero constant has value one, so `z=0`. Subtracting two
representatives proves uniqueness.

## Verification

`FiniteFieldEllipticBase.adele_existsUnique_gap_representative`
in `ArithmeticEffectivityTheory/FiniteFieldEllipticAdditiveDomain.lean`
passed direct `lake --old env lean` and transitive axiom audits.
Its only axioms are `propext`, `Classical.choice`, and `Quot.sound`.
