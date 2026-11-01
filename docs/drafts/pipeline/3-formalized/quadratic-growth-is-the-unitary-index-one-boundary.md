# Quadratic growth and the unitary index-one boundary

- **Stage:** 3-formalized.
- **Type:** THEOREM (Lean).
- **Source:** B9 in `docs/reports/review-3110/route-obstacles.md`.
- **Statement:** For an abelian Hermitian kernel of negative index at most
  one, cyclic subexponential growth, cyclic quadratic growth, and existence
  of a positive unitary-character mass hyperplane are equivalent.
- **Stronger forward statement:** A Hermitian kernel on any group, positive
  on a unitary-character mass hyperplane, has quadratic growth on every
  cyclic subgroup.
- **Count:** Strengthens contribution 4; not a separate contribution.

## Corpus bridge and novelty

HKT `exists_unitary_positive_hyperplane_of_cyclic_subexponential` supplies
one implication. AKG `TowerCoupling.polarIndex_eq_negIndex_secondDiff`
identifies conditional positivity on an integer tower with positivity of
its centered second difference. HKT `hermQuad_gram_twist` supplies the
unitary congruence, and `IsPosDefKernel.norm_le` bounds the resulting
coefficients. Their statements and proofs were read.

Searches `/tmp/hgt-conditional-cyclic-quadratic.json`,
`/tmp/hgt-second-difference-growth-corpus.json`, and
`/tmp/hgt-discrete-growth-final-novelty.json` found special negative-power
examples and second-difference estimates, but no general quadratic growth
classification.

## Paper proof

Suppose the character-mass hyperplane for a unitary character χ is positive.
Put `l(h)=conjugate(χ(h)) k(h)`. The unitary-twist Gram congruence identifies
its quadratic form at coefficients `c_i` with that of `k` at
`conjugate(χ(x_i)) c_i`. The latter coefficients have χ-mass `Σ c_i`.
Thus `l` is conditionally positive on total mass zero, and `|l(h)|=|k(h)|`.
Hermitian symmetry is preserved.

Fix `g` and pull back `l` along the homomorphism `m ↦ g^m` from ℤ. Denote
the pullback by `q`. Its polar index is zero because every mass-zero Gram
vector has nonnegative square. The exact polar-index identity makes
`d(m)=2q(m)-q(m+1)-q(m-1)` positive definite. Hence
`|d(m)| ≤ M=d(0).re`, with `M≥0`.

For `f(n)=q(n)` on the natural numbers, write `a(n)=f(n+1)-f(n)`.
The preceding bound gives `|a(n+1)-a(n)|≤M`; induction gives
`|a(n)|≤A+nM`, where `A=|f(1)-f(0)|`. A second induction gives
`|f(n)|≤B+nA+n²M`, where `B=|f(0)|`. Consequently
`|k(g^n)|=|f(n)|≤(A+B+M)(n+1)²`. This argument uses no commutativity of
the ambient group.

Every quadratic bound is subexponential. For `ε>0`, the elementary estimate
`x²/2≤exp(x)` at `x=ε(n+1)` gives
`(n+1)²≤(2/ε²) exp(ε) exp(ε n)`.

For an abelian kernel of index at most one, the formalized subexponential
unitary-hyperplane theorem gives the remaining implication. This proves
all three conditions equivalent without boundedness or translated-growth
assumptions.

## Lean formalization

- `HTGeometry/BoundedSecondDifferences.lean`:
  `norm_le_quadratic_of_second_difference`,
  `exists_quadratic_bound_of_second_difference`,
  `subexponential_of_quadratic_bound`.
- HKT `Index/PositiveHyperplaneQuadraticGrowth.lean`:
  `cyclic_quadratic_of_positive_unitary_hyperplane` (arbitrary groups).
- HKT `Index/IndexOneGrowthBoundary.lean`:
  `cyclic_subexponential_iff_unitary_positive_hyperplane`,
  `cyclic_subexponential_iff_quadratic`.

Required oleans and direct capstone checks pass. All three capstone axiom
audits contain exactly `propext`, `Classical.choice`, `Quot.sound`.
No proof placeholders or limit changes. HTGeometry and HKT umbrellas wired.
Final novelty audits: `/tmp/hgt-quadratic-boundary-final-novelty.json`,
`/tmp/hgt-quadratic-akg-final-novelty.json`.
