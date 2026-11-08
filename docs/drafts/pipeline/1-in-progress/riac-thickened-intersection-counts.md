# Actual counts of thickened arithmetic intersections

- **ID:** RIAC-thickened-intersections
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [RIAC](renormalized-intersection-arithmetic-counts.md)
- **Statement:** Construct `C(P,Q)=# ℤ[X]/(P,Q)` for proper monic intersections and prove `C(P^a,Q^b)=C(P,Q)^(ab)` from the actual quotient.

## Construction and proof target

For monic integral polynomials with nonzero resultant, the intersection
ring is finite. Its additive presentation is the Sylvester map
`(u,v) ↦ Qu+Pv`, with `deg u<deg P` and `deg v<deg Q`.
Monic division identifies its cokernel with the actual quotient ring;
the integer lattice index theorem then gives `C(P,Q)=|Res(P,Q)|`.
Resultant multiplicativity yields the thickening law and
`log C(P^k,Q^k)=k² log C(P,Q)`.
The quotient is defined before its determinant or logarithmic height.
Coprimality over `ℤ[X]` is not assumed: it would erase the nontrivial
arithmetic intersections. Properness means no common generic root.

## Relation to signed cancellation

The governing target remains `Σ_p index_p(N)=1−M(N)` at scale
`N^(1/2+ε)`. These positive intersection counts alone give no bound on
that signed sum. A useful bridge must compare the positive and negative
local contributions through actual arithmetic cycles, with a quantitatively
controlled remainder. No such comparison, positive primitive pairing or
archimedean completion is assumed. Quadratic thickening alone does not
qualify as a cancellation theorem.

## Existing work and novelty boundary

The corpus already counts reduced cyclotomic intersections in
`ArithmeticIntersectionTheory/TheArchimedeanIntersectionIsALogOrder.lean`.
This candidate concerns actual nonreduced two-divisor thickenings and their
integral presentation. Resultants, lattice indices and multiplicities are
classical; no novelty is claimed for their classical identities.
[Stacks, intersection multiplicities](https://stacks.math.columbia.edu/tag/0B01)
explains the length description for proper Cohen–Macaulay intersections;
[higher Tor terms](https://stacks.math.columbia.edu/tag/0AZR) explain why
ordinary cardinalities cannot be used for arbitrary intersections.

## Status

Quotient presentation, cardinality and thickening statements require Lean
proofs. No surface Riemann–Roch theorem, signed-cancellation estimate or RH
result follows from this card.
