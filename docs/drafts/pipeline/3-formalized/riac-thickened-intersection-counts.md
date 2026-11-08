# Actual counts of thickened arithmetic intersections

- **ID:** RIAC-thickened-intersections
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [RIAC](../1-in-progress/renormalized-intersection-arithmetic-counts.md)
- **Module:** [ThickenedArithmeticIntersections.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/ThickenedArithmeticIntersections.lean)
- **Statement:** Actual proper monic intersection rings have cardinality `|Res(P,Q)|`; two-divisor thickening multiplies each prime-local order and logarithmic height by `ab`.

## Construction and theorems

Define `C(P,Q)=# ℤ[X]/(P,Q)` before introducing a determinant, height or
Weil form. For monic `P,Q` with nonzero resultant, the actual ring is finite and

`C(P,Q)=|Res(P,Q)|`, `C(P^a,Q^b)=C(P,Q)^(ab)`.

The prime-local integer multiplicity `i_p=v_p(C)` and logarithmic height
`H=log C` satisfy

`i_p(P^a,Q^b)=ab·i_p(P,Q)`, `H(P^a,Q^b)=ab·H(P,Q)`.

Thus both local multiplicity and logarithmic height are quadratic under
equal thickening; the integer residue cardinality itself grows exponentially
in `k²`. The local-global formula is

`H(P,Q)=log|Res(P,Q)|=Σ_p i_p(P,Q) log p ≥ 0`.

Distinct cyclotomic divisors satisfy properness, proved over `ℚ` and descended
to `ℤ`. For positive distinct `n,m`, the actual thickened count has height
`ab·I(n,m)`, where `I` is the established torsion-orbit intersection.

## Proof

Write `d=deg P`, `e=deg Q`. Bounded polynomials of degree `<d+e` map onto
the intersection ring: reduction modulo monic `P` supplies representatives.
Their relation map is `(u,v)↦Qu+Pv`, with `deg u<d`, `deg v<e`.
If `r=aP+bQ`, set `u=b mod P` and `v=a+Q(b div P)`.
Then `r=Qu+Pv`; the degree bound on `r−Qu` forces `deg v<e`.
This identifies the actual quotient with the integral Sylvester cokernel.
The determinant is the resultant, so the integer lattice index theorem
proves cardinality and finiteness.

Resultant multiplicativity gives `Res(P^a,Q^b)=Res(P,Q)^(ab)`.
Taking prime factorization and logarithms proves the local scaling and
product formula. Over `ℂ`, the cyclotomic resultant is the product of
`η−ξ` over the two primitive-root orbits. Distinct orders exclude zero
factors; the logarithm of its norm is exactly `I(n,m)`.

## Lean declarations and audit

`intersectionRelationQuotientEquiv`,
`arithmeticIntersectionCount_eq_resultant`,
`arithmeticIntersectionRing_finite`,
`arithmeticIntersectionCount_thickening`,
`arithmeticIntersectionOrder_quadratic`,
`arithmeticIntersectionHeight_quadratic`,
`arithmeticIntersectionHeight_prime_sum`,
`cyclotomic_thickened_intersection_finite`,
`cyclotomic_intersectionHeight_thickening`.

Direct `lake --old env lean` check and transitive axiom audit: only
`propext`, `Classical.choice`, `Quot.sound`.

## Relation to signed cancellation

The governing target is `Σ_p index_p(N)=1−M(N)` at scale
`N^(1/2+ε)`. These effective proper intersection counts supply no bound on
that signed sum. A bridge must control positive and negative contributions,
including self-interaction and critical renormalization. No such comparison
or positive primitive pairing is assumed. The rational product formula for
an integral resultant does not supply the required critical completion.
The surface Riemann–Roch count remains open.

## Literature and novelty boundary

The corpus already counts reduced cyclotomic intersections in
`ArithmeticIntersectionTheory/TheArchimedeanIntersectionIsALogOrder.lean`.
This module constructs the integral presentation of the actual two-equation
quotient and its nonreduced thickenings. Resultants, lattice indices and
intersection multiplicities are classical; their classical identities are
not claimed as new mathematics.
[Stacks, intersection multiplicities](https://stacks.math.columbia.edu/tag/0B01)
explains the length description for proper Cohen–Macaulay intersections;
[higher Tor terms](https://stacks.math.columbia.edu/tag/0AZR) explain why
ordinary cardinalities cannot replace general derived intersections.
