# Integral gluing counts for the signed local-index sum

- **ID:** RIAC-integer-gluing-count
- **Stage:** 3-formalized
- **Type:** CONSTRUCTION (Lean)
- **Source:** [RIAC](../1-in-progress/renormalized-intersection-arithmetic-counts.md)
- **Lean:** [IntegerGluingCounts.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/IntegerGluingCounts.lean)

## Independent integer object

For `N≥1`, take the free integer lattice on `e_1,…,e_N` and impose

`Σ_(d|j)e_d=0` for every `2≤j≤N`, and `Σ_(2≤j≤N)e_j=0`.

The resulting group `G_N` is defined only from integer divisibility.
Neither a Möbius sum, a local index nor a Weil form enters its presentation.
Orient the final relation negatively. Its presentation matrix `R_N` has
column one equal to `−Σ_(j≥2)e_j`; all other columns are divisor sums.

## Exact integral and signed comparison

Write `S(N)=Σ_p index_p(N)=1−M(N)`, using the actual local relative
singular-homology indices. The construction proves

`G_N ≃ₗ[ℤ] ZMod |S(N)|`, `det R_N=S(N)`.

Thus `G_N` is finite exactly when `S(N)≠0`, with `#G_N=|S(N)|`.
When `S(N)=0`, it is infinite cyclic. The Lean cardinal convention
`Nat.card G_N=0` in that case does not assert an empty finite group.
The determinant retains the sign discarded by cardinality.

## Proof mechanism

The integral divisibility matrix `Z(i,j)=[i|j]` has integral inverse
`U(i,j)=μ(j/i)[i|j]`. The existing real inversion identity is transported
through the injective integer embedding, so the inverse is unimodular.
Left multiplication by `U` turns the actual presentation into identity
with one replaced column `w`, whose pole coordinate is `S(N)`.

The residue map sends a lattice vector `v` to `(Uv)_1 mod S(N)`.
It is surjective. If `(Uv)_1=S(N)k`, subtract `k w` in all non-pole
coordinates and put `k` at the pole: this explicitly constructs a
preimage under the relation map. Hence its kernel is exactly the
relation lattice. The quotient equivalence follows from this proved
kernel equality, not from the determinant or order alone.

## Primary factors and product-formula height

For finite `G_N`, define `C_N=#G_N` and `i_p(N)=v_p(C_N)`.
The actual group has the canonical primary decomposition

`G_N ≃ ⨁_(p|C_N) ℤ/p^(i_p(N))ℤ`.

Its independent logarithmic count satisfies

`H_N=log C_N=Σ_p i_p(N)log p=log|S(N)|`.

The primary exponents therefore describe the actual quotient, rather
than a prescribed integer with an assumed local-global formula.

## Mathematical boundary

Direct production Lean check and 11 transitive axiom audits pass with only
`propext`, `Classical.choice`, and `Quot.sound`.

This supplies an exact integer-count comparison with the governing signed
sum. The missing estimate is `H_N≤(1/2+ε)log N+Oε(1)` on finite fibres.
Product-formula equality and nonnegative counts do not provide that upper
bound. The quotient records the aggregate charge; the full count on Hecke
correspondences remains open. No square-root cancellation or RH theorem is claimed.

The real Redheffer determinant and its Mertens comparison already occur in
[ArithmeticDegenerationTheory](../../../../formal/GaloisForLFunctions/ArithmeticDegenerationTheory/TheMertensFunctionIsAGluingDeterminant.lean).
The present construction uses the reduced gluing, constructs its integral
cyclic quotient and primary factors, and compares its oriented determinant
with the actual local indices. Integral column reduction and CRT are
classical; no priority claim or web novelty audit is made.
