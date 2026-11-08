# Arithmetic Vieta correspondence

- **ID:** RIAC-arithmetic-Vieta
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); classical finite-field calibration
- **Source:** [discriminant-cover construction](../1-in-progress/riac-discriminant-cover-signed-counts.md)
- **Statement:** Monic degree-`n` polynomials over a finite field correspond bijectively to Frobenius-stable permutation orbits of `n` roots in the actual extension of degree `n!`, including repeated roots.

## Construction and proof

Let `F` have `q` elements. An irreducible factor of degree `d≤n` has
residue field of degree `d`; since `d` divides `n!`, that residue field
embeds in the common degree-`n!` extension `E/F`. Normality makes the
factor split there. Unique factorization gives splitting of every monic
polynomial of degree `n`.

Order its roots with their multiplicities. The product `∏ᵢ(X−xᵢ)` is
unchanged by reordering. Conversely, equality of products gives equality
of root multisets; bijections between equal-multiplicity fibres assemble
into a permutation. Thus the polynomial determines exactly one root orbit.
Base-field coefficients make that orbit Frobenius-stable, and the root
product makes the map from monic polynomials injective.

The coefficient count gives `q^n` monic polynomials. The independently
proved normal-basis/transporter count gives `q^n` stable orbits. Therefore
the injection is surjective. No polynomial Möbius degree sum enters this
argument. The resulting equivalence uses the explicitly constructed finite
extension; no splitting or surjectivity premise remains unproved.

## Exact scope

This identifies the actual coefficient space underlying the signed orbit
construction. The discriminant-square/Vandermonde comparison and the
resulting cover count remain separate. There is still no map identifying
these finite-field weights with the integer local indices and no bound on
`Σ_p index_p(N)=1−M(N)`.

## Formalization

[FiniteFieldVieta.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/FiniteFieldVieta.lean):

- `finiteField_irreducible_splits`, `finiteField_bounded_monic_splits`.
- `tupleRootPolynomial_roots`, `tupleRootPolynomial_smul`, `tupleRootPolynomial_eq_iff`.
- `monic_exists_root_tuple`, `monicRootTuple_frobenius`, `monicRootOrbit_injective`.
- `monicRootOrbit_bijective`, `monicFrobeniusOrbitEquiv`, `frobeniusOrbit_unique_monic`.
- `arithmeticVietaEquiv`.

Direct leaf check and twelve transitive axiom audits; only `propext`,
`Classical.choice`, `Quot.sound`.

## Literature boundary

Vieta and finite-field Galois descent are classical.
[Gadish, §1.1](https://arxiv.org/html/1703.01710v2) treats the polynomial
coefficient quotient and its ramified Frobenius statistics. The contribution
here is the formal comparison with the independently counted actual root
orbits, not a new point-count theorem.
