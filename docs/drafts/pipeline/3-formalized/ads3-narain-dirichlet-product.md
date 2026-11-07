# The scalar Narain Dirichlet series is an Eisenstein product

- **ID:** W11-ND
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [W11 programme](../1-in-progress/ads3-scalar-modular-bootstrap.md)
- **Statement:** For all target moduli `ρ,σ∈ℍ` and `Re s>1`, the nonvacuum scalar mass series converges absolutely and satisfies
  `Σ'_(n·w=0) (M²_(ρ,σ)(n,w))^(−s)=2ζ(2s)E_s(ρ)E_s(σ)`.

## Proof

[PROVED HERE] Put `Q_z(c,d)=(c Im z)²+(c Re z+d)²` and let
`L_z`, `P_z`, `H_z` sum the normalized weight `(Im z)^s Q_z^(−s)` over
nonzero integer pairs, primitive pairs and pairs with positive first coordinate.
Quadratic coercivity gives absolute convergence for `Re s>1`.

Positive-gcd decomposition gives `L_z=ζ(2s)P_z=2ζ(2s)E_s(z)`.
Central reflection `(c,d)↦(-c,-d)` identifies the two half-planes.
The remaining axis contributes `2(Im z)^sζ(2s)`, so
`H_z=ζ(2s)[E_s(z)−(Im z)^s]`.

Separate zero winding from nonzero winding. The first sector contributes
`(Im ρ)^sL_σ`. Unique primitive scalar coordinates
`n=d(a,b)`, `w=c(-b,a)`, `c>0` give
`M²=Q_ρ(c,d)Q_σ(a,-b)/(Im ρ Im σ)`.
Reflection of the second primitive coordinate is a bijection; hence the
second sector contributes `H_ρP_σ`. Absolute convergence of both factors
justifies the charge reindexing and product of sums. Adding the two sectors
cancels the removed axis and gives the stated product.

## Lean

Namespace: `GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap`.

- `EpsteinLatticeDecomposition.lean`: `epstein_eq_eisenstein`,
  `epstein_halfPlane_split`, `halfEpstein_eq_eisenstein_sub`.
- `NarainDirichlet.lean`: `summable_narainDirichletTerm`,
  `narainDirichlet_eq_eisenstein_product`.

Both modules are in `ArithmeticScatteringHolography/ModularBootstrap/` and
imported by the topic umbrella. Direct `lake --old env lean` checks pass without warnings;
endpoint axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.

This formalizes the classical two-torus factorization in
[Benjamin–Collier–Fitzpatrick–Maloney–Perlmutter, §3.1](https://arxiv.org/html/2107.10744).
The [actual scalar Mellin formula](ads3-narain-scalar-mellin.md) is formalized
separately; identifying its continued pole kernel remains an obligation.

## Gates

- [x] 0 → 1: actual general-modulus scalar masses.
- [x] 1 → 2: absolutely convergent reindexing and exact axis cancellation.
- [x] 2 → 3: Lean compilation, transitive axiom audit and umbrella imports.
