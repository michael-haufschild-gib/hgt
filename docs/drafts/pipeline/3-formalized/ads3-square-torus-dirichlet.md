# Scalar Dirichlet series of the square two-torus

- **ID:** W11-SD
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [W11 programme](../1-in-progress/ads3-scalar-modular-bootstrap.md)
- **Statement:** For `Re s>1`, the nonvacuum scalar charge series converges absolutely and equals
  `S(s)=L(s)²/(2ζ(2s))=2ζ(2s)E(i,s)²`,
  where `L(s)=Σ'_(a,b)∈ℤ²(a²+b²)^(−s)` and `E` is the corpus's primitive Eisenstein series.

## Proof

[PROVED HERE] Separate zero winding from nonzero winding. The first sector
contributes `L`. The unique primitive scalar coordinates give the second
sector as `HP`, where `P` sums over primitive pairs and `H` over `c>0,d∈ℤ`.
Both factors are restrictions of the absolutely convergent Epstein series;
their product is absolutely summable, so the charge bijection preserves sums.

Positive-gcd decomposition gives `L=ζ(2s)P`. Splitting the first coordinate
into positive, negative and zero parts gives `L=2H+2ζ(2s)`.
Thus `S=L+HP=LP/2=L²/(2ζ(2s))`. Zeta is nonzero in this chamber.
Finally `P=2E(i,s)` gives the exact Eisenstein normalization.

## Lean

Module: `ArithmeticScatteringHolography/ModularBootstrap/SquareTorusDirichlet.lean`.
Namespace: `GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap`.

- `windingSplit`: exact zero/nonzero-winding index bijection.
- `summable_scalarDirichletTerm`: absolute convergence on `Re s>1`.
- `scalarDirichlet_eq_lattice_square`: Epstein quotient identity.
- `scalarDirichlet_eq_eisenstein_square`: actual primitive Eisenstein normalization.

Direct `lake --old env lean` check passes. All three endpoint axiom audits
contain only `propext`, `Classical.choice`, `Quot.sound`.

This formalizes the square-target specialization of the classical Narain
Dirichlet identity. It does not identify a regularized overlap integral,
prove the general-target identity, or establish the RH-strength remainder.

## Gates

- [x] 0 → 1: exact scalar-charge series.
- [x] 1 → 2: convergent reindexing and axis cancellation.
- [x] 2 → 3: direct Lean check and transitive axiom audit.
