# Primitive coordinates for scalar two-torus charges

- **ID:** W11-SC
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [W11 programme](../1-in-progress/ads3-scalar-modular-bootstrap.md)
- **Statement:** Integer charges `n,w∈ℤ²` with `n·w=0` and `w≠0` are in bijection with `c∈ℤ_{>0}`, primitive `(a,b)∈ℤ²`, and `d∈ℤ`, through `n=d(a,b)`, `w=c(−b,a)`.

## Proof

[PROVED HERE] Apply the positive-gcd decomposition to `(w₂,−w₁)`, obtaining
the unique positive integer `c` and primitive direction `(a,b)`.
Orthogonality gives `n₁b−n₂a=0`. Choose Bézout coefficients `A,B` with
`aA+bB=1`. Then `d=n₁A+n₂B` gives `n₁=da`, `n₂=db`.
Bézout also proves uniqueness of `d`. Conversely, these coordinates give
orthogonal charges and nonzero winding. Expanding the four squares yields

`|n|²+|w|²=(c²+d²)(a²+b²)`.

## Lean

Module: `ArithmeticScatteringHolography/ModularBootstrap/ScalarChargeCoordinates.lean`.
Namespace: `GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap`.

- `scalar_charge_parameters`: existence and uniqueness.
- `scalarChargeEquiv`: actual index bijection.
- `scalarParameters_energy`: energy factorization.

`lake --old env lean GaloisForLFunctions/ArithmeticScatteringHolography/ModularBootstrap/ScalarChargeCoordinates.lean` passes. Transitive `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`. Imported by the programme umbrella; no umbrella build.

This is the arithmetic parametrization underlying the classical central-charge-two
Narain transform, not a novelty claim or a proved transform identity. The zero-winding
sector, summability and infinite-sum reindexing remain in the programme card.

## Gates

- [x] 0 → 1: exact scalar-charge source.
- [x] 1 → 2: dependency-closed Bézout and gcd proof.
- [x] 2 → 3: exact theorem, direct Lean check and transitive axiom audit.
