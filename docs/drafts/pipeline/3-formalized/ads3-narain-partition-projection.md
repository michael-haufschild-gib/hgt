# Convergence and scalar projection of the Narain partition function

- **ID:** W11-NP
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [W11 programme](../1-in-progress/ads3-scalar-modular-bootstrap.md)
- **Statement:** At every pair of target moduli and every positive worldsheet height, the actual momentum-winding partition sum converges absolutely. Translation by one preserves it, and its unit-interval average equals exactly the scalar charge sum, including the vacuum.

## Proof

[PROVED HERE] The explicit mass bound `|q|²≤KM²(q)` gives
`exp(−πyM²(q))≤exp(−π(y/K)|q|²)`. The latter sum factors into four
convergent integer Gaussian series. Every spin phase has norm one.

Integer spin gives translation invariance term by term. Each phase has
unit-interval integral one at zero spin and zero otherwise. The integrals
of the term norms are the summable Boltzmann weights, so integration
commutes with the full charge sum. The indicator sum is exactly the sum
over zero-spin charges.

## Lean

Module: `ArithmeticScatteringHolography/ModularBootstrap/NarainPartition.lean`.
Namespace: `GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap`.

- `summable_narainBoltzmann`: real Gaussian domination.
- `summable_norm_narainPartitionTerm`: absolute convergence.
- `narainPartition_add_one`: modular translation.
- `integral_narainPartition_eq_scalar`: actual scalar projection.

Direct `lake --old env lean` check passes without warnings. All four endpoint
axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.
The module is imported by the topic umbrella.

Modular inversion, the lattice Mellin identity and the RH-strength
small-height remainder are separate obligations.

## Gates

- [x] 0 → 1: literal momentum-winding source.
- [x] 1 → 2: Gaussian domination and integrable Fourier projection.
- [x] 2 → 3: direct Lean check and transitive axiom audit.
