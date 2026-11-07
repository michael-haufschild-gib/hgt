# The actual scalar Narain projection has an Eisenstein-product Mellin transform

- **ID:** W11-NM
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [W11 programme](../1-in-progress/ads3-scalar-modular-bootstrap.md)
- **Statement:** For every target pair `ρ,σ∈ℍ` and `Re s>1`,
  `Mellin[y⁻¹∫₀¹ Z_(ρ,σ)(x,y) dx−1](s)=2π^(−s)Γ(s)ζ(2s)E_s(ρ)E_s(σ)`,
  where `Z` is the literal, absolutely convergent momentum-winding partition function.

## Proof

[PROVED HERE] The [scalar projection theorem](ads3-narain-partition-projection.md)
retains exactly the zero-spin charges. The vacuum has Boltzmann weight one;
splitting it from the convergent sum gives
`y⁻¹∫₀¹ Z(x,y) dx−1=Σ'_(n·w=0) exp(−πyM²(n,w))`.

Every remaining mass is positive. The norm of its Dirichlet term is
`(M²)^(−Re s)`, and these norms are summable by the
[general Narain Dirichlet theorem](ads3-narain-dirichlet-product.md).
For each charge the Mellin integral is `π^(−s)Γ(s)(M²)^(−s)`.
The integrals of the term norms are the summable weights
`π^(−Re s)Γ(Re s)(M²)^(−Re s)`; hence the full sum and integral commute.
Substituting the Dirichlet product gives the stated normalization.

## Lean

Module: `ArithmeticScatteringHolography/ModularBootstrap/NarainMellin.lean`.
Namespace: `GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap`.

- `summable_narainScalarHeatTerm`: actual nonvacuum scalar heat convergence.
- `narainScalarPartition_eq_heat`: exact vacuum removal.
- `mellin_narainScalarHeat`: Gamma factor times the actual mass Dirichlet series.
- `mellin_narainScalarHeat_eq_eisenstein_product`: Eisenstein normalization.
- `mellin_narainScalarProjection`: the formula starting from the partition-function integral.

The proof applies mathlib's `hasSum_mellin_pi_mul`; mass positivity, heat
convergence and absolute Dirichlet convergence discharge all its premises.
The direct `lake --old env lean` check passes without warnings.
All four endpoint axiom audits contain only `propext`, `Classical.choice`,
`Quot.sound`. The module is imported by the topic umbrella.

This is the classical two-torus scalar Mellin formula. The regularized
fundamental-domain overlap, modular inversion, normalization of the continued
pole kernel and the RH-strength remainder remain separate obligations.

## Gates

- [x] 0 → 1: actual partition projection, with the vacuum explicitly removed.
- [x] 1 → 2: positive masses and absolute Gamma-integral interchange.
- [x] 2 → 3: Lean proof, transitive axiom audit and umbrella import.
