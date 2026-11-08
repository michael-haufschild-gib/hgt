# Symmetry and modularity in all three Narain moduli

- **ID:** W11-N3
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [Poisson triality](../3-formalized/ads3-narain-modular-inversion.md)
- **Statement:** The actual partition `Z_(ρ,σ)(τ)` is symmetric in all
  three upper-half-plane variables and invariant under an independent
  modular transformation of each variable.

## Charge identity

The involution `(n₁,n₂,w₁,w₂)↦(w₁,n₂,n₁,w₂)` preserves spin.
Expansion of the target quadratic gives
`M²_(σ,ρ)(w₁,n₂,n₁,w₂)=M²_(ρ,σ)(n₁,n₂,w₁,w₂)`.
Reindexing therefore exchanges `ρ` and `σ`. Together with the momentum
Poisson exchange of `ρ` and `τ`, this generates all permutations.
Worldsheet modular invariance then transfers to either target variable.

The corpus search supplied target inversion and Poisson exchange, but
no corresponding mirror-charge identity. This is a symmetry theorem;
it supplies no scalar remainder estimate. A further target is the
[three-height averaged identity and lower bound](../0-backlog/ads3-narain-three-height-average.md).

## Gates

- [x] 0 → 1: explicit charge involution and polynomial identity identified.
- [ ] 1 → 2: mirror mass identity and three-variable modularity proved.
- [ ] 2 → 3: direct Lean checks, axiom audits and umbrella imports.
