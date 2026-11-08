# Symmetry and modularity in all three Narain moduli

- **ID:** W11-N3
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Poisson triality and worldsheet modularity](ads3-narain-modular-inversion.md)

## Theorem

The actual partition `Z(ρ,σ,τ)` is unchanged by each of the three
pairwise exchanges of upper-half-plane variables. For independent
`γ₁,γ₂,γ₃∈SL₂(ℤ)`,

`Z(γ₁ρ,γ₂σ,γ₃τ)=Z(ρ,σ,τ)`.

## Proof

The involution `(n₁,n₂,w₁,w₂)↦(w₁,n₂,n₁,w₂)` preserves spin.
Expansion of the target quadratic gives
`M²_(σ,ρ)(w₁,n₂,n₁,w₂)=M²_(ρ,σ)(n₁,n₂,w₁,w₂)`.
Reindexing the literal partition exchanges `ρ` and `σ`.

The proved momentum Poisson identity exchanges `ρ` and `τ`.
Composing these two exchanges also exchanges `σ` and `τ`.
Worldsheet modular invariance transfers through these identities to
both target variables. Applying the three invariances successively
gives the independent transformation law.

## Lean

- `NarainMirrorSymmetry`: `narainMassSq_mirror` and `narainPartition_mirror`.
- `NarainThreeModuli`: the three pairwise exchanges and `narainThreeModuli_modular`.

Both modules passed final direct Lean checks and are imported by the
umbrella. All five endpoint axiom audits contain only `propext`,
`Classical.choice` and `Quot.sound`.

This symmetry supplies no scalar remainder rate. The
[three-height averaged identity](../0-backlog/ads3-narain-three-height-average.md)
still requires triple angular norm integrability and integral interchanges.

## Gates

- [x] 0 → 1: charge involution and polynomial mass identity identified.
- [x] 1 → 2: all pairwise exchanges and independent modularity proved.
- [x] 2 → 3: final direct Lean checks, transitive axiom audits and umbrella imports.
