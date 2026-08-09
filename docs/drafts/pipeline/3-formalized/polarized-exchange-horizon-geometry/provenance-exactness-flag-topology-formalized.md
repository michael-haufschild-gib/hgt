# Provenance-exactness flag topology — Lean certificate

- **ID:** `provenance-exactness-flag-topology-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `provenance-exactness-flag-topology.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Module

`GaloisForLFunctions/HTGeometry/ExactnessFlagProvenanceTopology.lean`, namespace
`GaloisForLFunctions.HTGeometry`.  The flag space is the structure

```lean
structure ExFlag (R M) where
  boundary : Submodule R M
  cycle    : Submodule R M
  boundary_le_cycle : boundary ≤ cycle
```

with `instTopologicalSpace := generateFrom (provSubbasis R M)` for the two provenance tests
`boundaryTest v = {p | v ∉ p.boundary}` and `cycleTest v = {p | v ∈ p.cycle}`.

## Card statement to Lean name

| Card | Lean |
|---|---|
| item 1, `(11)`: negative tests generate the lower topology | `lower_submodule_eq_generateFrom` |
| item 1, `(12)`: positive tests generate the Scott topology | `scott_submodule_eq_generateFrom` |
| item 1: `(3)` is the mixed lower–Scott topology | `ExFlag.provTopology_eq_inf`, `ExFlag.provTopology_eq_induced_toMixed` |
| item 1: coarsest topology making every test open | `ExFlag.le_of_isOpen_tests` |
| item 2: `T₀` | `ExFlag.instT0Space` |
| item 2, `(5)`: specialization order | `ExFlag.specializes_iff` |
| item 3: `𝒰ᵥ` open | `ExFlag.isOpen_survival` |
| item 3, `(6)`: survival detects a nonzero class in `Z/B` | `ExFlag.mem_survival_iff_homologyClass_ne_zero` |
| item 3, `(7)` and `(14)`: homology dimension is monotone | `ExFlag.finrank_homology_add_finrank_boundary`, `ExFlag.finrank_homology_mono` |
| item 4: a cycle-only reporter is constant on the fibre | `ExFlag.eq_of_factorsThrough_cycle` |
| item 4: `𝒰ᵥ` separates `(B,Z)` from `(Z,Z)` | `ExFlag.exists_survival_separating` |
| item 5, `(9)`, `(15)`: pullback is continuous | `ExFlag.continuous_pullback` |
| item 5, `(10)`: pushforward along an injective map is continuous | `ExFlag.continuous_pushforward_of_injective` |
| item 5, `(16)`–`(17)`: pushforward along a plane projection is not | `ExFlag.not_continuous_pushforward_fst` |
| §4, `(20)`: rank-one initial provenance topology `{∅,{0},ℝ}` | `RHTower.isOpen_exchangeFlagHorizon_iff` |
| §5: provenance separation from false exactness | `ExFlag.exists_survival_separating` |

The generation theorems hold for the submodule lattice of an arbitrary module over an arbitrary
semiring; `T₀`, the specialization law, openness of the survival locus, functoriality, and the
projection no-go are proved at the same generality (the no-go over an arbitrary infinite field).
Dimension monotonicity is stated over a field with a finite-dimensional ambient space, as in the
card.

## Strengthening of the card's item 5

The card proves the pushforward no-go for `p : k² → k`.  The Lean proof factors it through a
strictly more general statement,

`ExFlag.not_isOpen_boundaryLe : u ∉ K → w ∈ K → w ≠ 0 → ¬ IsOpen {p | p.boundary ≤ K}`,

for any subspace `K` of any vector space over an infinite field that is neither zero nor
everything.  The plane projection is the instance `K = ker (fst)`; the dagger discontinuity of the
companion card is the instance `K = ker φ`.

## Scope of §5

The Poisson corollary instantiates item 4 at the carrier `(𝓑_P, Γ_sec)`.  Its transferable content
— that a strictly smaller boundary space is separated from its falsely exact companion by a framed
survival locus, while every cycle-only reporter identifies the two — is exactly
`ExFlag.exists_survival_separating` together with `ExFlag.eq_of_factorsThrough_cycle`, proved here
unconditionally for every flag with `B < Z`.  The carrier-specific input `𝓑_P ⊊ Γ_sec` belongs to
`deninger-cofinal-floquet-secondary-poisson-graph.md`, a separate stage-2 card, and is not restated
here.

## Axiom audit

`[propext, Classical.choice, Quot.sound]` for every declaration listed above.
