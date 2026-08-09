# Initial-execution symmetry inheritance and anomaly necessity — formalized

- **ID:** `initial-execution-symmetry-inheritance-and-anomaly-necessity-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `initial-execution-symmetry-inheritance-and-anomaly-necessity.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.SymmetryInheritance` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/SymmetryInheritance.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

Theorem 1 — initial objects inherit symmetry:

1. `initialCompare` — the canonical arrow `α_F : I ⟶ F I` of card `(2)`.
2. `initialCompare_unique` — it is the only such arrow, so the equivariant structure exists and is
   unique.
3. `initialCompare_id` — card `(3)`, first half: `α_1 = id`.
4. `initialCompare_comp` — card `(3)`, second half: the strict cocycle law
   `α_{F⋙F'} = α_{F'} ≫ F'(α_F)`.
5. `isInitialMap` — an autoequivalence sends an initial object to an initial object.
6. `isIso_initialCompare` — `α_F` is an isomorphism.
7. `initialIsoMap` — the resulting isomorphism `I ≅ F I`.

The card's strict action `F_1 = id`, `F_g F_h = F_{gh}` enters only through the two instances
`F = 𝟭` and `F = F ⋙ F'`, which items 3 and 4 state directly.  Stating them this way avoids
equalities of functors, which carry no mathematical content here.

Theorem 2 — equivariant execution lands in the fixed locus:

8. `smul_obs_initial` — for a group acting by autoequivalences and an isomorphism-invariant
   equivariant observation `P`, `g • P I = P I` for every `g`.
9. `not_free_orbit_obs_initial` — no free nontrivial orbit contains `P I`.
10. `stabilizer_obs_initial_eq_top` — the stabilizer of `P I` is the whole group.

Corollary 3 — the trilemma — is the contrapositive of items 8–10: with an equivariant doctrine and
an initial successor, the successor is equivariant; a non-equivariant canonical event therefore
requires either failure of the action (anomaly) or nonuniqueness (an orbit plus a selection rule).

Generator-commutator necessity:

11. `RadialFlow` — the radial flow `Γ_c` acting on each eigenspace of the grading operator
    `∂ = ∂_log` by a scalar, with eigenvectors spanning.
12. `commute_flow_of_commute_grading` — **card `(6)`, the necessary condition**: if
    `[d, ∂_log] = 0` then `d Γ_c = Γ_c d` for every `c`.
13. `grading_commutator_ne_zero` — the contrapositive: a differential that breaks radial
    equivariance must have `[d, ∂_log] ≠ 0`.

Card equations `(8)` and `(9)` are explicitly labelled placeholders on the paper card, not
theorems, and are not formalized.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/SymmetryInheritance.lean  # clean
lake build GaloisForLFunctions.HTGeometry                                                   # green
```

`#print axioms` on `initialCompare_comp`, `isIso_initialCompare`, `smul_obs_initial`,
`commute_flow_of_commute_grading` returns only `[propext, Classical.choice, Quot.sound]`.
