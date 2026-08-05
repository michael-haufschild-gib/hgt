# Shilov envelope-correlation law: Lean layer complete (2026-08-05)

Card moved `2-fully-proven` → `3-formalized`:
`docs/drafts/pipeline/3-formalized/shilov-envelope-correlation-law.md`.

## What is now formalized (all in `GaloisForLFunctions.HTGeometry`, namespace
`GaloisForLFunctions.HTGeometry.BoundaryMigration`)

| Module | Content |
|---|---|
| `ShilovBoundaryMigrationDefect` (pre-existing) | escape/deficit defects, `RelativeQuotient`, derived inverse-limit law |
| `ShilovEnvelopeCorrelationLaw` (pre-existing) | `edgeJoin`, migration cochains, `(MR)` = `localMigrationSequence_shortExact` |
| `ShilovEnvelopeCorrelationPullback` (new) | `(EC)`, `(PB)`, `(FQ)`, `edgeJoin_least`, `(VE)`, entrywise matricial coupling |
| `ShilovCorrelationPathJoin` (new) | `relationalComp` + assoc, `ambiguousCorrelation`, one-step composition law, `(OL)`, `(PC)`, `(J)`, sharp strictness criterion |
| `ShilovSimplicialJoinSystem` (new) | `(SC)` over the nerve of an arbitrary small diagram, minimality, vertex/edge values, `H⁰(𝒬)` = correlations |
| `ShilovSimplicialJoinCohomology` (new) | `(SET)` + `(LES)` via cosimplicial modules and `alternatingCofaceMapComplex` |
| `ShilovTransmutationTower` (new) | algebraic core of `(UT)`: prescribed module = deficit = escape = composition excess = migration `H¹` |

All headline declarations audited: only `propext`, `Classical.choice`, `Quot.sound`.
`lake build GaloisForLFunctions.HTGeometry` green.

## Reusable Lean technique notes (cost these before re-deriving)

1. **The nerve is definitionally functorial.** `nerve C : SSet` has `map_id := rfl` and
   `map_comp := rfl` in mathlib.  Therefore `(nerve C).map (θ ≫ ψ).op υ` and
   `(nerve C).map θ.op ((nerve C).map ψ.op υ)` are *definitionally equal*, and so is the identity
   restriction.  This removes every transport/cast from a simplicial coefficient-system build.
2. **Do not prove the cosimplicial identities.** Build a genuine
   `CosimplicialObject (ModuleCat 𝕜)` (a functor out of `SimplexCategory`) and apply
   `AlgebraicTopology.alternatingCofaceMapComplex`; `d ∘ d = 0` comes for free.  Then
   `HomologicalComplex.shortExact_of_degreewise_shortExact` +
   `ModuleCat.shortComplex_shortExact` + `ShortComplex.ShortExact.δ / homology_exact₁₂₃` give the
   long exact sequence with no diagram chase.
3. **Factor the underlying linear map out of the functor.** Defining
   `cochainTransport θ : SimplexCochain n.len →ₗ SimplexCochain m.len` first and setting
   `map θ := ModuleCat.ofHom (cochainTransport θ)` avoids all `↑((X.obj n))`-vs-Pi coercion
   failures; `rw` cannot see through `CosimplicialObject.obj`.
4. **Morphisms of a preorder category are a subsingleton.** Equalities of composites of
   `ComposableArrows` transports are `(τ.map_comp _ _).symm.trans (congrArg _ (Subsingleton.elim _ _))`.
   Then push through `F` with `congrArg (fun g => ModuleCat.Hom.hom (F.map g))`; `rw` fails there
   because of dependent typing.
5. **Path recursion without `Nat.add_assoc`.** Define the source index by
   `pathSource m [] = m`, `pathSource m (d :: rest) = pathSource (m + d) rest`.  Then
   `pathSource m (d :: rest) = pathSource (m + d) rest` is `rfl`, and a `List ℕ`-indexed path of
   composable bonds needs no casts.  `towerMap bond m k : A (m + k) →ₗ A m` must recurse on the
   *second* argument (`m + (k+1) = (m+k)+1` is `rfl`).
6. **`abbrev`, not `def`, for a projection used inside `Submodule.map`.**  `simplexTip` had to be
   an `abbrev` or `rw [Submodule.map_id]` fails to match `F.obj (simplexTip σ)` against
   `F.obj (σ.obj (Fin.last p))`.
7. **`le_sup_left`/`le_sup_right` applied as coercions need a type ascription** when the lattice is
   `Submodule` and the metavariables are not yet fixed.

## Open on this card

Only gate 3 → 4: standalone paper, external novelty/priority audit, hostile review.  The Lean
layer is the exact algebraic core; the `C^*` statements (closedness, positivity, Shilov
minimality, the concrete `C([0,1],D)` transmutation construction) remain paper-level and are not
assumed anywhere in Lean.
