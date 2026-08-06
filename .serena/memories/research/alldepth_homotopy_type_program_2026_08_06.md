# All-depth cusped building `(5)` — READ THIS FIRST

**2026-08-06 correction.  Most of what the rest of this file proposes to build already exists.**
`NerveHomotopy.lean` has `nerveHomotopyOfLE` (monotone `f ≤ g` gives homotopic nerves),
`nerveHomotopy` (a functor out of a cylinder gives a homotopy of the nerves of its ends),
`intervalIso`, `SSetDeformationRetract` and `SSetDeformationRetract.homologyIso`.
`CuspedHorizonHomotopy.lean` has `cuspDeformationRetract` and `cuspBuildingDeformationRetract`
as **`SSetDeformationRetract`s** — a strict section plus an `SSet.Homotopy` to the identity.
So the deformation-retraction half of `(5)` is already a homotopy-type statement, not a
homological one.  A duplicate module (`NerveOrderHomotopy.lean`) was written and then deleted.

Also false below: mathlib **does** have the nerve/standard-simplex iso, `stdSimplex.isoNerve`.

**What is actually open in `(5)`:** the *building's own* homotopy type — Solomon--Tits as a wedge
of `(N-2)`-spheres.  The corpus has it only homologically (`isZero_homology_building_of_ne`,
`isFreeOver_cuspHomology`, `not_isZero_cuspHomology_top`).  That is the real target, and it is a
substantially harder theorem than anything discussed below.

**Process lesson:** grep the corpus by *content* (`grep -rn "SSet.Homotopy" GaloisForLFunctions`)
and read the whole hit list — filename greps and truncated `head` output hid an entire existing
layer here.

---

# All-depth cusped building: the homotopy-type statement `(5)`

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/projective-horizon/projective-horizon-all-depth-cusped-building.md`

Picked 2026-08-06 after the symmetric-space-boundary card was finished and moved to
`3-formalized`.  Six gates `[x]`, two `[ ]`; one of the two is an external audit, so there is
exactly one open Lean item:

> `(5)` as a statement about *homotopy types*: `Δ_∞(V) ≃ ⋁ S^(N-2)`.

The homological content `(6)` is already proved (`cuspBuildingDeformationRetract`,
`cuspBuildingHomologyIso`, `isZero_homology_building_of_ne`).

## Why the card says it is blocked, and why it is not

The card records the blocker as: mathlib has no model structure on `SSet`
(`AlgebraicTopology/ModelCategory` and `AnodyneExtensions` are an unfinished upstream project),
and `SSet.Homotopy` is not symmetric for a non-fibrant target, so homotopies cannot be composed.

**Both observations are right and neither blocks the deformation-retraction statement.**  A
*strong deformation retract* needs no composition and no symmetry: it is a strict equation plus a
single homotopy in one direction.  So the honest target is

```text
r : N(P_∞) ⟶ N(building),  i : N(building) ⟶ N(P_∞),
r ∘ i = 𝟙  (strict),        SSet.Homotopy (i ≫ r) (𝟙 (N P_∞)).
```

That is a genuine homotopy-type statement, strictly stronger than a bare homotopy equivalence,
and it is exactly what the poset retraction of `(4)` gives.

## The tool to build

Everything reduces to one reusable lemma the corpus does not have and mathlib does not have:

> **a natural transformation `η : F ⟶ G` between functors `C ⥤ D` induces
> `SSet.Homotopy (nerve.map F) (nerve.map G)`.**

For posets this specialises to: `f ≤ g` pointwise (order-preserving) gives a simplicial homotopy
between the induced maps of order complexes — which applied to `ρ ≤ id` (collapse each deep vertex
to its endpoint) is the deformation retraction.

Two routes, both real work; the second is cleaner and reusable:

1. **By hand, degreewise.**  `(nerve C ⊗ Δ[1])_⦋n⦌ = (⦋n⦌ ⥤ C) × (⦋n⦌ ⟶ ⦋1⦌)`; send `(σ, φ)` to
   the functor `i ↦ if φ i = 0 then F (σ i) else G (σ i)`, with `η` supplying the crossing
   morphisms.  Functoriality is a case analysis; naturality in `⦋n⦌` is another.
2. **Interval category.**  Build `Δ[1] ≅ nerve (Fin 2)` once, use `nerve (C × E) ≅ nerve C ⊗ nerve E`,
   and take `nerve.map H` for the classifying functor `H : C × Fin 2 ⥤ D` of `η`.

## Verified against this toolchain (2026-08-06)

- `SSet.Homotopy f g` is a morphism `h : X ⊗ Δ[1] ⟶ Y` with `SSet.Homotopy.h₀ : ι₀ ≫ h = f` and
  `h₁ : ι₁ ≫ h = g`.  (`Mathlib/AlgebraicTopology/SimplicialSet/Homotopy.lean`.)
- `SSet`'s monoidal structure is `CartesianMonoidalCategory`, so `⊗` **is** the binary product —
  no comparison map needed.
- `nerve`, `nerveFunctor : Cat ⥤ SSet`, `nerveAdjunction`, `nerveFunctor.fullyfaithful` all exist
  (`NerveAdjunction.lean`).  `nerveFunctor` is a right adjoint, so it preserves binary products;
  that gives `nerve (C × E) ≅ nerve C ⊗ nerve E`.
- **`nerveAdjunction` is the name; there is no `CategoryTheory.nerveAdjunction`** — it lives in the
  `SSet`/root namespace of that file.
- `SSet.standardSimplex` does **not** exist under that name in this mathlib; it is `SSet.stdSimplex`.
- There is **no** `nerve ≅ stdSimplex` iso anywhere in mathlib — route 2 must build it.  The
  content is only `Monotone ↔ Functor` for finite ordinals: `Δ[1]_⦋n⦌ = (⦋n⦌ ⟶ ⦋1⦌)` and
  `nerve (Fin 2)_⦋n⦌ = (⦋n⦌ ⥤ Fin 2)` are the same monotone maps.

## Corpus state

The corpus already owns a large nerve/apartment layer (`Apartment*.lean`, ~12 modules) and
`CuspedDepthSlice.lean`.  Check those before adding anything; see also the memory
[[nerve-is-definitionally-functorial]].

## A stale-card finding worth keeping

`projective-horizon-rank-one-full-monodromy.md` says at its line ~278 "The remaining step is to
identify the fixed field of that action with the field generated by the centered coefficients".
**That is stale.**  `CenteredRootFieldTop.lean` already has `rootField_centeredMonicE_eq_top`,
`centeredRootFieldEquiv` and `centeredRootFieldPermEquiv` ("the Galois group of the centered
polynomial is the symmetric group on its roots"), and `CenteredGenericGalois.lean`,
`CenteredCoeffFieldRational.lean`, `CenteredPartSplittingField.lean` complete the chain.  Do not
re-derive it — read the repo, not the card body.


## Build progress 2026-08-06

`NerveOrderHomotopy.lean` (in the umbrella, `#print axioms` = `[propext]` only):

- `interpolate f g σ φ i = if φ i = 0 then f (σ i) else g (σ i)`
- `monotone_interpolate` — with `f, g` monotone, `f ≤ g` pointwise, `σ` monotone and `φ` monotone,
  the interpolation is monotone.  This is the **entire combinatorial content** of the homotopy:
  the three surviving cases are `(0,0)`, `(1,1)` and the single crossing `(0,1)`, where
  `f (σ i) ≤ g (σ i) ≤ g (σ j)`; the case `(1,0)` is excluded by monotonicity of `φ`.

## RESOLVED 2026-08-06: the homotopy is packaged

`nerveOrderHomotopy` in `NerveOrderHomotopy.lean` gives
`SSet.Homotopy (nerveMap hf.functor) (nerveMap hg.functor)` for monotone `f ≤ g`.  The API notes
below are what it took; keep them.

### How the friction was resolved

Packaging it as `SSet.Homotopy` stalls on elaborating the simplex-level map.  Facts established
by trying:

- `nerve C |>.obj Δ = ComposableArrows C Δ.unop.len` and `ComposableArrows C n = Fin (n+1) ⥤ C`.
- **`nerveMap F : nerve C ⟶ nerve D` already exists** (`SimplicialSet/Nerve.lean`, ~line 53) —
  do not rebuild it.
- `SSet.RelativeMorphism.Homotopy` has fields `h`, `h₀`, `h₁`, **and `rel`**; `SSet.Homotopy` is a
  `def` for the `⊥`-relative case, so structure-instance syntax must discharge `rel` too, and the
  `cat_disch` default does **not** fire.
- `(nerve P ⊗ Δ[1]).obj m ⟶ (nerve Q).obj m` will not `intro` and is not defeq to `→` at that
  transparency — but `↾fun x ↦ …` (the `asHom` idiom used in `Nerve.lean`) works, and **inside it
  the `.1`/`.2` projections do resolve**.  The failure earlier was elaboration order, not defeq.
- The interval coordinate is reached with `SSet.stdSimplex.asOrderHom (α : Δ[n].obj m) :
  Fin (m.unop.len + 1) →o Fin (n + 1)`; `α` itself is not directly applicable.
- `ext` on an equality of maps of nerves goes all the way down to equality of **objects** of
  `ComposableArrows` — do not reach for `Functor.ext`, and note that passing `Subsingleton.elim`
  as a term argument to it gets stuck on metavariables.
- `h₀`/`h₁` are not `rfl` (`nerveMap F` acts by `X ⋙ F`, the interpolation by `Monotone.functor`).
  What works: `ext m x i` then
  `show (if (0 : Fin 2) = 0 then f (x.obj i) else g (x.obj i)) = f (x.obj i)` and `simp`.
- `SSet.Homotopy`'s fourth field `rel` must be given: `ext m x; exact x.1.2.elim`.
