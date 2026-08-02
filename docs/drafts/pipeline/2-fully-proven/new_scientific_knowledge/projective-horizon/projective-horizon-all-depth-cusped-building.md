# The all-depth projective horizon space is a cusped spherical building

- **ID:** `projective-horizon-all-depth-cusped-building`
- **Stage:** 2-fully-proven
- **Type:** ALL-DEPTH INFORMATION TOPOLOGY / SOLOMON--TITS PERSISTENCE
- **Scientific status:** `[PROVED CONSEQUENCE] [NOVEL TOPOLOGICAL SYNTHESIS CANDIDATE]`
- **Parents:** `projective-horizon-solomon-tits-topological-charge`,
  `projective-horizon-one-sided-depth-transition`
- **Statement:** The complete nonconstant projective-horizon field poset over all derivative
  depths is obtained from the depth-one spherical Tits building by attaching one contractible
  infinite jet-tail cusp to every elementary horizon vertex. It deformation-retracts to the
  building and retains its Steinberg top homology, even though every fixed depth-two slice has
  only pairwise constant intersections.

## All-depth context poset

Let `X in P(V)` be differential-generic, with `dim V=N`. Exclude the source field `F`, the
constant field `C`, and the universal full-projective invariant core, exactly as in the reduced
Solomon--Tits context complex.

The depth-one part consists of

```text
mathcal I_S=F^(G_S),    0<S<V*,                           (1)
```

ordered by reverse inclusion of `S`. Its order complex is the spherical building
`Delta_Tits(V*)`.

For every line `ell subset V*`, corresponding to one hyperplane horizon, adjoin its strict jet
tail chain

```text
... < mathcal H_(ell,3) < mathcal H_(ell,2)
    < mathcal H_(ell,1)=mathcal I_ell.                    (2)
```

Call the resulting field poset `P_infinity(V)`.

## Classification theorem

The only order relations involving a depth-at-least-two tail are those in its own chain `(2)`.
More precisely, if `ell != ell'`, then

```text
mathcal H_(ell,m) intersection mathcal H_(ell',n)=C
```

whenever `max(m,n)>=2`. Likewise, if `ell<S` with `dim S>=2`, then

```text
mathcal H_(ell,m) intersection mathcal I_S=C,    m>=2.    (3)
```

Equation `(3)` follows by expressing `mathcal I_S` inside any distinct depth-one horizon whose
normal lies in `S` and applying the one-sided transition theorem.

Consequently `P_infinity(V)` is exactly the depth-one building poset with one disjoint infinite
chain attached below every rank-one vertex.

## Topological theorem

Let `Delta_infinity(V)` be the order complex of `P_infinity(V)`. The order complex of each chain
in `(2)` is an infinite simplex, hence contractible, and it meets the depth-one building only at
its endpoint vertex `mathcal I_ell`. Collapsing every such simplex to its endpoint gives a
deformation retraction

```text
Delta_infinity(V) -> Delta_Tits(V*).                      (4)
```

Therefore

```text
Delta_infinity(V) homotopy-equivalent to wedge S^(N-2),   (5)
```

and

```text
reduced H_j(Delta_infinity(V),Z)=0,       j != N-2,
reduced H_(N-2)(Delta_infinity(V),Z)=St_N(C).              (6)
```

The global all-depth horizon topology has the same Steinberg observer charge as the depth-one
building.

## Slice-versus-global phase law

There are two simultaneous facts.

1. At any fixed depth `n>=2`, distinct horizon vertices have constant meet. The reduced slice has
   no higher incidence simplices.
2. Across all depths, the strict tail of each observer remains attached to its depth-one vertex.
   These radial cusps add no homotopy and cannot kill the building's top class.

Thus topological information is concentrated in the depth-one incidence skeleton but remains a
global invariant of the complete depth filtration.

## Physical interpretation

Derivative depth behaves as a radial coarse-graining coordinate without becoming source time.

- the spherical building is the observer-incidence boundary where projective curvature is shared;
- each elementary observer has an infinite private cusp of progressively deeper derivative data;
- different cusps have no nonconstant overlap after either crosses depth two;
- all cusps jointly retract to the same boundary building, so the Steinberg charge is protected
  against radial extension.

This is an exact field-poset topology. It resembles a noncompact space with a topologically charged
boundary, but no metric, causal structure, gravity, entropy, or quantum dynamics is asserted.

## Novelty and significance audit

- Attaching contractible rays to a complex and the Solomon--Tits theorem are classical.
- The new candidate input is the exact heterogeneous-depth field classification, which proves
  that the full HT horizon poset has precisely this cusped form and no hidden cross-cusp fields.
- No checked source gives an all-depth derivative-horizon topology whose fixed slices collapse but
  whose global order complex retains a Steinberg class.

This card is a proved topological consequence; its novelty depends on the parent field theorem.
Its significance is conceptual: it reconciles depth-two information collapse with persistent
global topology in one exact structure.

## Lean boundary

The all-projective-dimension current mechanism enforcing cross-cusp constant meet is formalized in
`formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonArbitraryRankCurrentAlgebra.lean`.
`arOneSidedCurrentLie_eq_arPolynomialCurrentLie` identifies the finite one-sided generator packet
exactly with the complete polynomial root, diagonal, and transverse-shear current Lie algebra for
every finite projective dimension.  The local toolchain has no Solomon--Tits/order-complex homotopy
surface, so `(4)--(6)` are not added as assumptions.  This card remains in stage 2 for that
topological layer and the infinite rational fixed-field layer.

## RH impact audit

`[ORGANISING TOPOLOGY; NOT RH PROGRESS]` The scalar zeta source gives a family of private deep
projective tails attached to a depth-one celestial sphere of observer labels, with direct and
reciprocal cusps sharing only the Schwarzian at their boundary endpoints. No Steinberg-to-Weil
positivity map or zero-location mechanism is known.

## Gates

- [x] all heterogeneous-depth field intersections classified
- [x] all-depth poset decomposition proved
- [x] deformation retraction and Solomon--Tits homology deduced
- [x] formal order-complex topology — `(4)` and the homology half of `(6)`
- [ ] Solomon--Tits: the building's own homology is now proved concentrated off degree `N - 2`
  (`isZero_cuspHomology_of_ne`), so what is left here is the homotopy type `(5)` as a statement
  about homotopy types, and the Steinberg identification beyond definition and observer action
- [ ] independent specialist audit

## Log

- 2026-08-01 — **The classification theorem is formalized as a partial order.**
  `formal/GaloisForLFunctions/HTGeometry/CuspedHorizonPoset.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `CuspedVertex` is a vertex of `P_infinity(V)`: a nonzero proper subspace with a derivative depth,
  where any depth beyond the first is carried by a **line**.  The order is

  ```text
  v ≤ w  ↔  w.depth ≤ v.depth  ∧  (v at depth one → w.space ≤ v.space)
                                ∧  (v deeper     → w.space = v.space),
  ```

  reverse inclusion at depth one, and depth alone within a cusp.  That this is a partial order is the
  content: transitivity is where the classification enters, since a depth-one vertex below a line
  must be that line, which is `eq_of_le_line` — a nonzero subspace of a line is the line.  Without
  the line condition on deeper vertices the relation is not transitive.

  `space_eq_of_le_of_depth_ne_zero`, `not_le_of_space_ne`, `eq_space_of_le_depthOne` — a deeper
  vertex is comparable only to vertices carried by its own line; two deeper vertices on different
  lines are incomparable; a deeper vertex sits below a depth-one vertex only when that vertex is its
  own line.  Those are `(3)` and the statement around it: distinct cusps meet nowhere.

  `le_total_of_space_eq`, `isChain_cusp` — the vertices carried by one line are totally ordered, so
  each cusp is a chain: the "contractible infinite jet-tail cusp" in its order-theoretic form.

  So `P_infinity(V)` is proved to be the depth-one poset with one disjoint chain attached below each
  line, which is the card's classification theorem.  The gate `formal order-complex topology` stays
  open: the deformation retraction to the building and the persistence of the Steinberg class are
  homotopy statements, and the local toolchain has no order-complex homotopy theory.  A chain is
  contractible, but that sentence is not available here — what is available is that it is a chain.

- 2026-08-01 — **The simplices of `P_infinity(V)` decompose.**
  `formal/GaloisForLFunctions/HTGeometry/CuspedHorizonPoset.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `space_eq_of_chain_of_depth_ne_zero` — any two deeper vertices of a chain lie on the **same** line,
  so a simplex of the all-depth poset meets at most one cusp.  A simplex is therefore a simplex of the
  depth-one building with at most one cusp segment attached, which is the shape the retraction of the
  statement acts on.

  `card_image_depthOne_le` and `card_filter_depthOne_le` — the depth-one vertices of a chain form a
  flag, so there are at most `N - 1` of them, however deep the cusp segment runs
  (`eq_of_depthOne_of_space_eq` gives that a depth-one vertex is determined by its subspace, so the
  count of vertices and of their subspaces agree).

  That is the card's sentence "topological information is concentrated in the depth-one incidence
  skeleton" in the form available without homotopy: the cusps can be arbitrarily long, but they
  contribute no width — the number of depth-one vertices of any simplex is bounded by the building's
  dimension, and the cusp direction of a simplex is unique.

  The homotopy gate is unchanged: the retraction itself, and the persistence of the Steinberg class,
  need order-complex homotopy theory that the toolchain does not have.

- 2026-08-01 — **The retraction is constructed, as a closure operator.**
  `formal/GaloisForLFunctions/HTGeometry/CuspedHorizonPoset.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `cuspClosure : ClosureOperator (CuspedVertex K V)` — forgetting the depth of a vertex is monotone,
  increases every vertex, and is idempotent.  `range_cuspClosure` — its closed elements are exactly
  the depth-one vertices, so it retracts `P_infinity(V)` onto the building poset.

  This is more than the previous entries.  A closure operator is precisely the hypothesis of the
  standard poset-homotopy lemma: if a monotone map satisfies `x ≤ f x` and is idempotent, the order
  complex of the poset deformation-retracts onto the order complex of its image.  So the card's
  deformation retraction is no longer only asserted — its **whole combinatorial input** is now a
  Lean object, and the missing step is exactly one named topological lemma applied to it, rather
  than a construction that has to be found.

  The three properties are one-liners once the order is right: `le_retract` because depth only
  decreases downwards and the subspace is unchanged; `retract_monotone` because a depth-one vertex
  compares by reverse inclusion and a deeper one has its subspace fixed, so both cases give
  `w.space ≤ v.space`; `retract_idem` definitionally.

  Gate status.  `formal order-complex topology` stays open, but its content is now narrow: the poset,
  its classification, its simplex decomposition, and the retracting closure operator are all
  formalized; what is missing is the homotopy lemma that converts a closure operator into a
  deformation retraction, and the Steinberg identification that rides on it.

- 2026-08-01 — **The retract is identified as the building poset.**
  `formal/GaloisForLFunctions/HTGeometry/CuspedHorizonPoset.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `depthOneOrderIso` — an **order isomorphism**

  ```text
  {depth-one vertices of P_infinity(V)}  ≃o  {nonzero proper subspaces}ᵒᵈ,
  ```

  the depth-one skeleton with its field order being the subspace poset under reverse inclusion.  So
  the closed part of `cuspClosure` is not merely a set in bijection with the building's vertices: it
  is the depth-one building poset, with its order.

  Combined with the previous entry, the card's first sentence is now formalized except for its
  homotopy content: `P_infinity(V)` is the depth-one poset with one chain attached below each line
  (classification), a closure operator retracts it onto the depth-one part (retraction), and that
  part is order-isomorphic to the building poset (identification of the retract).  What the
  statement adds beyond this is that the retraction is a deformation retraction of order complexes
  and that the Steinberg top homology survives — the two homotopy claims, which remain outside the
  toolchain.

- 2026-08-01 — **The deformation retraction is constructed at the level of poset maps.**
  `formal/GaloisForLFunctions/HTGeometry/CuspedHorizonPoset.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `cuspHomotopy : (CuspedVertex K V × Bool) →o CuspedVertex K V` — a **monotone** map

  ```text
  P_infinity(V) × [1] → P_infinity(V),
  ```

  equal to the identity at one end of the interval (`cuspHomotopy_false`) and to the retraction at the
  other (`cuspHomotopy_true`).  This is an elementary homotopy in the combinatorial sense, and it is
  what the deformation retraction of the statement is, before any topology is applied.

  Monotonicity in the time coordinate is exactly `x ≤ retract x`; in the vertex coordinate it is
  exactly that the retraction is monotone; the mixed case is the composite of the two.  The
  order-reversed pair of times is excluded by the interval's own order.

  What this leaves is genuinely general rather than specific to this poset: the nerve of a monotone
  map `P × [1] → P` realises to a homotopy of `|P|`, so the card's deformation retraction follows
  from `cuspHomotopy` by a fact about geometric realisation, not by anything further about horizons.
  The Steinberg identification of `(6)` on the parent card is a separate homotopy input and is
  untouched by this.

- 2026-08-01 — **The homotopy in categorical form; and the toolchain has more than assumed.**
  `formal/GaloisForLFunctions/HTGeometry/CuspedHorizonPoset.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `retractFunctor` and `cuspHomotopyFunctor` — the retraction and the elementary homotopy as
  **functors** of the poset viewed as a category, the second out of `P_infinity(V) × [1]`.
  `unitToRetract` — a natural transformation from the identity to the retraction: in a poset every
  diagram commutes, so the inequality `x ≤ retract x` already **is** natural, and naturality is
  `Subsingleton.elim`.

  A correction to the earlier entries.  They record the retraction as blocked on absent order-complex
  homotopy theory.  That was checked too shallowly: mathlib has `SSet.Homotopy` — homotopies of
  simplicial sets as a morphism `X ⊗ Δ[1] ⟶ Y` with its two endpoints — the nerve of a category, the
  nerve adjunction, geometric realisation through `SimplicialSet/TopAdj`, and `Monotone.functor` for
  turning a poset map into a functor.  What is genuinely missing is not the notion of homotopy but the
  bridge `nerve (C × [1]) ≅ nerve C ⊗ Δ[1]`, which is what would turn `cuspHomotopyFunctor` into an
  `SSet.Homotopy` between the nerve of the identity and the nerve of the retraction.

  So the gate is narrower again: the poset, its classification, the simplex decomposition, the closure
  operator, the elementary homotopy, the identification of the retract as the building poset, and now
  all three of these as categorical data are formalized.  The remaining step is a general fact about
  nerves and products, not anything further about horizons.

- 2026-08-01 — **Attempted the nerve bridge; stopped at the bundling, nothing landed.**

  The remaining step identified in the previous entry is the comparison
  `nerve (C × [1]) ≅ nerve C ⊗ Δ[1]`.  Simplicial sets are `CartesianMonoidalCategory`, so the tensor
  **is** the product and the comparison map is the lift of the two projections' nerves — mathematically
  a two-line construction.  In Lean it did not land: `nerveFunctor` is a functor out of the bundled
  `Cat`, and a plain functor `C × D ⥤ C` is not accepted as a morphism `Cat.of (C × D) ⟶ Cat.of C`
  without the bundling coercion, which is not `Cat.homOf` in this toolchain.  Two attempts failed on
  that point and the file was removed rather than left broken.

  Recorded so the next attempt starts from the right place: the obstacle is `Cat`-bundling plumbing,
  not the mathematics, and the mathematical content of the gate is unchanged from the previous entry.

- 2026-08-01 — **The nerve bridge lands.**
  `formal/GaloisForLFunctions/HTGeometry/NerveProductComparison.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `nerveProductComparison` — the canonical map from the nerve of a product of categories to the
  tensor of the nerves, the lift of the two projections' nerves; `nerveProductComparison_fst` and
  `_snd` identify its components.  `PreservesLimits nerveFunctor` — the nerve preserves limits, being
  the right adjoint of `nerveAdjunction`, so that comparison is an isomorphism.

  The obstacle recorded in the previous entry was the `Cat` bundling, and the missing piece was
  `CategoryTheory.Functor.toCatHom`, which turns a functor into a morphism of the bundled category
  `Cat`.  With it the construction is the two lines it should be.

  What this gives the card: `cuspHomotopyFunctor` is a functor `P_infinity(V) × [1] ⥤ P_infinity(V)`,
  its nerve is a map out of `nerve (P × [1])`, and the comparison above identifies that source with
  `nerve P ⊗ Δ[1]` once `Δ[1]` is recognised as the nerve of the interval.  That last identification
  is the only step still missing before the deformation retraction is an `SSet.Homotopy` in mathlib's
  own sense.

- 2026-08-01 — **The last named gap is not a gap: mathlib has the standard simplex as a nerve.**
  `formal/GaloisForLFunctions/HTGeometry/CuspedHorizonPoset.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  The previous entry left one step: recognising `Δ[1]` as the nerve of the interval.  mathlib has it —
  `SSet.stdSimplex` carries `(Δ[n] : SSet.{u}) ≅ nerve (ULift.{u} (Fin (n + 1)))`.

  `cuspHomotopyInterval` — the elementary homotopy restated over `ULift (Fin 2)`, the preordered type
  whose nerve is that simplex, so the poset-level data now matches mathlib's model of the interval
  rather than the ad hoc `Bool`.  `cuspHomotopyInterval_zero` fixes the identity endpoint.

  Every ingredient of the card's deformation retraction is therefore present: the homotopy as a
  functor out of `P_infinity(V) × [1]`, the comparison identifying the nerve of a product with the
  tensor of nerves and its being an isomorphism, and the identification of `Δ[1]` as the nerve of the
  interval.  What is left is to compose them into a term of type `SSet.Homotopy`, which is assembly of
  named pieces.

  This supersedes the earlier entries' claim that the toolchain lacks order-complex homotopy theory.
  It lacks an `OrderComplex`, but the nerve serves that role and the surrounding theory is present.

- 2026-08-01 — **The homotopy's target shape, and the one input it rests on.**
  `formal/GaloisForLFunctions/HTGeometry/NerveProductComparison.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `nerveTensorMap` — a functor out of a product induces a map out of the tensor of the nerves,

  ```text
  (C × D ⥤ E)  ↦  nerve C ⊗ nerve D ⟶ nerve E,
  ```

  which with `D` the interval is exactly the shape of a homotopy of simplicial sets.
  `nerveProductComparison_comp_nerveTensorMap` records that it is a section of the comparison.

  The construction takes `IsIso (nerveProductComparison C D)` as an instance argument, and that is now
  the only input the card's deformation retraction rests on.  It is true — the nerve preserves limits
  (recorded in the previous entry) and `Cat` has all limits (`CategoryTheory.Category.Cat.Limit`) — but
  deriving it needs the identification of the product in `Cat` with `Cat.of (C × D)` and of the
  cartesian-monoidal tensor with the categorical product, which is mathlib-specific plumbing rather
  than mathematics.

  Applying `nerveTensorMap` to `cuspHomotopyInterval` viewed as a functor, and reading its two
  endpoints, then gives the `SSet.Homotopy` between the nerve of the identity and the nerve of the
  retraction.  That is the whole remaining content of the card's deformation retraction.

- 2026-08-01 — **Audit note.**  All modules of this card's chain build:
  `CuspedHorizonPoset`, `NerveProductComparison`, together with the flag machinery they rest on
  (`ProjectiveFlagDimension`), every result depending only on `propext`, `Classical.choice`,
  `Quot.sound`.

  The `HTGeometry` umbrella itself does **not** build, for a reason unrelated to this card: two
  modules owned by other work, `UpperEndGammaElement` and `RelativeTwoShiftGaugeCharacterization`,
  both declare `deriv_algebraMap_complex` in the same namespace, so the umbrella cannot import both.
  They are genuinely different theorems — one about `upperEndMeroField`, the other about
  `meroField Set.univ` — and nine further modules reference the name, all resolving to the second.
  The minimal fix is to rename the declaration and its single use inside `UpperEndGammaElement`.
  Not done here: that file belongs to other work and was under active build, and a rename landing on
  top of in-flight edits is worse than the report.

- 2026-08-01 — **The deformation retraction is now a simplicial homotopy, unconditionally.**
  Three new modules, all axioms `[propext, Classical.choice, Quot.sound]`:

  `formal/GaloisForLFunctions/HTGeometry/NerveProductComparison.lean`
  — `isIso_nerveProductComparison`: the comparison map from the nerve of a product of categories to
  the tensor of the nerves is an isomorphism.  Proof: `catProdIsLimit` exhibits `Cat.of (C × D)` as a
  binary product in `Cat`; the nerve is a right adjoint, so it carries that to a binary product of
  simplicial sets; the tensor is the categorical product; the comparison commutes with both
  projections, hence is the canonical map between two limit cones.  The hypothesis `[IsIso …]` that
  `nerveTensorMap` previously carried is discharged and removed.

  `formal/GaloisForLFunctions/HTGeometry/NerveHomotopy.lean`
  — `nerveHomotopy`: **a functor out of a cylinder `C × [1]` is a simplicial homotopy between the
  nerves of its two ends**, as an `SSet.Homotopy`.  The interval is `ULift (Fin 2)`, whose nerve is
  `Δ[1]`.  The two endpoint identifications rest on `nerveFunctor_map_const` (the nerve of a constant
  functor is a constant simplicial map) and on the vertices of `stdSimplex.isoNerve 1`.  Mathlib has
  simplicial homotopies and the nerve, but does not connect them; this is the missing bridge.
  — `prodPreorderFunctor`: a monotone map out of a product of preorders as a functor out of the
  product *category*.  The preorder on a product and the product of the two preorder categories are
  different category structures on the same type, and a cylinder needs the latter.

  `formal/GaloisForLFunctions/HTGeometry/CuspedHorizonHomotopy.lean`
  — `cuspCylinder_zero`, `cuspCylinder_one`: the cusp deformation's two ends are the identity and the
  retraction.
  — `cuspNerveHomotopyId`: **the identity of the nerve of the all-depth cusped poset is simplicially
  homotopic to the nerve of the retraction onto the depth-one skeleton.**

  With `depthOneOrderIso` identifying that skeleton with the building poset, the topological bullet
  of `(3)` is now proved in the simplicial category and no longer only at the level of poset maps.
  What remains for the card is the Steinberg identification, which is a separate statement.

- 2026-08-01 — **`(4)` is proved, and with it the homology half of `(6)`.**
  `formal/GaloisForLFunctions/HTGeometry/CuspedHorizonHomotopy.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  cuspBuildingDeformationRetract :
    SSetDeformationRetract (nerve P_∞(V)) (nerve {S : S ≠ ⊥ ∧ S ≠ ⊤}ᵒᵈ)
  ```

  a **strong deformation retraction of the order complex of the all-depth cusped poset onto the
  order complex of the building** — the inclusion is a section of the retraction on the nose
  (`depthOneIncl_comp_cuspRetract`), and the other composite is simplicially homotopic to the
  identity (`cuspNerveHomotopyId`).  The target is the poset of nonzero proper subspaces under
  reverse inclusion itself, reached through `depthOneNerveIso`, which is `depthOneOrderIso`
  transported to nerves by `orderIsoNerveIso`.  This is `(4)`.

  ```text
  cuspBuildingHomologyIso : H_n(Δ_∞(V); R) ≅ H_n(Δ_Tits(V*); R)
  ```

  in **every** degree and with **any** coefficient object, from
  `SSetDeformationRetract.homologyIso` and mathlib's homotopy invariance of simplicial homology.
  So the cusps contribute nothing to homology: the card's sentence "these radial cusps add no
  homotopy and cannot kill the building's top class" is now a theorem, not an assertion, in its
  homological form.

  What `(5)` and `(6)` still need is the *building's own* homotopy type — Solomon--Tits — which is a
  statement about `Δ_Tits(V*)` alone and involves nothing about depth or cusps.  The card's own
  contribution, that the all-depth structure has the same topology as the depth-one one, is proved.
  The `formal order-complex topology` gate is closed; the remaining gate is Solomon--Tits itself.

  Supporting infrastructure, all in
  `formal/GaloisForLFunctions/HTGeometry/NerveHomotopy.lean`:
  `SSetDeformationRetract` (structure), `SSetDeformationRetract.homologyIso`, `orderIsoCatIso`
  (an order isomorphism is an isomorphism in `Cat`), `orderIsoNerveIso`.

- 2026-08-01 — **The vanishing half of `(6)` above the top degree.**
  `formal/GaloisForLFunctions/HTGeometry/CuspedHorizonHomotopy.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  isZero_cuspHomology :  N - 1 ≤ n  →  H_n(Δ_∞(V); R) = 0
  ```

  for any coefficient object.  This is the first half of

  ```text
  reduced H_j(Δ_∞(V)) = 0,   j ≠ N - 2
  ```

  and it is not visible on `Δ_∞(V)` itself: that complex is **infinite dimensional**, since every
  cusp is an infinite chain and so carries nondegenerate simplices in every degree.  The vanishing
  is transported from the building through `cuspBuildingHomologyIso`, where it is a dimension count:
  `buildingHasDimensionLT` says the order complex of the building has dimension below `N - 1`,
  because a nondegenerate simplex is a strict chain of nonzero proper subspaces and
  `card_le_finrank_sub_one` bounds such a chain by `N - 1`.

  So the card's "the cusps add no homotopy" now has a sharp consequence that its own geometry cannot
  see: an infinite-dimensional complex with homology concentrated below degree `N - 1`.

  Supporting infrastructure in `NerveHomotopy.lean`: `isZero_homology_of_hasDimensionLT` (homology
  vanishes above the dimension, via mathlib's normalized chain complex) and
  `hasDimensionLT_nerve_of_chain_bound` (a bound on strict chains bounds the dimension of a nerve).

  What remains of `(5)`--`(6)` is entirely about the building itself: that its reduced homology
  vanishes *below* `N - 2` and is the Steinberg module in degree `N - 2` — Solomon--Tits, which
  mentions neither depth nor cusps.

- 2026-08-02 — **Degree zero, and `(6)` complete for `N = 3`.**
  `formal/GaloisForLFunctions/HTGeometry/CuspedHorizonHomotopy.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  buildingZigzag       :  3 ≤ N  →  any two vertices of the building are joined by a zigzag
  buildingIsConnected  :  3 ≤ N  →  SSet.IsConnected (nerve Δ_Tits(V*))
  cuspHomologyZeroIso  :  3 ≤ N  →  H_0(Δ_∞(V); R) ≅ R
  ```

  The zigzag is uniform and short: pick a line in each of the two subspaces and join them through
  the plane the two lines span, which is a proper subspace exactly because `N ≥ 3`.  Four steps, no
  case split on whether the two subspaces meet.  Vanishing of **reduced** `H_0` is the `j = 0` case
  of the card's homology statement.

  Together with `isZero_cuspHomology` this settles `(6)` **completely for `N = 3`**: there
  `N - 2 = 1`, the homology vanishes in degrees `≥ 2` by the dimension bound and in degree `0` by
  connectedness, so it is concentrated in degree `1`, as claimed.

  For `N ≥ 4` what is left is the intermediate range `1 ≤ j ≤ N - 3`, that is, the
  `(N-3)`-connectedness of the building.  That is Solomon--Tits proper and it is a statement about
  `Δ_Tits(V*)` alone.

  Supporting infrastructure in `NerveHomotopy.lean`: `nerveEdgeOfLE`, `pi0_mk_eq_of_comparable`,
  `isPreconnected_nerve_of_zigzag`, `zigzag_orderDual`.

- 2026-08-02 — **A poset-homotopy toolkit, and the cusps are proved contractible.**
  `formal/GaloisForLFunctions/HTGeometry/NerveHomotopy.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  nerveHomotopyOfLE        :  f ≤ g pointwise  →  SSet.Homotopy (nerve f) (nerve g)
  isZero_homology_of_conical:  id ≤ F ≥ const p₀  →  H_n = 0 for n ≥ 1
  isZero_homology_of_orderTop / _of_orderBot
  ```

  `nerveHomotopyOfLE` is the poset case of "a natural transformation induces a simplicial homotopy of
  nerves": the cylinder `leCylinder f g h` sends `(x, 0) ↦ f x` and `(x, 1) ↦ g x`, and is monotone
  exactly because `f x ≤ f y ≤ g y`.  It is the engine behind every contractibility statement, and
  the earlier cusp retraction is its first instance.

  A caution recorded from the build: `SSet.Homotopy` is **not** an equivalence relation for general
  simplicial sets — mathlib supplies no `symm` or `trans`, correctly, since composing homotopies needs
  a Kan condition.  So conical contractibility cannot be assembled as a chain of homotopies; it is
  assembled one level down, where `homologyMap` equality *is* symmetric and transitive.  Both
  `nerveHomotopyConst_of_orderTop` and `nerveHomotopyConst_of_orderBot` are genuine single homotopies
  and are stated as such; the conical case is stated on homology.

  Applied to the card, in `CuspedHorizonHomotopy.lean`:

  ```text
  isZero_homology_cusp :  S ≠ ⊥ → S ≠ ⊤ → H_n(nerve {v : v.space = S}) = 0 for n ≥ 1
  ```

  **each cusp is contractible.**  The earlier entry recorded that "a chain is contractible, but that
  sentence is not available here — what is available is that it is a chain".  It is available now:
  the cusp has a greatest element, the depth-one vertex it hangs from, and a poset with a greatest
  element has a contractible nerve.  This is the card's own sentence about `(2)`, proved.

  `isZero_homology_above` records the same for the subspaces above a fixed one, which is the
  contractible piece any Solomon--Tits induction glues along.

- 2026-08-02 — **First stone of Mayer--Vietoris: the coproduct splitting.**
  `formal/GaloisForLFunctions/HTGeometry/CoproductMayerVietoris.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  mvSplitting  : (mvShortComplex R S₁ S₂).Splitting          -- needs S₁ ∪ S₂ = univ
  mvShortExact : (mvShortComplex R S₁ S₂).ShortExact
  ```

  For a set covered by two subsets, the coproducts over the four sets form a **split** short exact
  sequence

  ```text
  0 → ∐_{S₁ ∩ S₂} R → (∐_{S₁} R) ⊞ (∐_{S₂} R) → ∐_{S} R → 0
  ```

  in any preadditive category with a zero object, binary biproducts and coproducts.  The retraction
  keeps only the basis elements of the intersection; the section sends a basis element to the first
  summand when it lies in the first subset and to minus the second otherwise.

  Two facts worth recording from the proof.  The identity `r ≫ f + g ≫ s = 𝟙` holds **without** the
  covering hypothesis — the cover is needed only for `s` to be a section of `g`, since that is the
  only place a basis element outside `S₁` has to be found in `S₂`.  And the sequence is split
  *degreewise only*: the retraction is not a chain map, because a face of a simplex outside the
  intersection can land inside it, which is exactly why Mayer--Vietoris needs the degreewise-split
  criterion rather than a splitting of complexes.

  This is the identified obstruction to the remaining range `1 ≤ j ≤ N - 3` of `(6)`, taken one step
  down: the chain complex of a simplicial set is a coproduct over its simplices in each degree, and
  two subcomplexes covering it cover the simplices of each degree, so this is the degreewise input to
  the Mayer--Vietoris short exact sequence of chain complexes.  What remains before the long exact
  sequence is to identify the chain complex of a subcomplex with the coproduct over its simplices,
  check that the two maps are chain maps, and pass from degreewise short exactness to short exactness
  of complexes.

- 2026-08-02 — **Mayer--Vietoris, second step: chains on a subcomplex are the coproduct over its
  simplices.**  `formal/GaloisForLFunctions/HTGeometry/SimplicialMayerVietoris.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  chainComplex_X_eq         :  ((A : SSet).chainComplex R).X n = subCoproduct R (A.obj ⦋n⦌)
  chainComplexMap_ι_f       :  (chainComplexMap A.ι R).f n = inclFull R (A.obj ⦋n⦌)
  chainComplexMap_homOfLE_f :  (chainComplexMap (homOfLE h) R).f n = inclCop R …
  subcomplex_obj_union      :  A ⊔ B = ⊤  →  A.obj ⦋n⦌ ∪ B.obj ⦋n⦌ = univ
  subcomplex_obj_inter      :  (A ⊓ B).obj ⦋n⦌ = A.obj ⦋n⦌ ∩ B.obj ⦋n⦌
  ```

  The first and the last two are **definitional** — mathlib's `ιChainComplex` is literally
  `Sigma.ι`, and `Subcomplex` meets and joins are computed degreewise — so the coproduct splitting
  of the previous entry applies to the chain objects with no transport at all.  The two chain-map
  identifications need one step each, from `ι_chainComplexMap_f`.

  The total object was refactored from `∐_{↥univ} R` to `∐_{T} R` so that it matches
  `(X.chainComplex R).X n` on the nose; that removed every reindexing iso the assembly would
  otherwise have needed, and simplified the splitting proofs as a side effect.

  Remaining before the long exact sequence: the biproduct of chain complexes degreewise (mathlib's
  `HomologicalComplexBiprod` — it is *not* definitional, unlike everything above), and the passage
  from degreewise short exactness to short exactness in `ChainComplex C ℕ`.

- 2026-08-02 — **The Mayer--Vietoris short exact sequence of chain complexes is proved.**
  `formal/GaloisForLFunctions/HTGeometry/SimplicialMayerVietoris.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  mvChainShortExact :  A ⊔ B = ⊤  →  (mvChainShortComplex X R A B).ShortExact
  ```

  for two subcomplexes `A B` of a simplicial set `X` covering it, with coefficients in any abelian
  category with coproducts.  The short complex is

  ```text
  C(A ⊓ B) --(incl, incl)--> C(A) ⊞ C(B) --(incl - incl)--> C(X).
  ```

  Assembly: `mvChainFst_f` and `mvChainSnd_f` identify the two chain maps in each degree with the
  maps of the coproduct short complex, through `HomologicalComplex.biprodXIso`;
  `mvChainShortComplexIso` packages that as an isomorphism of short complexes;
  `ShortComplex.shortExact_of_iso` transports the splitting, and mathlib's
  `HomologicalComplex.shortExact_of_degreewise_shortExact` lifts degreewise short exactness to short
  exactness of complexes.

  The obstruction named three entries ago is therefore removed.  With
  `HomologicalComplex.HomologySequence` this yields the Mayer--Vietoris long exact sequence, which is
  the tool the remaining range `1 ≤ j ≤ N - 3` of `(6)` needs: the induction glues the contractible
  star of a line (`isZero_homology_above`) to the complement along the link.

- 2026-08-02 — **Mayer--Vietoris vanishing, the form the induction consumes.**
  `formal/GaloisForLFunctions/HTGeometry/SimplicialMayerVietoris.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  isZero_homology_of_mayerVietoris :
    A ⊔ B = ⊤ → (down ℕ).Rel i j →
    H_i(A) = 0 → H_i(B) = 0 → H_j(A ⊓ B) = 0 → H_i(X) = 0
  ```

  Two covering subcomplexes with no homology in degree `i`, whose intersection has none in degree
  `i - 1`, force the whole simplicial set to have none in degree `i`.  This is exactness of

  ```text
  H_i(C(A) ⊞ C(B)) → H_i(C(X)) --δ--> H_{i-1}(C(A ⊓ B))
  ```

  at the middle term, from mathlib's `homology_exact₃` applied to the short exact sequence of the
  previous entry, with both ends zero.  `isZero_homology_biprod` supplies the left end: the homology
  of a biproduct of complexes vanishes when both summands' does, proved from `biprod.total` and
  additivity of `homologyMap` — mathlib does not register `PreservesBinaryBiproduct` for the homology
  functor, so `mapBiprod` is unavailable and the direct route is shorter anyway.

  The Mayer--Vietoris chain is now complete end to end: coproduct splitting → degreewise identification
  → short exact sequence of complexes → vanishing criterion.  What the remaining range
  `1 ≤ j ≤ N - 3` of `(6)` needs from here is purely the combinatorial induction on the building:
  cover the order complex by the star of a line (contractible, `isZero_homology_above`) and the
  complement, and identify the intersection with the link.

- 2026-08-02 — **The combinatorial side: full subcomplexes of an order complex.**
  `formal/GaloisForLFunctions/HTGeometry/NerveSubcomplex.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  nerveSubcomplex Q             -- the simplices all of whose vertices lie in Q
  nerveSubcomplexIso            :  (nerveSubcomplex Q : SSet) ≅ nerve ↥Q
  nerveSubcomplex_inter         :  nerveSubcomplex (Q₁ ∩ Q₂) = nerveSubcomplex Q₁ ⊓ nerveSubcomplex Q₂
  nerveSubcomplex_star_sup_compl:  (∀ q ≤ p, q = p) →
                                   nerveSubcomplex {q | p ≤ q} ⊔ nerveSubcomplex {q | q ≠ p} = ⊤
  ```

  `nerveSubcomplexIso` is the bridge: a full subcomplex **is** the order complex of the subposet it
  spans, so every poset-level result — conical contractibility, `orderTop`/`orderBot` — transfers to
  it, through `nerveSubcomplexHomologyIso`.

  `nerveSubcomplex_star_sup_compl` is the decomposition the Solomon--Tits induction uses, and its
  proof is the only place the minimality of the chosen element matters: a simplex either avoids `p`,
  and then lies in the complement, or contains `p` at some vertex, and then **every** vertex is
  comparable to `p`, hence above it by minimality, so the whole simplex lies in the star.  For the
  building, `p` a line is minimal exactly because a nonzero subspace of a line is the line.

  With `nerveSubcomplex_inter` the intersection of the two pieces is the full subcomplex spanned by
  `{q | p ≤ q} ∩ {q | q ≠ p}` — the **link** of `p`, which for a line `L` in the building is the
  poset of subspaces strictly between `L` and `V`.  That poset is the building of `V/L`, one
  dimension down: the induction step.

- 2026-08-02 — **Mayer--Vietoris for an order complex, cut at a minimal element.**
  `formal/GaloisForLFunctions/HTGeometry/NerveMayerVietoris.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  isZero_homology_nerve_of_minimal' :
    p minimal → 1 ≤ i → (down ℕ).Rel i j →
    H_i(Δ(P ∖ {p})) = 0 → H_j(Δ({q | p < q})) = 0 → H_i(Δ(P)) = 0
  ```

  The star of `p` contributes nothing because it has a least element (`isZero_homology_star`); the two
  pieces cover because `p` is minimal; and they meet in the link `{q | p < q}`.  Every ingredient
  named in the previous four entries is used here, and nothing is assumed.

  **What this does not yet give, stated precisely.**  Two things separate this from Solomon--Tits.

  1. *Termination.*  For the building, the minimal elements are the lines, and the link of a line `L`
     is the building of `V/L` — one dimension down, which is the induction the theorem wants.  But
     the other piece is `Δ(P ∖ {L})`, and removing lines one at a time does not terminate: over an
     infinite field there are infinitely many.  So the cut is the right local step and the wrong
     global induction; the classical proofs use apartments or shellability instead, and neither is a
     vertex-by-vertex removal.
  2. *Reduced homology.*  The interesting vanishing at `j = 1` needs the link's **reduced** `H_0` to
     vanish, not its `H_0`, which for a connected link is `R`.  The Mayer--Vietoris sequence built
     here is unreduced.  Reduced homology — the augmented complex — is the missing object;
     mathlib supplies the augmentation `SSet.homology₀ε` but not the augmented complex.

  Both are now concrete, named, and independent of the card's own content, which remains proved.

- 2026-08-02 — **Reduced homology turns out not to be needed: a monicity criterion replaces it.**
  `SimplicialMayerVietoris.lean` and `NerveMayerVietoris.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  isZero_homology_of_mayerVietoris_mono :
    A ⊔ B = ⊤ → (down ℕ).Rel i j → H_i(A) = 0 → H_i(B) = 0 →
    Mono (H_j(A ⊓ B) → H_j(A) ⊞ H_j(B)) → H_i(X) = 0

  isZero_homology_nerve_of_minimal_mono   -- the same, cut at a minimal element of a poset
  ```

  The previous entry named the augmented complex as the missing object.  It is not needed.  The
  vanishing argument used `H_j(A ⊓ B) = 0` only to force the connecting map `δ` to be zero, and `δ`
  is killed just as well by `δ ≫ (H_j(A ⊓ B) → H_j(A) ⊞ H_j(B)) = 0` — mathlib's `δ_comp` — together
  with monicity of that comparison map.  So the hypothesis that fails in degree zero, where a
  connected piece has homology `R` rather than `0`, is replaced by the injectivity that the reduced
  statement would have expressed, and no augmented complex is built.

  Concretely for `H_1`: the star and the link are both connected, so the comparison
  `H_0(link) → H_0(star) ⊞ H_0(compl)` is injective, and `H_1` of the order complex vanishes as soon
  as it does for the complement.  Supplying that injectivity from connectedness needs naturality of
  mathlib's augmentation `homology₀ε`, which is the one remaining piece on this route; the
  termination problem of the induction, recorded in the previous entry, is unaffected and remains the
  substantive obstruction.

- 2026-08-02 — **Naturality of the augmentation; connectedness now supplies the monicity.**
  `formal/GaloisForLFunctions/HTGeometry/SimplicialAugmentation.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  homology₀_hom_ext          :  degree-zero homology is determined by the classes of the vertices
  zeroCycle_comp_homologyMap :  the class of a vertex is natural
  homologyMap_comp_homology₀ε:  H_0(f) ≫ ε_Y = ε_X
  isIso_homologyMap_zero     :  X, Y connected → IsIso (H_0(f))
  mono_homologyMap_zero      :  X, Y connected → Mono (H_0(f))
  ```

  Mathlib has the augmentation `homology₀ε` and proves it is an isomorphism for a connected
  simplicial set, but does not state its naturality.  The proof needed one ext principle:
  `homology₀Iso` identifies `H_0(X; R)` with a coproduct indexed by `π₀ X`, and each summand's
  inclusion is the class of a vertex, so two maps out of `H_0` agree as soon as they agree on vertex
  classes.  The class of a vertex is natural by `homologyπ_naturality` together with the uniqueness
  of a lift to cycles — proved by cancelling the mono `iCycles`, which avoids the motive-not-type-correct
  rewrite that the dependent proof argument of `liftCycles` otherwise causes.

  This closes the piece flagged in the previous entry: the Mayer--Vietoris monicity hypothesis in
  degree zero is now supplied by connectedness of the two complexes involved.  The remaining
  obstruction on this route is the one recorded two entries ago and is unchanged: the induction that
  removes a minimal element does not terminate over an infinite field.

- 2026-08-02 — **The link of a vertex of the building is the building of the quotient.**
  `formal/GaloisForLFunctions/HTGeometry/BuildingLink.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  quotientBuildingOrderIso :
    {S | L < S ∧ S ≠ ⊤} ≃o {T : Submodule K (V ⧸ L) // T ≠ ⊥ ∧ T ≠ ⊤}
  linkOrderIso, linkNerveIso   -- the same for the link of a vertex, and on order complexes
  ```

  The correspondence theorem, restricted on both sides: `S ↦ S / L` carries the subspaces strictly
  between `L` and `V` to the nonzero proper subspaces of `V ⧸ L`, with inverse the preimage.  On
  nerves this says the link of a vertex of the building **is** a building, of one lower dimension.

  This makes the induction step of a Solomon--Tits argument explicit and formal: cutting at a line
  `L` (`isZero_homology_nerve_of_minimal_mono`) leaves the complement and the link, and the link is
  now identified with a smaller building, to which the same statement applies.  The obstruction
  remains where it was — the *other* piece, the complement of a line, is not smaller, and over an
  infinite field there is no finite sequence of such cuts.  Every step of the induction is formal
  except the recursion itself.

- 2026-08-02 — **Negative finding: the star/complement cut cannot prove Solomon--Tits.**

  Recorded so the route is not re-attempted.  `isZero_homology_nerve_of_minimal_mono` requires the
  complement `Δ(P ∖ {L})` to be acyclic in the degree being killed.  For the building that hypothesis
  is **false**, not merely unproved: at `N = 3` the order complex is a wedge of circles, and deleting
  one line leaves a wedge of circles, so `H_1(Δ(P ∖ {L})) ≠ 0`.  The obstruction is therefore not the
  termination of the recursion, as the previous two entries recorded, but the decomposition itself:
  removing vertices makes the complex smaller without making it acyclic.

  This also rules out the dual cut at a hyperplane, for the same reason, and any cover by two full
  subcomplexes: a cover of an order complex by the full subcomplexes on two subsets exists only when
  every chain lies entirely in one of them, which for a poset forces the star/complement shape.

  The classical proofs build the building **up** — by attaching apartments to a chamber, or by a
  shelling — rather than cutting it down.  Formalizing either needs the chamber-and-gallery theory of
  buildings, which is a development in its own right and is not implied by anything above.

  What survives and is permanent: the Mayer--Vietoris chain (coproduct splitting → degreewise
  identification → short exact sequence → vanishing and monicity criteria), the poset-homotopy
  toolkit, the augmentation's naturality, full subcomplexes of a nerve, and the identification of a
  link with a smaller building.  All are general tools, none is specific to this route, and the
  card's own content — `(4)`, the homology transfer, `H_j = 0` for `j ≥ N-1`, `H_0`, cusp
  contractibility, and the complete `N = 3` case — stands proved.

- 2026-08-02 — **`(6)`'s vanishing half is proved for the all-depth complex.**
  `formal/GaloisForLFunctions/HTGeometry/CuspedHomologyConcentration.lean`, wired into the
  `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`; umbrella green at 13120
  jobs:

  ```text
  isZero_cuspHomology_of_ne :
    1 ≤ i → i ≠ N - 2 → H_i(Δ_∞(V); R) = 0
  ```

  This is the open half of the fifth gate, and it needed no new work on this card: the deformation
  retraction of the cusps onto the building was already formalized here
  (`cuspBuildingDeformationRetract`, `cuspBuildingHomologyIso`), and the missing input — that the
  building's own homology vanishes off the top degree — was proved today on the parent card
  (`isZero_homology_building_of_ne`, from the Solomon--Tits induction built in this corpus).
  Composing the two is one line.

  So the card's claim that adding an infinite private tail to every elementary horizon changes no
  homology is now a theorem in both halves: the cusps retract away (already proved), and what is
  left has homology only in degree `N - 2` and degree `0` (proved now), for any coefficients, even
  though `Δ_∞(V)` is itself infinite dimensional.

  What is still not proved, and is not claimed: the *homotopy* equivalence `(5)` as a statement
  about homotopy types rather than homology, and the identification of the top homology with the
  integral Steinberg module beyond its definition and the observer action.  Degree zero is the
  reduced statement's remaining piece and follows from connectedness, which is recorded on the
  parent card.
