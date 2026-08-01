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
- [ ] Solomon--Tits: the building's own homotopy type `(5)` and the Steinberg identification
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
