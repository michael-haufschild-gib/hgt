# periodic-pencil `(11)`: the family coefficient descent — route found, first brick built

`HTGeometry/FamilyBoundedRelationSurvival.exists_coeff_ne_zero_famJets_of_boundedRelation`
kills every nonzero jet relation `Q` **with algebraic coefficients**.  Dropping that hypothesis is
the last blocker.  This note records the dead ends and the route that works.

## Dead ends (verified by hand)

1. `formal_mahler_descent` with `K = ℚ̄`: it descends the relation's coefficient field only to a
   field containing the *series'* coefficients, which are transcendental here.
2. "independent over `ℚ̄` ⇒ independent over `ℂ`" is FALSE for families of values (`π` as a jet);
   only the differential structure rules it out.
3. Wronskian descent returns dependence over the *full* constant field `ℂ` — no gain.
4. Reducing to the corpus's single-element `differentialAlgebraicOver_of_intermediate_trdeg_lt_aleph0`
   does not apply directly: family dependence does not make any single member DA.
5. Kolchin differential-transcendence-degree additivity would work but is a large theory build.

## THE ROUTE THAT WORKS (no dtrdeg needed)

Split the family with the **differential tower law**, then descend each single-element statement
with the corpus's finite-trdeg theorem:

- `¬ DifferentialIndependent F x` (finite family) ⇒ ∃ a splitting `x = (x', z)` with
  `DifferentialIndependent F x'` and `DifferentialAlgebraicOver ↥(F⟨x'⟩) z`;
- `F = ℚ⟨S⟩` with `S` the finitely many *constant* coefficients of the relation, so
  `(ℚ⟨x'⟩)⟨S⟩` has finite trdeg over `ℚ⟨x'⟩`
  (`differentialAdjoin_trdeg_lt_aleph0_of_finite_jetSet`, jet set of constants is finite);
- hence `DifferentialAlgebraicOver ↥(ℚ⟨x'⟩⟨S⟩) z ⇒ DifferentialAlgebraicOver ↥(ℚ⟨x'⟩) z`
  by `differentialAlgebraicOver_of_intermediate_trdeg_lt_aleph0`;
- rebuild with the tower law ⇒ `¬ DifferentialIndependent ℚ x`.

**Brick 1 is BUILT** (`HTGeometry/DifferentialIndependentTowerIff.lean`, axiom-clean):
`differentialIndependent_sumElim_iff` — the tower law as an **equivalence**
(`DifferentialIndependent F (Sum.elim y x) ↔ DifferentialIndependent F x ∧
DifferentialIndependent ↥(differentialAdjoin F (range x)) y`), from mathlib's
`AlgebraicIndependent.sumElim_iff` plus the reindexing `Equiv.sumProdDistrib`.

## Remaining bricks

1. **Maximal-independent-subset extraction**: from `¬ DifferentialIndependent F ((↑) : s → E)` with
   `s` finite, produce `t ⊆ s`, `z ∈ s \ t` with `t` independent and `z` DA over `F⟨t⟩`.  Index by
   *subsets of `E`* (`↥s : Type u`) and use `PUnit.{u+1}` as the singleton index — this keeps all
   universes equal to `E`'s, which `differentialIndependent_sumElim_iff` requires.
2. **Commutation** `(F⟨S⟩)⟨t⟩ = (F⟨t⟩)⟨S⟩` as subfields of `E`, plus a transfer of
   `DifferentialIndependent` between two bases with the same underlying subfield.
3. Assemble the descent `DifferentialIndependent F x → DifferentialIndependent ↥(F⟨S⟩) x`
   for `S` of finite jet set, then instantiate at `F = ℚ` (or `ℚ̄`) and `S` = the relation's
   coefficients to remove `hQalg`.
4. Then step (iv): bridge to `DifferentialIndependent` of the analytic orbit.

See `mem:nsk-other/periodic-pencil-item11-progress-2026-08-14`.
