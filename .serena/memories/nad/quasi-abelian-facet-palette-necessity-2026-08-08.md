# Card `quasi-abelian-facet-palette-necessity` — IN PROGRESS (2026-08-08)

Card: `docs/drafts/pipeline/2-fully-proven/nad/quasi-abelian-facet-palette-necessity.md`.
Open Lean gate: *"construct full-period extraction and the Capocasa–Catanese necessary direction in
Lean"* — discharge `QuasiAbelianFacetCertificate` / `QuasiAbelianFacetPaletteInput` in
`HTGeometry/QuasiAbelianFacetPaletteCompletion.lean`.

**Status: properties 1–6 all proved in complex dimension 1; properties 1–3 proved in any
dimension; property 6 in dimension ≥ 2 is the only thing left.**  Before this work *none* of these
clauses had a proof — `quotient_noncompact`, `gammaClosed`, `gammaDiscrete`, `H_positive`,
`H_integral_imaginary` existed **only** as hypothesis fields of two structures.

## Five new modules (all axiom-clean, all wired into the HTGeometry umbrella)

### `ClosedSubgroupLineStructure.lean` — mathlib does not have this
Closed additive subgroups of a finite-dim real normed space.  `lineDirections P = {x | ∀ t:ℝ, t•x ∈ P}`.
* `exists_unit_mem_lineDirections` — accumulation at `0` ⟹ `P` contains a line (unit vectors
  subconverge on the sphere; `⌊t/‖p_k‖⌋ • p_k → t·u`).
* `exists_pos_forall_mem_lineDirections` — `P` discrete modulo `lineDirections P`.
**Trick**: take a linear complement `F`; `P ⊓ F` is closed with no line; transport the isolation
back along the continuous projection.  No quotient topology, no induction on dimension.

### `FullPeriodExtraction.lean` — properties 1, 2
`translationPeriods G = {h | Function.Periodic G h}` for any additive group — generalizes the
corpus's one-variable `periodSubgroup` (bridge `translationPeriods_eq_periodSubgroup`, by `rfl`;
do **not** build a third notion).  `isClosed_translationPeriods`,
**`complex_smul_mem_lineDirections_translationPeriods`** (line directions of an entire function are
a *complex* subspace — identity theorem on `w ↦ G(z+w•x) − G z`),
**`analytic_full_period_extraction`**.

### `NoncompactPeriodQuotient.lean` — property 3's criterion
**`not_isCompact_univ_quotient_of_span_ne_top`** — `span ℝ Γ ≠ ⊤` ⟹ `W ⧸ Γ` noncompact (a dual
vector annihilating `Γ` descends to a continuous surjection onto ℝ).  Plus
`span_closure_ne_top_of_card_lt_finrank`.  **The real span is unchanged by dividing out the line
directions, so the criterion reads on the period group itself — no two-step quotient.**

### `GeneralizedRiemannRelations.lean` — property 6, ℂ-independent lattices
`basisHermitian b x y = ∑ i (b.repr x i) * conj (b.repr y i)` (declare a ℂ-basis orthonormal).
`im_basisHermitian_eq_zero_of_mem_closure` (Im ≡ 0 on the lattice) and
**`exists_hermitian_positive_integral_of_basis`** in exactly the certificate's shape.

### `PlaneRiemannRelations.lean` — **dimension 1 needs no Capocasa–Catanese**
* **`exists_planeHermitian_pos_integral`** — for *any* `ω₁ ω₂ : ℂ` there is `c > 0` making
  `Im (c x conj y)` integral on the subgroup they generate.  `Im (x conj y)` vanishes on the
  diagonal and is antisymmetric, so the only constraint is `c·Im(ω₁ conj ω₂) ∈ ℤ`: take `c = 1` or
  `c = |Im(ω₁ conj ω₂)|⁻¹`.  A discrete subgroup of ℂ has rank ≤ 2, so this is *every* plane lattice.
* **`not_isCompact_univ_quotient_periodSubgroup_of_hypertranscendental`** (property 3) and
  **`exists_planeHermitian_pos_integral_periodSubgroup`** (property 6), both by composing with the
  corpus law `exists_periodSubgroup_eq_closure_singleton` (period group of a hypertranscendental
  meromorphic NF function on ℂ is cyclic).

### `RankTwoRiemannRelations.lean` — rank ≤ 2 in **any** dimension
* `exists_int_of_mem_closure_of_biadditive` — reusable core: integrality of a biadditive real
  pairing propagates from generators to the generated subgroup (closure induction in each slot;
  zero/neg derived from additivity, so only the two additivity laws are hypotheses).
* `innerHermitian c x y = c⟪y,x⟫` on any complex inner-product space.
* **`exists_innerHermitian_pos_integral`** / **`exists_hermitian_positive_integral_of_two_generators`**
  — the plane argument is dimension-free: the only constraint on a two-generated subgroup is the
  single number `Im ⟪ω₂,ω₁⟫`.

### `CocycleCommutatorPairing.lean` — where the integral alternating form comes from
`IsAddTwoCocycle c : c x y + c (x+y) z = c y z + c x (y+z)`;
`cocycleCommutator c x y = c x y - c y x`.
`_self` and `_skew` need **no** hypothesis (axioms: only `[propext]`).
**`cocycleCommutator_add_left`** — biadditivity.  Whole content is `T = K1 + K2 − K3` between the
target and the cocycle identity at `(x,y,z)`, `(z,x,y)`, `(x,z,y)`; commutativity of the base is
what makes the third instance available.  Integrality is inherited from the value group.

### `AlternatingHermitianDictionary.lean` — the Appell–Humbert dictionary
`IsAlternatingCompatible E` (additive + real-homogeneous in slot 1, alternating, `E(i·,i·) = E`).
`hermitianOfAlternating E x y = E(i x, y) + i E(x,y)`, with `Im H = E` on the nose.
**`hermitian_smul_left`** (complex homogeneity — reduces to real homogeneity plus
`H(i x, y) = i H(x,y)`), **`hermitian_symm`**, **`exists_hermitian_of_alternating`** (positivity
`E(i x, x) > 0` ⟹ the certificate shape).

**Chain now built**: factor of automorphy → integral alternating form → Hermitian form with
integral imaginary part → certificate.

## Still open — the precise frontier

Property 6 for a complex-**dependent** lattice of **rank ≥ 3**.  Everything else is covered:
ℂ-independent lattices (`exists_hermitian_positive_integral_of_basis`), rank ≤ 2 in any dimension,
and hence *all* of complex dimension 1 (discreteness forces rank ≤ 2).

In the open case the relations **can genuinely fail** (a generic complex torus of dim ≥ 2 is not
abelian), so no purely algebraic construction can work: the analytic hypothesis — that the lattice
is the full period group of a nondegenerate meromorphic function — must actually be used.

**The whole integrality half is now built.**  Third module of the chain:

### `AutomorphyFactorCocycle.lean`
* `automorphyFactor θ γ z = θ (z+γ) / θ z`; **`automorphyFactor_add`** — the multiplicative cocycle
  law holds for *every* nowhere-vanishing θ, no analytic input.
* `IsQuasiAdditive F c : F (γ+γ') z = F γ (z+γ') + F γ' z + c γ γ'`.
* **`isAddTwoCocycle_of_isQuasiAdditive`** — pure algebra (expand `F(γ₁+γ₂+γ₃)` both bracketings and
  cancel); axioms `[propext]` only.
* **`exists_int_of_isQuasiAdditive_exp`** — the defect is an **integer**: its exponential *is* the
  multiplicative cocycle law rearranged, hence 1; `Complex.exp_eq_one_iff` finishes.  **This is
  where the ℤ of `Im H(Γ,Γ) ⊆ ℤ` is born.**
* **`automorphyFactor_commutator_int`** — packaged: commutator is alternating, biadditive, ℤ-valued.

Chain complete: nonvanishing θ + logarithm → ℤ-valued 2-cocycle → ℤ-valued alternating form
(`cocycleCommutator_isAlternatingBiadditive`) → Hermitian form with integral Im
(`exists_hermitian_of_alternating`) → certificate.

**Only two analytic inputs remain on the whole card:**
1. existence of the logarithm `F` — a holomorphic branch of `log e(γ,·)` on the simply connected
   ambient space;
2. the positivity `E(i x, x) > 0` extracted from nondegeneracy of the meromorphic function.

## Lean traps hit

* **`Basis` is now `Module.Basis`** — without `open Module` it becomes an autoImplicit variable and
  every downstream error is nonsense.
* `AddSubgroup.closure_induction` case names are `mem`, **`zero`, `add`, `neg`** (not one/mul/inv).
* `have h : A →+ B := ...` forgets the body — `h a` cannot be unfolded.  Use `closure_induction`
  instead of building comap subgroups through a `have`-bound hom.
* `rcases ha with rfl | rfl` on `a = ω₁ ∨ a = ω₂` may substitute **ω₁ := a**, renaming the outer
  variables; a later `rw [lemma]` then unifies against the wrong occurrence.  Factor the case
  analysis into a name-independent helper returning a disjunction of *values*
  (`im_mul_star_pair_cases`).
* `Submodule.linearProjOfIsCompl` deprecated → `Submodule.projectionOnto` / `Submodule.projection`.
* `rw [← hsplit]` rewrites the `x` *inside* the projection too — rewrite in the hypothesis.
* `push_neg` deprecated → `push Not at h`.
* `((r:ℝ):ℂ) • y = r • y` in a ℂ-module: `rw [← Complex.coe_algebraMap, algebraMap_smul]`.
* `FiniteDimensional ℝ V` from `FiniteDimensional ℂ V`: `Module.Finite.trans ℂ V`.
* `QuotientAddGroup.lift` returns a bundled `→+`; coerce with `⇑`.
* `omit [Inst] in` goes **before** the docstring.
* `Submodule.exists_dual_map_eq_bot_of_lt_top` takes a `Projective` argument — pass `inferInstance`.
