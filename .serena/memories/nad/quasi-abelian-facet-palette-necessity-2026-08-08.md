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

### `AutomorphyLogarithmDefect.lean` — analytic input #1, CLOSED
* **`eq_of_continuous_int_valued`** — a continuous ℤ-valued function on a preconnected space is
  constant (locally constant: distinct integers are ≥ 1 apart).
* **`exists_continuous_exp_eq`** — every continuous nowhere-vanishing function on a complex normed
  space has a continuous logarithm.  The space is contractible ⟹ simply connected; mathlib's
  **`Complex.exists_continuousOn_eqOn_exp_comp`** (in `Analysis/Complex/BranchLogRoot.lean`) applies
  on `univ`.  `IsSimplyConnected (univ : Set W)` via
  `(Homeomorph.Set.univ W).toHomotopyEquiv.simplyConnectedSpace`.
* **`exists_isQuasiAdditive_log_of_isMulTwoCocycle`** — every continuous nowhere-vanishing factor of
  automorphy has a logarithm that is quasi-additive with a **constant integral** defect.

### ARCHITECTURAL CORRECTION (6th → 7th instalment)
Deriving the factor from a globally nowhere-vanishing θ is **degenerate**: on a contractible space
such a θ has a global logarithm, so the cocycle is a coboundary and the Chern class vanishes.  The
primitive datum must be the factor `e` itself (`IsMulTwoCocycle`), with `automorphyFactor θ` only a
special case.  Integrality core factored out as `exists_int_logDefect` (no quasi-additivity
hypothesis needed — the *pointwise* defect is already an integer).

### `HermitianRadicalPositivity.lean` — nondegeneracy ⟹ strict positivity
`altSym E u v = E (i u, v)` is the **symmetric** real form with `Re H(x,x) = altSym E x x`; symmetry
is `i`-invariance + alternation, not an extra assumption.
* **`altSym_eq_zero_of_self_eq_zero`** — degenerate Cauchy–Schwarz: a null vector of a PSD symmetric
  form is orthogonal to everything.  **No limit needed**: with `s = |S(u,v)|/(1+S(v,v))` the
  quadratic expansion at `t = ±s` is already contradictory.
* **`altSym_pos_of_psd_of_nondegenerate`**, **`exists_hermitian_of_psd_of_nondegenerate`**.

## Standing state of the Capocasa–Catanese chain (all unconditional)

```
factor of automorphy (IsMulTwoCocycle)
  → continuous logarithm + constant integral defect   AutomorphyLogarithmDefect
  → integral alternating biadditive form              CocycleCommutatorPairing
  → Hermitian form, Im H integral on Γ                AlternatingHermitianDictionary
  → positive definite (given PSD + nondegenerate)     HermitianRadicalPositivity
  → quasi-Abelian facet certificate
```

### `GaussianDecayVanishing.lean` — the analytic engine for semi-definiteness
* **`eq_zero_of_gaussian_decay`** — entire `f : ℂ → ℂ` with `‖f t‖ ≤ C exp(−a‖t‖²)`, `a > 0`, is
  identically zero.  Bounded ⟹ Liouville ⟹ constant ⟹ the bound at one large radius kills it.
* **`eq_zero_of_gaussian_decay_along_line`** — same on a complex line in any complex normed space.
  mathlib's `Differentiable.apply_eq_apply_of_bounded` already works on an arbitrary complex normed
  space, so no dimension restriction enters.
* **`not_gaussian_decay_along_line_of_ne_zero`** — the contrapositive, the form actually used.

### `AppellHumbertFactor.lean` — the normal form (10th instalment)
* `IsHermitianForm H` + derived `add_right`, `self_im`, `re_symm`,
  `sub_symm : H x y − H y x = 2i·Im H(x,y)`.
* `appellHumbertFactor H χ γ z = χ γ · exp(π H(z,γ) + (π/2) H(γ,γ))`.
* **`appellHumbertFactor_isMulTwoCocycle`** — it *is* a factor of automorphy.  The exponents differ
  by `(π/2)(H(γ,γ') − H(γ',γ)) = πi·Im H(γ,γ')`, exactly what the semicharacter law cancels — so the
  semicharacter condition is **forced** by the cocycle law, not an extra normalisation.
* `norm_appellHumbertFactor`; `thetaNorm H θ z = ‖θ z‖·exp(−(π/2)Re H(z,z))` and
  **`thetaNorm_add`**: the normalised modulus is **Γ-invariant** (every base-point term cancels;
  `Re H(z,γ)` appears twice with opposite signs).
* `hermitianForm_smul_self`: `Re H(s·v, s·v) = ‖s‖²·Re H(v,v)`.
* **`eq_zero_along_line_of_neg_of_thetaNorm_bounded`** — `Re H(v,v) < 0` + bounded normalised
  modulus ⟹ θ vanishes on the whole line `ℂv`.

### `PeriodicBoundedThetaNorm.lean` + `AffineGaussianSemidefinite.lean` (11th instalment)
mathlib has boundedness only for a full `ZLattice` (`IsZLattice.isCompact_range_of_periodic`); a
quasi-Abelian period group is not one.  Built the compact-covering-set version:
* `range_subset_image_of_periodic_of_covers` (no topology; axioms `[propext]` only),
  **`exists_bound_of_periodic_of_compact_cover`**, **`exists_bound_thetaNorm_of_compact_cover`**.
* `hermitianForm_affine_re`, `abs_hermitianForm_cross_le`,
  **`eq_zero_along_affine_line_of_neg`** — the linear cross term is absorbed by completing the
  square, `2|s|B ≤ (−c/2)|s|² + 2B²/(−c)`, halving the Gaussian exponent.
* **`nonneg_re_of_thetaNorm_bounded_of_exists_ne_zero`** — a theta function nonzero at a *single
  point* forces `Re H(v,v) ≥ 0` for **every** `v`.

## THE CHAIN IS COMPLETE (as unconditional Lean results)

```
factor of automorphy → logarithm w/ constant integral defect → integral alternating form
  → Hermitian form with integral Im
  → semi-definite  (nonzero theta function + compact covering set)
  → positive definite  (nondegeneracy)
  → quasi-Abelian facet certificate
```

### `CapocasaCatanesePositivity.lean` — assembled (12th instalment)
**Refactor, not duplication**: the degenerate Cauchy–Schwarz is now the standalone
**`symmBilin_eq_zero_of_self_eq_zero`**, stated for *any* real form whose diagonal expands
quadratically along a one-parameter family (`comb : ℝ → X → X → X`, no algebraic structure on `X`).
Both `altSym` and `hermitianRe` instantiate it.
* `hermitianRe H u v = Re H(u,v)`, `hermitianRe_expand`.
* **`IsHermitianForm.eq_zero_of_self_re_eq_zero`** — a null vector of a PSD Hermitian form is
  annihilated *entirely*: Cauchy–Schwarz at `x` kills `Re H(x,y)`, at `i·x` kills `Im H(x,y)`
  (because `Re H(i x, y) = −Im H(x,y)` and `Re H(i x, i x) = Re H(x,x)`).
* **`hermitianForm_nonneg_of_theta`**, **`hermitianForm_pos_of_theta_of_nondegenerate`**.

### `QuasiAbelianFacetCertificateOfTheta.lean` — the certificate is CONSTRUCTED (13th instalment)
* **`certificateOfAlternating`** — builds a `QuasiAbelianFacetCertificate` from facet data (period
  group + discreteness/closedness/span-deficiency, an alternating compatible form that is integral,
  PSD and nondegenerate, and the vertex incidence).  `X := W ⧸ Γ` so surjectivity and the fibre
  description are *definitional*; `quotient_noncompact` is the span criterion; `H` is
  `hermitianOfAlternating` with the dictionary's four clauses and Cauchy–Schwarz positivity;
  `H_integral_imaginary` is integrality of `E` because `Im(hermitianOfAlternating E) = E` on the nose.
* `exists_certificateOfAlternating`.
* **`latticeClass_certificateOfAlternating_eq_iff`** — for the constructed certificate the lattice
  class *is* a quotient class, so two exponents agree iff their difference lies in Γ.

### Palette input DISCHARGED (14th instalment)
* **`paletteInputOfCertificates`** — injectivity of the lattice class is *all* the input needs; the
  structural-shift clause is immediate because equal classes force equal exponents.  That second
  field was never an independent analytic assumption.
* **`latticeClass_injective_of_free`** — for a `certificateOfAlternating`, injectivity is exactly
  card property 5 in concrete form (the facet lattice meets Γ only at 0); proof = quotient-class
  bridge + `sub_zsmul`.

**Full pipeline, no unproved analytic hypothesis:**
```
facet data (period group, vertex incidence, integral nondegenerate alternating form)
  → certificateOfAlternating          : all six certificate clauses
  → latticeClass_injective_of_free    : injective integral facet lattice
  → paletteInputOfCertificates        : QuasiAbelianFacetPaletteInput
  → quasiAbelianFacetPalette_necessity: the card's theorem
```

### Proof step 1 CLOSED — and mostly corpus-owned (15th instalment)
**`StanleyReisnerFacetSeparator.lean` already proved the card's (7)–(9) in a stronger form**: the
per-facet vertex choice `b_B ∈ A \ B` is unnecessary — by the corpus's monomial-support
characterisation of `I_Δ`, the facet monomial `∏_{w∈A} x_w` *is* the separator
(`srProd_facet_ne_zero`, `srVertexX_mul_srProd_facet_eq_zero`).  The card's `q_A = ∏_{B≠A} x_{b_B}`
and its choice are not needed.  **Check this file before rebuilding any facet-isolation step.**

New `StanleyReisnerExponentDetector.lean` supplies the missing converse of (9):
* **`srExponentDetector`** — the face detector generalizes from squarefree exponents to *any*
  exponent with face support; `coeff_eq_zero_of_isFace_support` never used squarefreeness.
* **`srMonomial_ne_zero`**, **`srVertexX_mul_srProd_facet_ne_zero`**,
  **`srVertexX_mul_srProd_facet_eq_zero_iff`** — equation (9) exactly: `x_v q_A ∈ I_Δ ↔ v ∉ A`.

**Next**: card proof step 2 (the integral facet orbit is differentially free) and then the
realization transport `G_A = q_A(T)F`; plus the specialist novelty audit (not a Lean obligation).

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
