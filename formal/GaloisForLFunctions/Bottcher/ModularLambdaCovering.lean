/-
# `λ : ℍ → ℂ∖{0,1}` is a covering map — the construction

The three-value Montel lane needs the modular `λ` to be the universal covering of `ℂ∖{0,1}`, so that
holomorphic maps from a disk into `ℂ∖{0,1}` lift to disk-valued (bounded) maps (`normal_of_omitting_lift`).
`λ` being a *covering* decomposes into genuinely new content (none of it in Mathlib):

1. **`λ` is a local biholomorphism** — `λ' ≠ 0` (now a theorem, `modularLambda_deriv_ne_zero'`), so by the
   holomorphic inverse function theorem `λ` is a local homeomorphism on `ℍ`.
2. **`λ` is surjective onto `ℂ∖{0,1}`** — the little-Picard content. Image is open (`λ` open, from `λ'≠0`)
   and closed in `ℂ∖{0,1}` (properness over a `Γ(2)`-fundamental domain: a value-sequence escaping to the
   boundary forces `τ` to a cusp `{0,1,∞}`, where `λ → {0,1,∞}`, contradicting a limit in `ℂ∖{0,1}`).
3. **Fibres are exactly `Γ(2)`-orbits** — `λ̄ : ℍ/Γ(2) → ℂ∖{0,1}` is injective; combined with (2) it is a
   homeomorphism, and `Γ(2)` (mod `±I`) acts freely & properly discontinuously, giving the deck structure.

This file builds the analytic backbone. The **cusp limits** of `λ` (this section) are the heart of the
properness in (2): `λ → 0` at the cusp `∞`, and via the deck relations `λ(−1/τ) = 1 − λ(τ)`,
`λ(τ+1) = λ/(λ−1)`, the values at the cusps `0` and `1`.

Consumes `ThetaWronskian` (`λ' ≠ 0` unconditional + the theta cusp limits).
-/
import GaloisForLFunctions.Bottcher.ThetaWronskian

open Complex Filter Topology Matrix UpperHalfPlane ModularGroup CongruenceSubgroup
open scoped MatrixGroups

namespace Bottcher

/-! ### Cusp limits of `λ`. -/

/-- **`λ → 0` at the cusp `i∞`.** `λ = (θ₂/θ₃)⁴`, `θ₂ → 0`, `θ₃ → 1`, so `λ → (0/1)⁴ = 0`. This is the
value of `λ` at the cusp `∞` of `Γ(2)` — the first of the three cusp values `{0,1,∞}` that drive the
properness (closed-image) half of surjectivity. -/
theorem tendsto_modularLambda_atImInfty :
    Tendsto modularLambda (comap Complex.im atTop) (𝓝 0) := by
  have h : Tendsto (fun τ => (thetaTwo τ / thetaThree τ) ^ 4)
      (comap Complex.im atTop) (𝓝 ((0 / 1) ^ 4)) :=
    (tendsto_thetaTwo_atImInfty.div tendsto_thetaThree_atImInfty (by norm_num)).pow 4
  simpa [modularLambda] using h

/-- **`1 − λ → 1`, i.e. `λ → 0`, restated via the omitted value `1`.** Packaged for the `S`-cusp: under
`τ ↦ −1/τ` the value `1 − λ(τ)` is `λ(−1/τ)` (`modularLambda_S'`), so as `τ → i∞` (where `λ(τ) → 0`)
the deck-image value `λ(−1/τ) → 1` — the cusp value at `0`. -/
theorem tendsto_one_sub_modularLambda_atImInfty :
    Tendsto (fun τ => 1 - modularLambda τ) (comap Complex.im atTop) (𝓝 1) := by
  have := tendsto_modularLambda_atImInfty
  simpa using (tendsto_const_nhds (x := (1 : ℂ))).sub this

/-! ### `λ` is a local homeomorphism on `ℍ` (from `λ' ≠ 0`, via the holomorphic IFT). -/

/-- `λ` is analytic at every `x ∈ ℍ` (holomorphic on the open set `ℍ`). -/
theorem analyticAt_modularLambda {x : ℂ} (hx : 0 < x.im) : AnalyticAt ℂ modularLambda x := by
  have hdiff : DifferentiableOn ℂ modularLambda {z : ℂ | 0 < z.im} :=
    fun z hz => (differentiableAt_modularLambda_of_im_pos hz).differentiableWithinAt
  exact hdiff.analyticAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hx)

/-- **`λ` is a local homeomorphism on `ℍ`.** `λ` is analytic with `λ' ≠ 0`
(`modularLambda_deriv_ne_zero'`), so at each `x ∈ ℍ` the holomorphic inverse function theorem
(`HasStrictFDerivAt.toOpenPartialHomeomorph`) produces a biholomorphic chart with `λ` as its map. This
is the local-homeomorphism datum of the covering `λ : ℍ → ℂ∖{0,1}` (a covering is in particular a local
homeo); the global structure (surjectivity, fibres = `Γ(2)`-orbits) is built separately. -/
theorem isLocalHomeomorphOn_modularLambda :
    IsLocalHomeomorphOn modularLambda {z : ℂ | 0 < z.im} := by
  intro x hx
  have hxim : 0 < x.im := hx
  have hd : deriv modularLambda x ≠ 0 := modularLambda_deriv_ne_zero' hxim
  have hstr : HasStrictDerivAt modularLambda (deriv modularLambda x) x :=
    (analyticAt_modularLambda hxim).hasStrictDerivAt
  set e : ℂ ≃L[ℂ] ℂ :=
    ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv modularLambda x) hd) with he
  have hcle : (e : ℂ →L[ℂ] ℂ) = ContinuousLinearMap.toSpanSingleton ℂ (deriv modularLambda x) := by
    rw [he]; ext y
    simp [ContinuousLinearEquiv.unitsEquivAut, ContinuousLinearMap.toSpanSingleton_apply, mul_comm]
  have hfd : HasStrictFDerivAt modularLambda (e : ℂ →L[ℂ] ℂ) x := by
    rw [hcle]; exact hstr.hasStrictFDerivAt
  exact ⟨hfd.toOpenPartialHomeomorph modularLambda, hfd.mem_toOpenPartialHomeomorph_source,
    (hfd.toOpenPartialHomeomorph_coe).symm⟩

/-- **The image `λ(ℍ)` is open in `ℂ`.** `λ` is a local homeomorphism on the open set `ℍ`
(`isLocalHomeomorphOn_modularLambda`), hence an open map there. This is the *open* half of "`λ` is
surjective onto `ℂ∖{0,1}`": the image is open, and is the whole connected target once it is also shown
closed (the cusp/properness half). -/
theorem isOpen_modularLambda_image : IsOpen (modularLambda '' {z : ℂ | 0 < z.im}) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  rw [← isLocalHomeomorphOn_modularLambda.map_nhds_eq hx]
  exact Filter.image_mem_map ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hx)

/-- **`λ → 1` at the cusp `0`.** Under `σ ↦ −1/σ` (which sends `i∞` to the cusp `0`),
`λ(−1/σ) = 1 − λ(σ)` (`modularLambda_S'`), and `λ(σ) → 0` at `i∞`, so `λ(−1/σ) → 1`. This is the cusp
value of `λ` at `0` — the second of the three cusp values `{0,1,∞}`. -/
theorem tendsto_modularLambda_neg_inv_atImInfty :
    Tendsto (fun σ : ℂ => modularLambda (-1 / σ)) (comap Complex.im atTop) (𝓝 1) := by
  refine tendsto_one_sub_modularLambda_atImInfty.congr' ?_
  filter_upwards [tendsto_comap.eventually (eventually_gt_atTop (0 : ℝ))] with σ hσ
  exact (modularLambda_S' hσ).symm

/-! ### The anharmonic `S₃`-orbit — the value-side of the `SL(2,ℤ)`-action on `λ`.

`SL(2,ℤ)/Γ(2) ≅ S₃` acts on the values of `λ` through the six anharmonic Möbius maps
`{w, 1−w, 1/w, 1/(1−w), w/(w−1), (w−1)/w}`. This orbit is the value-side bookkeeping for the cusp /
properness argument behind surjectivity: every `λ(g•τ)` is one of these six functions of `λ(τ)`. -/

/-- The **anharmonic orbit** of `w`: the six cross-ratio values permuted by `S₃`. -/
def anharmonicOrbit (w : ℂ) : Set ℂ :=
  {w, 1 - w, 1 / w, 1 / (1 - w), w / (w - 1), (w - 1) / w}

@[simp] theorem self_mem_anharmonicOrbit (w : ℂ) : w ∈ anharmonicOrbit w := by
  simp [anharmonicOrbit]

/-! ### The anharmonic action as a group of `Equiv`s of `ℂ∖{0,1}`.

The genuinely structural object: `SL(2,ℤ)` acts on the *values* of `λ` through the six-element
anharmonic group `S₃`, realised as permutations of the thrice-punctured plane `ℂ∖{0,1}`. Building the
two generators as `Equiv`s makes the multiplicativity of the action `λ(g•τ) = φ_g · λ(τ)` automatic
(`Equiv` composition), with **no** cross-ratio case bash. -/

/-- The thrice-punctured plane `ℂ∖{0,1}` (the target of `λ`). -/
abbrev Punctured : Type := ↥({0, 1}ᶜ : Set ℂ)

theorem mem_compl01 {x : ℂ} : x ∈ ({0, 1}ᶜ : Set ℂ) ↔ x ≠ 0 ∧ x ≠ 1 := by
  simp [Set.mem_compl_iff, not_or]

/-- Membership engine for `ℂ∖{0,1}` under `w ↦ 1−w`. -/
private theorem anharmS_mem {w : ℂ} (hw : w ∈ ({0, 1}ᶜ : Set ℂ)) : 1 - w ∈ ({0, 1}ᶜ : Set ℂ) :=
  mem_compl01.mpr ⟨sub_ne_zero.mpr (Ne.symm (mem_compl01.mp hw).2),
    fun h => (mem_compl01.mp hw).1 (sub_eq_self.mp h)⟩

/-- **The `S`-generator** of the anharmonic group: `w ↦ 1 − w` on `ℂ∖{0,1}` (an involution). -/
def anharmS : Punctured ≃ Punctured where
  toFun w := ⟨1 - w.1, anharmS_mem w.2⟩
  invFun w := ⟨1 - w.1, anharmS_mem w.2⟩
  left_inv w := by apply Subtype.ext; show 1 - (1 - w.1) = w.1; ring
  right_inv w := by apply Subtype.ext; show 1 - (1 - w.1) = w.1; ring

/-- Membership engine for `ℂ∖{0,1}` under `w ↦ w/(w−1)`. -/
private theorem anharmT_mem {w : ℂ} (hw : w ∈ ({0, 1}ᶜ : Set ℂ)) :
    w / (w - 1) ∈ ({0, 1}ᶜ : Set ℂ) := by
  have h1 : w - 1 ≠ 0 := sub_ne_zero.mpr (mem_compl01.mp hw).2
  refine mem_compl01.mpr ⟨div_ne_zero (mem_compl01.mp hw).1 h1, fun h => ?_⟩
  rw [div_eq_iff h1, one_mul] at h
  exact one_ne_zero (sub_eq_self.mp h.symm)

/-- **The `T`-generator** of the anharmonic group: `w ↦ w/(w−1)` on `ℂ∖{0,1}` (an involution:
`m(w)−1 = 1/(w−1)`, so `m(m(w)) = (w/(w−1))·(w−1) = w`). -/
noncomputable def anharmT : Punctured ≃ Punctured where
  toFun w := ⟨w.1 / (w.1 - 1), anharmT_mem w.2⟩
  invFun w := ⟨w.1 / (w.1 - 1), anharmT_mem w.2⟩
  left_inv w := by
    have h1 : w.1 - 1 ≠ 0 := sub_ne_zero.mpr (mem_compl01.mp w.2).2
    apply Subtype.ext
    show w.1 / (w.1 - 1) / (w.1 / (w.1 - 1) - 1) = w.1
    rw [show w.1 / (w.1 - 1) - 1 = 1 / (w.1 - 1) from by field_simp; ring]
    field_simp
  right_inv w := by
    have h1 : w.1 - 1 ≠ 0 := sub_ne_zero.mpr (mem_compl01.mp w.2).2
    apply Subtype.ext
    show w.1 / (w.1 - 1) / (w.1 / (w.1 - 1) - 1) = w.1
    rw [show w.1 / (w.1 - 1) - 1 = 1 / (w.1 - 1) from by field_simp; ring]
    field_simp

/-- `λ` packaged as a map `ℍ → ℂ∖{0,1}`. -/
noncomputable def lambdaPunct (τ : ℍ) : Punctured :=
  ⟨modularLambda (τ : ℂ),
    modularLambda_mem_compl_zero_one' (by rw [UpperHalfPlane.coe_im]; exact τ.im_pos)⟩

/-- **Base relation `S`:** `λ(S•τ) = anharmS (λ τ)`, i.e. `λ(−1/τ) = 1 − λ(τ)` (`modularLambda_S'`). -/
theorem lambdaPunct_smul_S (τ : ℍ) :
    lambdaPunct (ModularGroup.S • τ) = anharmS (lambdaPunct τ) := by
  have hτ : 0 < (τ : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact τ.im_pos
  apply Subtype.ext
  show modularLambda ((ModularGroup.S • τ : ℍ) : ℂ) = 1 - modularLambda (τ : ℂ)
  have hact : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / (τ : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, neg_div, one_div, inv_neg]
  rw [hact, modularLambda_S' hτ]

/-- **Base relation `T`:** `λ(T•τ) = anharmT (λ τ)`, i.e. `λ(τ+1) = λ(τ)/(λ(τ)−1)`
(`modularLambda_T_eq'`). -/
theorem lambdaPunct_smul_T (τ : ℍ) :
    lambdaPunct (ModularGroup.T • τ) = anharmT (lambdaPunct τ) := by
  have hτ : 0 < (τ : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact τ.im_pos
  apply Subtype.ext
  show modularLambda ((ModularGroup.T • τ : ℍ) : ℂ) = modularLambda (τ : ℂ) / (modularLambda (τ : ℂ) - 1)
  have hact : ((ModularGroup.T • τ : ℍ) : ℂ) = (τ : ℂ) + 1 := by
    rw [← zpow_one ModularGroup.T, ModularGroup.coe_T_zpow_smul_eq]; push_cast; ring
  rw [hact, modularLambda_T_eq' hτ]

@[simp] theorem anharmS_apply (w : Punctured) : (anharmS w : ℂ) = 1 - w := rfl
@[simp] theorem anharmT_apply (w : Punctured) : (anharmT w : ℂ) = (w : ℂ) / (w - 1) := rfl

theorem punct_ne_one (w : Punctured) : (w : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (mem_compl01.mp w.2).2
theorem punct_ne_zero (w : Punctured) : (w : ℂ) ≠ 0 := (mem_compl01.mp w.2).1

/-- `S² = 1`: `w ↦ 1−w` is an involution. -/
theorem anharmS_sq : anharmS * anharmS = 1 := by
  ext w
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, anharmS_apply, Equiv.Perm.coe_one, id_eq]
  ring

/-- `T² = 1`: `w ↦ w/(w−1)` is an involution. -/
theorem anharmT_sq : anharmT * anharmT = 1 := by
  ext w
  have h1 : (w : ℂ) - 1 ≠ 0 := punct_ne_one w
  have h2 : (w : ℂ) / (w - 1) - 1 ≠ 0 := by
    rw [div_sub_one h1]
    exact div_ne_zero (by rw [show (w : ℂ) - (w - 1) = 1 from by ring]; exact one_ne_zero) h1
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, anharmT_apply, Equiv.Perm.coe_one, id_eq]
  field_simp
  ring

/-- `(ST)³ = 1`, in braid form `STS = TST`. Both sides send `w ↦ 1/w` (the third anharmonic
involution). The only cross-ratio identity needed. -/
theorem anharm_braid : anharmS * anharmT * anharmS = anharmT * anharmS * anharmT := by
  ext w
  have h0 : (w : ℂ) ≠ 0 := punct_ne_zero w
  have h1 : (w : ℂ) - 1 ≠ 0 := punct_ne_one w
  have hnw : (-(w : ℂ)) ≠ 0 := neg_ne_zero.mpr h0
  have eL : (1 : ℂ) - (1 - (w : ℂ)) / ((1 - (w : ℂ)) - 1) = 1 / (w : ℂ) := by
    rw [show (1 - (w : ℂ)) - 1 = -w from by ring, one_sub_div hnw,
        show -(w : ℂ) - (1 - w) = -1 from by ring, neg_div_neg_eq]
  have eR : (1 - (w : ℂ) / (w - 1)) / ((1 - (w : ℂ) / (w - 1)) - 1) = 1 / (w : ℂ) := by
    rw [one_sub_div h1, show (w : ℂ) - 1 - w = -1 from by ring, div_sub_one h1,
        show (-1 : ℂ) - (w - 1) = -w from by ring, div_div_div_cancel_right₀ h1, neg_div_neg_eq]
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, anharmS_apply, anharmT_apply]
  rw [eL, eR]

/-- **The anharmonic group** `⟨S, T⟩ ≅ S₃` inside `Equiv.Perm (ℂ∖{0,1})`. -/
def anharmonicGroup : Subgroup (Equiv.Perm Punctured) :=
  Subgroup.closure {anharmS, anharmT}

/-- The explicit six elements of the anharmonic `S₃`. -/
def sixSet : Set (Equiv.Perm Punctured) :=
  {1, anharmS, anharmT, anharmS * anharmT, anharmT * anharmS, anharmS * anharmT * anharmS}

theorem sixSet_finite : sixSet.Finite := by
  unfold sixSet
  exact ((((Set.finite_singleton _).insert _).insert _).insert _).insert _ |>.insert _

theorem anharmS_inv : anharmS⁻¹ = anharmS := inv_eq_of_mul_eq_one_right anharmS_sq
theorem anharmT_inv : anharmT⁻¹ = anharmT := inv_eq_of_mul_eq_one_right anharmT_sq

/-- **`⟨S,T⟩` has at most six elements.** Closure induction multiplying by a *generator* on the left
(`closure_induction_left`): only the 12 short products `S·g`, `T·g` (`g ∈ sixSet`) arise, each reduced
by `S²=T²=1` and the braid `TST=STS`. -/
theorem anharmonicGroup_subset_sixSet :
    (anharmonicGroup : Set (Equiv.Perm Punctured)) ⊆ sixSet := by
  intro φ hφ
  simp only [anharmonicGroup, SetLike.mem_coe] at hφ
  induction hφ using Subgroup.closure_induction_left with
  | one => simp [sixSet]
  | mul_left x hx y _ ih =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [sixSet, Set.mem_insert_iff, Set.mem_singleton_iff] at ih ⊢
    rcases hx with rfl | rfl <;> rcases ih with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | (rw [mul_one]; tauto)
        | (rw [anharmS_sq]; tauto)
        | (rw [anharmT_sq]; tauto)
        | tauto
        | (rw [← mul_assoc]; tauto)
        | (rw [← mul_assoc, anharmS_sq, one_mul]; tauto)
        | (rw [← mul_assoc, anharmT_sq, one_mul]; tauto)
        | (rw [← mul_assoc, anharm_braid.symm]; tauto)
        | (rw [← mul_assoc, ← mul_assoc, anharmS_sq, one_mul]; tauto)
        | (rw [← mul_assoc, ← mul_assoc, anharm_braid.symm, mul_assoc, anharmS_sq, mul_one]; tauto)
  | inv_mul_cancel x hx y _ ih =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [sixSet, Set.mem_insert_iff, Set.mem_singleton_iff] at ih ⊢
    rcases hx with rfl | rfl <;>
      [rw [anharmS_inv]; rw [anharmT_inv]] <;>
    rcases ih with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | (rw [mul_one]; tauto)
        | (rw [anharmS_sq]; tauto)
        | (rw [anharmT_sq]; tauto)
        | tauto
        | (rw [← mul_assoc]; tauto)
        | (rw [← mul_assoc, anharmS_sq, one_mul]; tauto)
        | (rw [← mul_assoc, anharmT_sq, one_mul]; tauto)
        | (rw [← mul_assoc, anharm_braid.symm]; tauto)
        | (rw [← mul_assoc, ← mul_assoc, anharmS_sq, one_mul]; tauto)
        | (rw [← mul_assoc, ← mul_assoc, anharm_braid.symm, mul_assoc, anharmS_sq, mul_one]; tauto)

instance : Finite anharmonicGroup :=
  Set.Finite.to_subtype (sixSet_finite.subset anharmonicGroup_subset_sixSet)

/-- The `S`-generator is continuous (restriction of the affine map `w ↦ 1−w`). -/
theorem continuous_anharmS : Continuous (anharmS : Punctured → Punctured) :=
  continuous_induced_rng.2 (continuous_const.sub continuous_induced_dom)

/-- The `T`-generator is continuous (`w ↦ w/(w−1)`, denominator nonvanishing on `ℂ∖{0,1}`). -/
theorem continuous_anharmT : Continuous (anharmT : Punctured → Punctured) :=
  continuous_induced_rng.2
    (continuous_induced_dom.div (continuous_induced_dom.sub continuous_const)
      (fun w => punct_ne_one w))

/-- **Every anharmonic permutation is continuous** (it is one of the six words in `S, T`). Combined with
its being an `Equiv`, each `φ ∈ ⟨S,T⟩` is a self-homeomorphism of `ℂ∖{0,1}`. -/
theorem continuous_of_mem_anharmonicGroup {φ : Equiv.Perm Punctured} (hφ : φ ∈ anharmonicGroup) :
    Continuous (φ : Punctured → Punctured) := by
  have h6 := anharmonicGroup_subset_sixSet hφ
  simp only [sixSet, Set.mem_insert_iff, Set.mem_singleton_iff] at h6
  rcases h6 with rfl | rfl | rfl | rfl | rfl | rfl
  · exact continuous_id
  · exact continuous_anharmS
  · exact continuous_anharmT
  · exact continuous_anharmS.comp continuous_anharmT
  · exact continuous_anharmT.comp continuous_anharmS
  · exact (continuous_anharmS.comp continuous_anharmT).comp continuous_anharmS

/-- **The `SL(2,ℤ)`-action on `λ`-values is by the anharmonic group.** For every `g ∈ SL(2,ℤ)` there
is an anharmonic permutation `φ` (in `⟨S,T⟩ ≅ S₃`) with `λ(g•τ) = φ(λ τ)` for all `τ`. The proof is a
closure induction over `SL(2,ℤ) = ⟨S,T⟩`; the `mul` step is automatic `Equiv` composition (no cross-ratio
algebra). This is the value-side realisation of `λ` as the `Γ(2)`-Hauptmodul / `S₃`-cover quotient,
and the engine of the cusp/properness half of surjectivity. -/
theorem exists_anharm_eq (g : SL(2, ℤ)) :
    ∃ φ ∈ anharmonicGroup, ∀ τ : ℍ, lambdaPunct (g • τ) = φ (lambdaPunct τ) := by
  have hmem : g ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hmem using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨anharmS, Subgroup.subset_closure (by simp), lambdaPunct_smul_S⟩
    · exact ⟨anharmT, Subgroup.subset_closure (by simp), lambdaPunct_smul_T⟩
  | one => exact ⟨1, one_mem _, fun τ => by rw [one_smul]; rfl⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨φx, hφx, hx⟩ := ihx
    obtain ⟨φy, hφy, hy⟩ := ihy
    refine ⟨φx * φy, mul_mem hφx hφy, fun τ => ?_⟩
    rw [mul_smul, hx (y • τ), hy τ, Equiv.Perm.mul_apply]
  | inv x _ ih =>
    obtain ⟨φ, hφ, hx⟩ := ih
    refine ⟨φ⁻¹, inv_mem hφ, fun τ => ?_⟩
    have := hx (x⁻¹ • τ)
    rw [← mul_smul, mul_inv_cancel, one_smul] at this
    rw [this]; exact (φ.symm_apply_apply _).symm

/-- **`‖1/λ‖ → ∞` at the cusp `∞`** — the third cusp value `∞`. Since `λ → 0` (hence `‖λ‖ → 0⁺`,
`λ ≠ 0` on `ℍ`), the reciprocal value `1/λ` blows up: this is `λ → ∞` read off at the cusp `1`
(the anharmonic inversion-image of `∞`). Completes the three cusp values `{0,1,∞}`. -/
theorem tendsto_norm_inv_modularLambda_atImInfty :
    Tendsto (fun σ : ℂ => ‖modularLambda σ‖⁻¹) (comap Complex.im atTop) atTop := by
  have h0 : Tendsto (fun σ : ℂ => ‖modularLambda σ‖) (comap Complex.im atTop) (𝓝 0) := by
    simpa using tendsto_modularLambda_atImInfty.norm
  refine Tendsto.inv_tendsto_nhdsGT_zero ?_
  rw [tendsto_nhdsWithin_iff]
  refine ⟨h0, ?_⟩
  filter_upwards [tendsto_comap.eventually (eventually_gt_atTop (0 : ℝ))] with σ hσ
  exact Set.mem_Ioi.mpr (norm_pos_iff.mpr (modularLambda_omits_zero_one' hσ).1)

end Bottcher
