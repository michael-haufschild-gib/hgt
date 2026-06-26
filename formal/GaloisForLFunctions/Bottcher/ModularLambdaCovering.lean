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

/-- **`‖1/λ‖ → ∞` at the cusp `∞`** — the cusp value `∞`. Since `λ → 0` (hence `‖λ‖ → 0⁺`, `λ ≠ 0`
on `ℍ`), the reciprocal value `1/λ` blows up. -/
theorem tendsto_norm_inv_modularLambda_atImInfty :
    Tendsto (fun σ : ℂ => ‖modularLambda σ‖⁻¹) (comap Complex.im atTop) atTop := by
  have h0 : Tendsto (fun σ : ℂ => ‖modularLambda σ‖) (comap Complex.im atTop) (𝓝 0) := by
    simpa using tendsto_modularLambda_atImInfty.norm
  refine Tendsto.inv_tendsto_nhdsGT_zero ?_
  rw [tendsto_nhdsWithin_iff]
  refine ⟨h0, ?_⟩
  filter_upwards [tendsto_comap.eventually (eventually_gt_atTop (0 : ℝ))] with σ hσ
  exact Set.mem_Ioi.mpr (norm_pos_iff.mpr (modularLambda_omits_zero_one' hσ).1)

/-! ### The six anharmonic cusp values at `i∞` (where `λ → 0`).

For the escaping-cusp half of surjectivity: as `σ → i∞`, `λ(σ) → 0`, and each of the six anharmonic
value-functions `(φ ∘ λ)(σ)` tends into `{0, 1, ∞}` — never to a point of `ℂ∖{0,1}`. The `T`/`ST`
images tend to `0`/`1`; the `TS`/`STS` images blow up in norm. -/

/-- `T`-value `λ/(λ−1) → 0`. -/
theorem tendsto_modularLambda_div_sub_one :
    Tendsto (fun σ : ℂ => modularLambda σ / (modularLambda σ - 1)) (comap Complex.im atTop) (𝓝 0) := by
  have h := tendsto_modularLambda_atImInfty
  simpa using h.div (h.sub_const 1) (by norm_num : (0 : ℂ) - 1 ≠ 0)

/-- `ST`-value `1 − λ/(λ−1) → 1`. -/
theorem tendsto_one_sub_modularLambda_div_sub_one :
    Tendsto (fun σ : ℂ => 1 - modularLambda σ / (modularLambda σ - 1))
      (comap Complex.im atTop) (𝓝 1) := by
  simpa using (tendsto_const_nhds (x := (1 : ℂ))).sub tendsto_modularLambda_div_sub_one

/-- `TS`-value `(1−λ)/((1−λ)−1)` blows up in norm (`= ‖1−λ‖·‖λ‖⁻¹ → ∞`). -/
theorem tendsto_anharmTS_norm_atTop :
    Tendsto (fun σ : ℂ => ‖(1 - modularLambda σ) / ((1 - modularLambda σ) - 1)‖)
      (comap Complex.im atTop) atTop := by
  have hnorm1 : Tendsto (fun σ : ℂ => ‖1 - modularLambda σ‖) (comap Complex.im atTop) (𝓝 1) := by
    simpa using tendsto_one_sub_modularLambda_atImInfty.norm
  have key := hnorm1.pos_mul_atTop (by norm_num : (0 : ℝ) < 1) tendsto_norm_inv_modularLambda_atImInfty
  refine key.congr (fun σ => ?_)
  rw [show (1 - modularLambda σ) - 1 = -modularLambda σ from by ring, norm_div, norm_neg,
      div_eq_mul_inv]

/-- `STS`-value `= 1/λ` (on `ℍ`, where `λ ≠ 0`), so its norm `→ ∞` (reusing `‖1/λ‖ = ‖λ‖⁻¹`). -/
theorem tendsto_anharmSTS_norm_atTop :
    Tendsto (fun σ : ℂ => ‖1 - (1 - modularLambda σ) / ((1 - modularLambda σ) - 1)‖)
      (comap Complex.im atTop) atTop := by
  refine tendsto_norm_inv_modularLambda_atImInfty.congr' ?_
  filter_upwards [tendsto_comap.eventually (eventually_gt_atTop (0 : ℝ))] with σ hσ
  have hne : modularLambda σ ≠ 0 := (modularLambda_omits_zero_one' hσ).1
  rw [show 1 - (1 - modularLambda σ) / ((1 - modularLambda σ) - 1) = (modularLambda σ)⁻¹ from by
        rw [show (1 - modularLambda σ) - 1 = -modularLambda σ from by ring]; field_simp; ring,
      norm_inv]

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

/-! ### Topological frame for surjectivity: `range λ` is open, `ℂ∖{0,1}` is connected. -/

@[simp] theorem lambdaPunct_coe (τ : ℍ) : (lambdaPunct τ : ℂ) = modularLambda (τ : ℂ) := rfl

/-- **`range (λ : ℍ → ℂ∖{0,1})` is open.** It is `Subtype.val ⁻¹'` of the open image `λ(ℍ) ⊆ ℂ`. -/
theorem isOpen_range_lambdaPunct : IsOpen (Set.range lambdaPunct) := by
  have heq : Set.range lambdaPunct = Subtype.val ⁻¹' (modularLambda '' {z : ℂ | 0 < z.im}) := by
    ext w
    simp only [Set.mem_range, Set.mem_preimage, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨τ, rfl⟩; exact ⟨(τ : ℂ), τ.2, rfl⟩
    · rintro ⟨z, hz, hzeq⟩; exact ⟨⟨z, hz⟩, Subtype.ext hzeq⟩
  rw [heq]; exact isOpen_modularLambda_image.preimage continuous_subtype_val

/-- **`ℂ∖{0,1}` is connected** (complement of a finite set in `ℂ ≅ ℝ²`, `rank ℝ ℂ = 2 > 1`). -/
theorem isConnected_compl_zero_one : IsConnected ({0, 1} : Set ℂ)ᶜ :=
  Set.Countable.isConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)
    ((Set.finite_singleton (1 : ℂ)).insert 0).countable

/-- `λ : ℍ → ℂ∖{0,1}` is continuous. -/
theorem continuous_lambdaPunct : Continuous lambdaPunct :=
  continuous_induced_rng.2 continuous_modularLambda_comp

/-- **`λ : ℍ → ℂ∖{0,1}` is a local homeomorphism** (subtype form). The ambient `λ : ℂ → ℂ` is a local
homeo on `ℍ` (`isLocalHomeomorphOn_modularLambda`); composing the open embeddings `ℍ ↪ ℂ`, `ℂ∖{0,1} ↪ ℂ`
transfers this to the subtype map. The covering-map datum on the source/target spaces. -/
theorem isLocalHomeomorph_lambdaPunct : IsLocalHomeomorph lambdaPunct := by
  have hvalP : IsLocalHomeomorph (Subtype.val : Punctured → ℂ) :=
    (IsOpen.isOpenEmbedding_subtypeVal
      (isOpen_compl_iff.mpr ((Set.finite_singleton (1 : ℂ)).insert 0).isClosed)).isLocalHomeomorph
  have hcomp : IsLocalHomeomorph ((Subtype.val : Punctured → ℂ) ∘ lambdaPunct) := by
    have heq : (Subtype.val : Punctured → ℂ) ∘ lambdaPunct = modularLambda ∘ UpperHalfPlane.coe := rfl
    rw [heq, isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
    exact isLocalHomeomorphOn_modularLambda.comp
      isOpenEmbedding_coe.isLocalHomeomorph.isLocalHomeomorphOn (fun z _ => z.2)
  exact IsLocalHomeomorph.of_comp hcomp hvalP continuous_lambdaPunct

/-- **Escaping-cusp exclusion.** If `ν k → i∞` (`Im → ∞`), then for any anharmonic `φ` the value
`(φ ∘ λ)(ν k)` cannot converge to a point `w₀ ∈ ℂ∖{0,1}`: casing `φ` into the six explicit maps, the
value tends to `0`, `1`, or `∞` in norm. This excludes the escaping subsequence in the closed-image
argument. -/
theorem anharm_cusp_ne {φ : Equiv.Perm Punctured} (hφ : φ ∈ anharmonicGroup)
    {ν : ℕ → ℍ} (hν : Tendsto (fun k => ((ν k : ℂ)).im) atTop atTop)
    {w₀ : ℂ} (hw₀ : w₀ ∈ ({0, 1} : Set ℂ)ᶜ) :
    ¬ Tendsto (fun k => (φ (lambdaPunct (ν k)) : ℂ)) atTop (𝓝 w₀) := by
  intro hcon
  have hcoe : Tendsto (fun k => ((ν k : ℂ))) atTop (comap Complex.im atTop) :=
    tendsto_comap_iff.mpr hν
  rw [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hw₀
  have h6 := anharmonicGroup_subset_sixSet hφ
  simp only [sixSet, Set.mem_insert_iff, Set.mem_singleton_iff] at h6
  rcases h6 with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [Equiv.Perm.coe_one, id_eq, lambdaPunct_coe] at hcon
    exact hw₀.1 (tendsto_nhds_unique hcon (tendsto_modularLambda_atImInfty.comp hcoe))
  · simp only [anharmS_apply, lambdaPunct_coe] at hcon
    exact hw₀.2 (tendsto_nhds_unique hcon (tendsto_one_sub_modularLambda_atImInfty.comp hcoe))
  · simp only [anharmT_apply, lambdaPunct_coe] at hcon
    exact hw₀.1 (tendsto_nhds_unique hcon (tendsto_modularLambda_div_sub_one.comp hcoe))
  · simp only [Equiv.Perm.coe_mul, Function.comp_apply, anharmS_apply, anharmT_apply,
      lambdaPunct_coe] at hcon
    exact hw₀.2 (tendsto_nhds_unique hcon (tendsto_one_sub_modularLambda_div_sub_one.comp hcoe))
  · simp only [Equiv.Perm.coe_mul, Function.comp_apply, anharmT_apply, anharmS_apply,
      lambdaPunct_coe] at hcon
    exact not_tendsto_atTop_of_tendsto_nhds hcon.norm (tendsto_anharmTS_norm_atTop.comp hcoe)
  · simp only [Equiv.Perm.coe_mul, Function.comp_apply, anharmS_apply, anharmT_apply,
      lambdaPunct_coe] at hcon
    exact not_tendsto_atTop_of_tendsto_nhds hcon.norm (tendsto_anharmSTS_norm_atTop.comp hcoe)

/-- **`range (λ : ℍ → ℂ∖{0,1})` is closed** — the properness/cusp half of surjectivity. A limit
`x = lim λ(τ_n)` is reached as follows: move each `τ_n` into the `SL(2,ℤ)` fundamental domain `𝒟`
(`exists_smul_mem_fd`), track `λ` through the anharmonic action (`exists_anharm_eq`), pick (pigeonhole,
`Finite anharmonicGroup`) one `φ₀` occurring infinitely often; on that subsequence the `𝒟`-points are
either bounded in `Im` — then `𝒟∩{Im≤M}` is compact (`isCompact_truncatedFundamentalDomain`), a
sub-subsequence converges to `a ∈ ℍ`, and `x = φ₀(λ a) = λ(g⁻¹•a) ∈ range` — or escape to the cusp,
excluded by `anharm_cusp_ne`. -/
theorem isClosed_range_lambdaPunct : IsClosed (Set.range lambdaPunct) := by
  apply IsSeqClosed.isClosed
  intro u x hu hux
  choose τ hτ using hu
  choose g hg using fun n => exists_smul_mem_fd (τ n)
  choose φ hφmem hφeq using fun n => exists_anharm_eq (g n)⁻¹
  set σ : ℕ → ℍ := fun n => g n • τ n with hσdef
  have hun : ∀ n, u n = φ n (lambdaPunct (σ n)) := by
    intro n
    have hτn : τ n = (g n)⁻¹ • σ n := by rw [hσdef, ← mul_smul, inv_mul_cancel, one_smul]
    rw [← hτ n, hτn, hφeq n (σ n)]
  obtain ⟨⟨φ₀, hφ₀⟩, hinf⟩ :=
    Finite.exists_infinite_fiber (fun n => (⟨φ n, hφmem n⟩ : anharmonicGroup))
  rw [Set.infinite_coe_iff] at hinf
  have hSinf : {n | φ n = φ₀}.Infinite := by
    apply hinf.mono
    intro n hn
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.mk.injEq] at hn
    exact hn
  obtain ⟨ρ, hρmono, hρS⟩ :=
    extraction_of_frequently_atTop (Nat.frequently_atTop_iff_infinite.mpr hSinf)
  by_cases hb : ∃ M : ℝ, {k | (σ (ρ k)).im ≤ M}.Infinite
  · obtain ⟨M, hM⟩ := hb
    obtain ⟨ρ', hρ'mono, hρ'⟩ :=
      extraction_of_frequently_atTop (Nat.frequently_atTop_iff_infinite.mpr hM)
    have hmem : ∀ j, σ (ρ (ρ' j)) ∈ ModularGroup.truncatedFundamentalDomain M :=
      fun j => ⟨hg (ρ (ρ' j)), hρ' j⟩
    obtain ⟨a, _, ρ'', hρ''mono, hconv⟩ :=
      (ModularGroup.isCompact_truncatedFundamentalDomain M).tendsto_subseq hmem
    have hla : Tendsto (fun i => lambdaPunct (σ (ρ (ρ' (ρ'' i))))) atTop (𝓝 (lambdaPunct a)) :=
      (continuous_lambdaPunct.tendsto a).comp hconv
    have hφla : Tendsto (fun i => φ₀ (lambdaPunct (σ (ρ (ρ' (ρ'' i)))))) atTop
        (𝓝 (φ₀ (lambdaPunct a))) :=
      ((continuous_of_mem_anharmonicGroup hφ₀).tendsto _).comp hla
    have hψ : StrictMono (fun i => ρ (ρ' (ρ'' i))) := hρmono.comp (hρ'mono.comp hρ''mono)
    have hux' : Tendsto (fun i => u (ρ (ρ' (ρ'' i)))) atTop (𝓝 x) := hux.comp hψ.tendsto_atTop
    have heq : (fun i => u (ρ (ρ' (ρ'' i)))) = fun i => φ₀ (lambdaPunct (σ (ρ (ρ' (ρ'' i))))) := by
      funext i; rw [hun, hρS]
    rw [heq] at hux'
    have hxeq : x = φ₀ (lambdaPunct a) := tendsto_nhds_unique hux' hφla
    exact ⟨(g (ρ (ρ' (ρ'' 0))))⁻¹ • a, by rw [hxeq, ← hρS (ρ' (ρ'' 0)), ← hφeq (ρ (ρ' (ρ'' 0))) a]⟩
  · push_neg at hb
    have hImtop : Tendsto (fun k => (σ (ρ k)).im) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro M
      obtain ⟨N, hN⟩ := (hb M).bddAbove
      refine ⟨N + 1, fun k hk => ?_⟩
      by_contra hlt
      push_neg at hlt
      have := hN hlt.le
      omega
    have heq : (fun k => (u (ρ k) : ℂ)) = fun k => (φ₀ (lambdaPunct (σ (ρ k))) : ℂ) := by
      funext k; rw [hun, hρS]
    have hux' : Tendsto (fun k => (u (ρ k) : ℂ)) atTop (𝓝 (x : ℂ)) :=
      (continuous_subtype_val.tendsto x).comp (hux.comp hρmono.tendsto_atTop)
    rw [heq] at hux'
    exact absurd hux' (anharm_cusp_ne hφ₀ hImtop x.2)

/-- **`λ : ℍ → ℂ∖{0,1}` is surjective** (little Picard for the modular `λ`). Its range is clopen
(open: local homeo; closed: `isClosed_range_lambdaPunct`) and nonempty in the connected space
`ℂ∖{0,1}`, hence everything. -/
theorem lambdaPunct_surjective : Function.Surjective lambdaPunct := by
  haveI : PreconnectedSpace Punctured :=
    isPreconnected_iff_preconnectedSpace.mp isConnected_compl_zero_one.isPreconnected
  rw [← Set.range_eq_univ]
  rcases isClopen_iff.mp ⟨isClosed_range_lambdaPunct, isOpen_range_lambdaPunct⟩ with h | h
  · exact absurd h (Set.range_nonempty lambdaPunct).ne_empty
  · exact h

/-- **`λ` attains every value in `ℂ∖{0,1}`** on the upper half-plane. -/
theorem modularLambda_surjective {w : ℂ} (hw : w ∈ ({0, 1} : Set ℂ)ᶜ) :
    ∃ τ : ℂ, 0 < τ.im ∧ modularLambda τ = w := by
  obtain ⟨z, hz⟩ := lambdaPunct_surjective ⟨w, hw⟩
  exact ⟨(z : ℂ), z.2, congrArg Subtype.val hz⟩

/-! ### The anharmonic representation `SL(2,ℤ) → S₃` (well-defined by surjectivity).

Now that `λ` is surjective, the anharmonic permutation realizing `λ(g•τ) = φ_g(λ τ)` is **unique**, so
`g ↦ φ_g` is a genuine group homomorphism `SL(2,ℤ) → ⟨S,T⟩ ≅ S₃`, with `Γ(2)` in its kernel. This is
the algebraic skeleton of the fibre/orbit structure (`λ̄` injectivity): `λ(τ)=λ(τ')` forces the
connecting `SL(2,ℤ)`-element into `Γ(2)` *once* the remaining (analytic) univalence input is supplied. -/

/-- **Two permutations agreeing after `λ` are equal** — the well-definedness lemma, straight from
surjectivity of `λ`. -/
theorem eq_of_eq_on_lambdaPunct {φ φ' : Equiv.Perm Punctured}
    (h : ∀ τ, φ (lambdaPunct τ) = φ' (lambdaPunct τ)) : φ = φ' := by
  ext w
  obtain ⟨τ, rfl⟩ := lambdaPunct_surjective w
  exact congrArg Subtype.val (h τ)

/-- The anharmonic permutation attached to `g ∈ SL(2,ℤ)`. -/
noncomputable def anharmElem (g : SL(2, ℤ)) : Equiv.Perm Punctured :=
  Classical.choose (exists_anharm_eq g)

theorem anharmElem_mem (g : SL(2, ℤ)) : anharmElem g ∈ anharmonicGroup :=
  (Classical.choose_spec (exists_anharm_eq g)).1

theorem anharmElem_eq (g : SL(2, ℤ)) (τ : ℍ) :
    lambdaPunct (g • τ) = anharmElem g (lambdaPunct τ) :=
  (Classical.choose_spec (exists_anharm_eq g)).2 τ

theorem anharmElem_one : anharmElem 1 = 1 := by
  refine eq_of_eq_on_lambdaPunct (fun τ => ?_)
  rw [← anharmElem_eq, one_smul, Equiv.Perm.one_apply]

theorem anharmElem_mul (g h : SL(2, ℤ)) : anharmElem (g * h) = anharmElem g * anharmElem h := by
  refine eq_of_eq_on_lambdaPunct (fun τ => ?_)
  rw [Equiv.Perm.mul_apply, ← anharmElem_eq, ← anharmElem_eq, ← anharmElem_eq, ← mul_smul]

/-- **The anharmonic representation** `SL(2,ℤ) → Equiv.Perm (ℂ∖{0,1})`, `g ↦ φ_g`. -/
noncomputable def anharmHom : SL(2, ℤ) →* Equiv.Perm Punctured where
  toFun := anharmElem
  map_one' := anharmElem_one
  map_mul' := anharmElem_mul

/-- **`Γ(2) ≤ ker (anharmonic representation)`** — every `γ ∈ Γ(2)` acts trivially on `λ`-values
(`λ(γ•τ) = λ(τ)`), so `φ_γ = 1`. -/
theorem gamma2_le_ker_anharmHom : CongruenceSubgroup.Gamma 2 ≤ anharmHom.ker := by
  intro γ hγ
  rw [MonoidHom.mem_ker]
  refine eq_of_eq_on_lambdaPunct (fun τ => ?_)
  show anharmElem γ (lambdaPunct τ) = (1 : Equiv.Perm Punctured) (lambdaPunct τ)
  rw [← anharmElem_eq, Equiv.Perm.one_apply]
  exact Subtype.ext (modularLambda_smul hγ τ)

/-! ### Schwarz reflection: `λ(−conj τ) = conj(λ τ)`, and `λ` real on the imaginary axis.

The theta constants have real `q`-expansions, so they satisfy `θ(−conj τ) = conj(θ τ)`. This makes `λ`
satisfy the **Schwarz reflection** across the imaginary axis — the analytic foundation of the boundary
correspondence behind the fundamental-domain univalence (hence `λ̄` injectivity, task #28). -/

/-- `θ₃(−conj τ) = conj(θ₃ τ)`. -/
theorem thetaThree_conj (τ : ℂ) :
    (starRingEnd ℂ) (thetaThree τ) = thetaThree (-(starRingEnd ℂ) τ) := by
  rw [thetaThree, thetaThree, jacobiTheta₂_conj, map_zero]

/-- `θ₂(−conj τ) = conj(θ₂ τ)` (the `e^{πiτ/4}` prefactor conjugates correctly, and `jacobiTheta₂` is
even in its first argument). -/
theorem thetaTwo_conj (τ : ℂ) :
    (starRingEnd ℂ) (thetaTwo τ) = thetaTwo (-(starRingEnd ℂ) τ) := by
  rw [thetaTwo, thetaTwo, map_mul, jacobiTheta₂_conj, ← Complex.exp_conj]
  congr 1
  · congr 1
    simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  · rw [show ((-(starRingEnd ℂ) τ) / 2 : ℂ) = -((starRingEnd ℂ) (τ / 2)) from by
        rw [map_div₀, map_ofNat]; ring, jacobiTheta₂_neg_left]

/-- **Schwarz reflection for `λ`:** `λ(−conj τ) = conj(λ τ)`. -/
theorem modularLambda_conj (τ : ℂ) :
    modularLambda (-(starRingEnd ℂ) τ) = (starRingEnd ℂ) (modularLambda τ) := by
  rw [modularLambda, modularLambda, map_pow, map_div₀, thetaTwo_conj, thetaThree_conj]

/-- **`λ` is real on the imaginary axis.** For `τ = t·i` (`t > 0`), `−conj τ = τ`, so
`λ(τ) = conj(λ(τ))`, i.e. `λ(τ) ∈ ℝ`. The first boundary arc of the fundamental-domain correspondence. -/
theorem modularLambda_im_axis_real {t : ℝ} :
    (modularLambda ((t : ℂ) * Complex.I)).im = 0 := by
  have hfix : -(starRingEnd ℂ) ((t : ℂ) * Complex.I) = (t : ℂ) * Complex.I := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  have h := modularLambda_conj ((t : ℂ) * Complex.I)
  rw [hfix] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- **`λ` is real on the vertical line `Re = 1`.** Reflection across `Re = 1` is `τ ↦ 2 − conj τ`;
combined with the `Γ(2)`-translation `λ(·+2) = λ(·)` and Schwarz reflection, `λ(1+it) = conj(λ(1+it))`.
The second boundary arc of the fundamental-domain correspondence. -/
theorem modularLambda_re_one_real {t : ℝ} :
    (modularLambda (1 + (t : ℂ) * Complex.I)).im = 0 := by
  have hfix : -(starRingEnd ℂ) (1 + (t : ℂ) * Complex.I) + 2 = 1 + (t : ℂ) * Complex.I := by
    rw [map_add, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  have h := modularLambda_conj (1 + (t : ℂ) * Complex.I)
  rw [← modularLambda_add_two (-(starRingEnd ℂ) (1 + (t : ℂ) * Complex.I)), hfix] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-! ### `Γ(2)` has no elliptic elements (`|trace| ≥ 2`) — the free-action core for the covering.

Every `γ ∈ Γ(2)` has `trace ≡ 2 (mod 4)`: the diagonal entries are odd, the off-diagonal even, and the
determinant `= 1` forces `a+d = 4e+2`. Hence `|trace| ≥ 2` (no elliptic elements), so `Γ(2)` mod `±I`
acts freely on `ℍ` — the input to the properly-discontinuous *free* quotient covering `ℍ → ℍ/Γ(2)`. -/

/-- For `γ ∈ Γ(2)`, the trace has the form `4e + 2`. -/
theorem Gamma2_trace_form {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma 2) :
    ∃ e : ℤ, g.1 0 0 + g.1 1 1 = 4 * e + 2 := by
  obtain ⟨h00, h01, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.mp hg
  have e00 : (2 : ℤ) ∣ (g.1 0 0 - 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h00]; ring
  have e11 : (2 : ℤ) ∣ (g.1 1 1 - 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h11]; ring
  have e01 : (2 : ℤ) ∣ g.1 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h01
  have e10 : (2 : ℤ) ∣ g.1 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h10
  obtain ⟨a, ha⟩ := e00; obtain ⟨b, hb⟩ := e11; obtain ⟨c, hc⟩ := e01; obtain ⟨d, hd⟩ := e10
  have hdet : g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
    have h := g.2; rwa [Matrix.det_fin_two] at h
  refine ⟨c * d - a * b, ?_⟩
  have ha' : g.1 0 0 = 2 * a + 1 := by omega
  have hb' : g.1 1 1 = 2 * b + 1 := by omega
  rw [ha', hb', ha', hb', hc, hd] at *
  linear_combination hdet

/-- **`Γ(2)` has no elliptic elements:** every `γ ∈ Γ(2)` has `|trace| ≥ 2`. -/
theorem Gamma2_abs_trace_ge_two {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma 2) :
    2 ≤ |g.1 0 0 + g.1 1 1| := by
  obtain ⟨e, he⟩ := Gamma2_trace_form hg
  rw [he]
  rcases le_or_lt 0 e with h | h
  · rw [abs_of_nonneg (by omega)]; omega
  · rw [abs_of_neg (by omega)]; omega

end Bottcher
