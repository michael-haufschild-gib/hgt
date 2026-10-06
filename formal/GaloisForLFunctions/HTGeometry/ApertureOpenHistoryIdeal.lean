import GaloisForLFunctions.HTGeometry.ApertureConeCalculus

/-!
# The open-history ideal of the aperture cone

The open-history ideal `J_T = C*(e_c − e_d : c, d > 0)` inside `C*(e_1) ≅ C_0((0,1])`.

* The difference quotients `(e_{1+s} − e_1)/s = e(1 − e)(1 + se)⁻¹` converge to `e − e²` as
  `s → 0`, and the second quotients to `e² − e³`; hence `κ(e) ∈ J_T` for the profile
  `κ(t) = t(1 − t)(1 + it)`, which identifies exactly the endpoints `0` and `1` of `[0,1]`.
* Every `g` vanishing at both endpoints factors continuously through `κ` (quotient map from the
  compact interval), so `g(e) ∈ C*(κ(e)) ⊆ J_T`.

Hence (SAC.6) `J_T` is the image of the suspension `C_0((0,1)) = {g : g(0) = g(1) = 0}` under the
isometric functional calculus of `e_1`, and (SAC.7) `0 → J_T → C*(e_1) → ℂ → 0` is the endpoint
sequence: `J_T` is the kernel of evaluation at the closed aperture, which is onto and sends every
scale germ to `1`.
-/

set_option autoImplicit false

open Filter Topology Set ContinuousLinearMap
open scoped ContinuousMapZero

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {T : H →L[ℂ] H} (hT : T.IsPositive) (hcpt : IsCompactOperator T)

/-! ## The open-history ideal -/

/-- The open-history ideal `J_T = C*(e_c − e_d : c, d > 0)`. -/
def openHistoryIdeal : NonUnitalStarSubalgebra ℂ (BoundaryCorona H) :=
  (NonUnitalStarAlgebra.adjoin ℂ {x | ∃ (c d : ℝ) (hc : 0 < c) (hd : 0 < d),
    x = scaleGerm T hT hcpt hc - scaleGerm T hT hcpt hd}).topologicalClosure

theorem isClosed_openHistoryIdeal : IsClosed (openHistoryIdeal hT hcpt : Set (BoundaryCorona H)) :=
  NonUnitalStarSubalgebra.isClosed_topologicalClosure _

theorem scaleGerm_sub_mem_openHistoryIdeal {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    scaleGerm T hT hcpt hc - scaleGerm T hT hcpt hd ∈ openHistoryIdeal hT hcpt :=
  NonUnitalStarSubalgebra.le_topologicalClosure _
    (NonUnitalStarAlgebra.subset_adjoin ℂ _ ⟨c, d, hc, hd, rfl⟩)

section Functional

variable (hinj : Function.Injective T) (hH : ¬ FiniteDimensional ℂ H)

/-- The closed-observer generator `e = e_1`. -/
abbrev unitGerm : BoundaryCorona H := scaleGerm T hT hcpt one_pos

include hinj hH in
theorem quasispectrum_unitGerm : quasispectrum ℂ (unitGerm hT hcpt) = unitIntervalC :=
  quasispectrum_scaleGerm hT hcpt one_pos hinj hH

theorem isStarNormal_unitGerm : IsStarNormal (unitGerm hT hcpt) :=
  (isSelfAdjoint_scaleGerm hT hcpt one_pos).isStarNormal

include hinj hH in
theorem scaleGerm_eq_cfcₙ {c : ℝ} (hc : 0 < c) :
    scaleGerm T hT hcpt hc = cfcₙ (scaleChange c) (unitGerm hT hcpt) := by
  rw [scaleGerm_eq_cfcₙ_scaleChange hT hcpt one_pos hinj hH hc, div_one]

include hinj hH in
/-- Distances of functional calculi of `e` are sup-distances on `[0,1]`. -/
theorem norm_cfcₙ_unitGerm_sub_le {f g : ℂ → ℂ} (hf : ContinuousOn f unitIntervalC)
    (hg : ContinuousOn g unitIntervalC) (hf0 : f 0 = 0) (hg0 : g 0 = 0) {C : ℝ}
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t - g t‖ ≤ C) :
    ‖cfcₙ f (unitGerm hT hcpt) - cfcₙ g (unitGerm hT hcpt)‖ ≤ C := by
  have hσ := quasispectrum_unitGerm hT hcpt hinj hH
  have hn := isStarNormal_unitGerm hT hcpt
  rw [← cfcₙ_sub f g (unitGerm hT hcpt) (by rwa [hσ]) hf0 (by rwa [hσ]) hg0]
  refine norm_cfcₙ_le fun z hz => ?_
  rw [hσ] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  exact hC t ht


include hinj hH in
/-- Uniform limits on `[0,1]` of functional calculi lying in `J_T` lie in `J_T`. -/
theorem cfcₙ_mem_openHistoryIdeal_of_approx {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, ContinuousOn (F n) unitIntervalC) (hF0 : ∀ n, F n 0 = 0)
    (hf : ContinuousOn f unitIntervalC) (hf0 : f 0 = 0)
    (hmem : ∀ n, cfcₙ (F n) (unitGerm hT hcpt) ∈ openHistoryIdeal hT hcpt)
    (happrox : ∀ n, ∀ t ∈ Icc (0 : ℝ) 1, ‖F n t - f t‖ ≤ 1 / ((n : ℝ) + 1)) :
    cfcₙ f (unitGerm hT hcpt) ∈ openHistoryIdeal hT hcpt := by
  have hlim : Tendsto (fun n => cfcₙ (F n) (unitGerm hT hcpt)) atTop
      (𝓝 (cfcₙ f (unitGerm hT hcpt))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n =>
      norm_cfcₙ_unitGerm_sub_le hT hcpt hinj hH (hF n) hf (hF0 n) hf0 (happrox n))
      tendsto_one_div_add_atTop_nhds_zero_nat
  exact (isClosed_openHistoryIdeal hT hcpt).mem_of_tendsto hlim (Eventually.of_forall hmem)

/-- `w₁(s, z) = z(1 − z)/(1 + sz)`. -/
def quotientProfile₁ (s : ℝ) (z : ℂ) : ℂ := z * (1 - z) / (1 + s * z)

/-- `w₂(s, z) = z²(1 − z)/(1 + sz)`. -/
def quotientProfile₂ (s : ℝ) (z : ℂ) : ℂ := z ^ 2 * (1 - z) / (1 + s * z)

theorem quotientProfile₁_ofReal (s t : ℝ) :
    quotientProfile₁ s t = ((t * (1 - t) / (1 + s * t) : ℝ) : ℂ) := by
  simp [quotientProfile₁]

theorem quotientProfile₂_ofReal (s t : ℝ) :
    quotientProfile₂ s t = ((t ^ 2 * (1 - t) / (1 + s * t) : ℝ) : ℂ) := by
  simp [quotientProfile₂]

theorem continuousOn_div_one_add {s : ℝ} (hs : 0 ≤ s) {p : ℂ → ℂ} (hp : Continuous p) :
    ContinuousOn (fun z : ℂ => p z / (1 + s * z)) unitIntervalC := by
  refine hp.continuousOn.div (continuousOn_const.add (continuousOn_const.mul continuousOn_id)) ?_
  rintro _ ⟨t, ⟨ht0, -⟩, rfl⟩
  have : (0 : ℝ) < 1 + s * t := by positivity
  exact_mod_cast this.ne'

theorem continuousOn_scaleChange {r : ℝ} (hr : 0 < r) :
    ContinuousOn (scaleChange r) unitIntervalC := by
  refine (continuousOn_const.mul continuousOn_id).div
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id)) ?_
  rintro _ ⟨t, ht, rfl⟩
  have := scaleChange_denom_pos hr ht
  exact_mod_cast this.ne'


theorem abs_profile_sub_le {s t q : ℝ} (hs : 0 ≤ s) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : |q / (1 + s * t) - q| ≤ s := by
  have hpos : 0 < 1 + s * t := by positivity
  have hD : q - q / (1 + s * t) = q * (s * t) / (1 + s * t) := by field_simp; ring
  rw [abs_sub_comm, abs_of_nonneg (by rw [hD]; positivity), hD, div_le_iff₀ hpos]
  nlinarith [mul_nonneg hs ht0, mul_le_mul hq1 (mul_le_mul_of_nonneg_left ht1 hs)
    (mul_nonneg hs ht0) zero_le_one]

include hinj hH in
theorem cfcₙ_quotientProfile₁_mem {s : ℝ} (hs : 0 < s) :
    cfcₙ (quotientProfile₁ s) (unitGerm hT hcpt) ∈ openHistoryIdeal hT hcpt := by
  have hσ := quasispectrum_unitGerm hT hcpt hinj hH
  have hr : (0 : ℝ) < 1 + s := by linarith
  have hfun : cfcₙ (quotientProfile₁ s) (unitGerm hT hcpt) = cfcₙ (fun z =>
      ((s : ℂ)⁻¹) • (scaleChange (1 + s) z - scaleChange 1 z)) (unitGerm hT hcpt) := by
    refine cfcₙ_congr fun z hz => ?_
    rw [hσ] at hz
    obtain ⟨t, ⟨ht0, -⟩, rfl⟩ := hz
    have hpos : (0 : ℝ) < 1 + s * t := by positivity
    rw [quotientProfile₁_ofReal, scaleChange_ofReal, scaleChange_ofReal, smul_eq_mul,
      ← Complex.ofReal_sub, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
    congr 1
    simp only [add_sub_cancel_left, sub_self, zero_mul, add_zero, one_mul, div_one]
    field_simp
    ring
  have hc1 : ContinuousOn (scaleChange (1 + s)) (quasispectrum ℂ (unitGerm hT hcpt)) := by
    rw [hσ]; exact continuousOn_scaleChange hr
  have hc2 : ContinuousOn (scaleChange 1) (quasispectrum ℂ (unitGerm hT hcpt)) := by
    rw [hσ]; exact continuousOn_scaleChange one_pos
  have h01 : scaleChange (1 + s) 0 = 0 := by simp [scaleChange]
  have h02 : scaleChange 1 0 = 0 := by simp [scaleChange]
  rw [hfun, cfcₙ_smul _ (fun z => scaleChange (1 + s) z - scaleChange 1 z) _ (hc1.sub hc2)
      (by rw [h01, h02, sub_self]),
    cfcₙ_sub _ _ _ hc1 h01 hc2 h02,
    ← scaleGerm_eq_cfcₙ hT hcpt hinj hH hr, ← scaleGerm_eq_cfcₙ hT hcpt hinj hH one_pos]
  exact (openHistoryIdeal hT hcpt).smul_mem _
    (scaleGerm_sub_mem_openHistoryIdeal hT hcpt hr one_pos)

include hinj hH in
theorem cfcₙ_quotientProfile₁_zero_mem :
    cfcₙ (quotientProfile₁ 0) (unitGerm hT hcpt) ∈ openHistoryIdeal hT hcpt := by
  refine cfcₙ_mem_openHistoryIdeal_of_approx hT hcpt hinj hH (F := fun n =>
    quotientProfile₁ (1 / ((n : ℝ) + 1))) (fun n => continuousOn_div_one_add (by positivity)
      (by fun_prop)) (fun n => by simp [quotientProfile₁]) (continuousOn_div_one_add le_rfl
      (by fun_prop)) (by simp [quotientProfile₁])
    (fun n => cfcₙ_quotientProfile₁_mem hT hcpt hinj hH (by positivity)) fun n t ⟨ht0, ht1⟩ => ?_
  rw [quotientProfile₁_ofReal, quotientProfile₁_ofReal, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, zero_mul, add_zero, div_one]
  have hn : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  exact abs_profile_sub_le (by positivity) ht0 ht1 (by nlinarith) (by nlinarith)


include hinj hH in
theorem cfcₙ_quotientProfile₂_mem {s : ℝ} (hs : 0 < s) :
    cfcₙ (quotientProfile₂ s) (unitGerm hT hcpt) ∈ openHistoryIdeal hT hcpt := by
  have hσ := quasispectrum_unitGerm hT hcpt hinj hH
  have hfun : cfcₙ (quotientProfile₂ s) (unitGerm hT hcpt) = cfcₙ (fun z =>
      ((s : ℂ)⁻¹) • (quotientProfile₁ 0 z - quotientProfile₁ s z)) (unitGerm hT hcpt) := by
    refine cfcₙ_congr fun z hz => ?_
    rw [hσ] at hz
    obtain ⟨t, ⟨ht0, -⟩, rfl⟩ := hz
    have hpos : (0 : ℝ) < 1 + s * t := by positivity
    rw [quotientProfile₂_ofReal, quotientProfile₁_ofReal, quotientProfile₁_ofReal, smul_eq_mul,
      ← Complex.ofReal_sub, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
    congr 1
    simp only [zero_mul, add_zero, div_one]
    field_simp
    ring
  have hc1 : ContinuousOn (quotientProfile₁ 0) (quasispectrum ℂ (unitGerm hT hcpt)) := by
    rw [hσ]; exact continuousOn_div_one_add le_rfl (by fun_prop)
  have hc2 : ContinuousOn (quotientProfile₁ s) (quasispectrum ℂ (unitGerm hT hcpt)) := by
    rw [hσ]; exact continuousOn_div_one_add hs.le (by fun_prop)
  have h01 : quotientProfile₁ 0 0 = 0 := by simp [quotientProfile₁]
  have h02 : quotientProfile₁ s 0 = 0 := by simp [quotientProfile₁]
  rw [hfun, cfcₙ_smul _ (fun z => quotientProfile₁ 0 z - quotientProfile₁ s z) _ (hc1.sub hc2)
      (by rw [h01, h02, sub_self]),
    cfcₙ_sub _ _ _ hc1 h01 hc2 h02]
  exact (openHistoryIdeal hT hcpt).smul_mem _ (sub_mem
    (cfcₙ_quotientProfile₁_zero_mem hT hcpt hinj hH) (cfcₙ_quotientProfile₁_mem hT hcpt hinj hH hs))

include hinj hH in
theorem cfcₙ_quotientProfile₂_zero_mem :
    cfcₙ (quotientProfile₂ 0) (unitGerm hT hcpt) ∈ openHistoryIdeal hT hcpt := by
  refine cfcₙ_mem_openHistoryIdeal_of_approx hT hcpt hinj hH (F := fun n =>
    quotientProfile₂ (1 / ((n : ℝ) + 1))) (fun n => continuousOn_div_one_add (by positivity)
      (by fun_prop)) (fun n => by simp [quotientProfile₂]) (continuousOn_div_one_add le_rfl
      (by fun_prop)) (by simp [quotientProfile₂])
    (fun n => cfcₙ_quotientProfile₂_mem hT hcpt hinj hH (by positivity)) fun n t ⟨ht0, ht1⟩ => ?_
  rw [quotientProfile₂_ofReal, quotientProfile₂_ofReal, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, zero_mul, add_zero, div_one]
  exact abs_profile_sub_le (by positivity) ht0 ht1 (by positivity)
    (by nlinarith [mul_nonneg ht0 ht0])

/-- The injective profile `κ(t) = t(1 − t)(1 + it)` of the open aperture. -/
def openProfile (z : ℂ) : ℂ := quotientProfile₁ 0 z + Complex.I • quotientProfile₂ 0 z

include hinj hH in
/-- **`κ(e)` lies in the open-history ideal.** -/
theorem cfcₙ_openProfile_mem :
    cfcₙ openProfile (unitGerm hT hcpt) ∈ openHistoryIdeal hT hcpt := by
  have hσ := quasispectrum_unitGerm hT hcpt hinj hH
  have hc1 : ContinuousOn (quotientProfile₁ 0) (quasispectrum ℂ (unitGerm hT hcpt)) := by
    rw [hσ]; exact continuousOn_div_one_add le_rfl (by fun_prop)
  have hc2 : ContinuousOn (quotientProfile₂ 0) (quasispectrum ℂ (unitGerm hT hcpt)) := by
    rw [hσ]; exact continuousOn_div_one_add le_rfl (by fun_prop)
  have h01 : quotientProfile₁ 0 0 = 0 := by simp [quotientProfile₁]
  have h02 : quotientProfile₂ 0 0 = 0 := by simp [quotientProfile₂]
  rw [show openProfile = fun z => quotientProfile₁ 0 z + Complex.I • quotientProfile₂ 0 z from rfl,
    cfcₙ_add (quotientProfile₁ 0) (fun z => Complex.I • quotientProfile₂ 0 z) _ hc1 h01
      (hc2.const_smul Complex.I) (by rw [h02, smul_zero]),
    cfcₙ_smul _ _ _ hc2 h02]
  exact add_mem (cfcₙ_quotientProfile₁_zero_mem hT hcpt hinj hH)
    ((openHistoryIdeal hT hcpt).smul_mem _ (cfcₙ_quotientProfile₂_zero_mem hT hcpt hinj hH))

end Functional

/-! ## The open profile -/

theorem openProfile_eq : openProfile = fun z => z * (1 - z) + Complex.I • (z ^ 2 * (1 - z)) := by
  funext z; simp [openProfile, quotientProfile₁, quotientProfile₂]

theorem openProfile_ofReal (t : ℝ) :
    openProfile t = ⟨t * (1 - t), t ^ 2 * (1 - t)⟩ := by
  rw [openProfile_eq]
  apply Complex.ext
  · simp only [smul_eq_mul, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    norm_cast; simp
  · simp only [smul_eq_mul, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    norm_cast; simp

theorem continuous_openProfile : Continuous openProfile := by
  rw [openProfile_eq]; fun_prop

theorem openProfile_zero : openProfile 0 = 0 := by simp [openProfile, quotientProfile₁,
  quotientProfile₂]

/-- `κ` identifies exactly the two endpoints of `[0,1]`. -/
theorem openProfile_eq_iff {t u : ℝ} (h : openProfile t = openProfile u) :
    t = u ∨ (t * (1 - t) = 0 ∧ u * (1 - u) = 0) := by
  rw [openProfile_ofReal, openProfile_ofReal, Complex.mk.injEq] at h
  obtain ⟨hre, him⟩ := h
  by_cases hr : t * (1 - t) = 0
  · exact Or.inr ⟨hr, hre ▸ hr⟩
  · left
    have : t * (t * (1 - t)) = u * (u * (1 - u)) := by linear_combination him
    rw [← hre] at this
    exact mul_right_cancel₀ hr this

theorem endpoint_of_mul_one_sub_eq_zero {t : ℝ} (h : t * (1 - t) = 0) : t = 0 ∨ t = 1 := by
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- **Factorization through the open profile**: a function on `[0,1]` vanishing at both endpoints
is a continuous function of `κ`. -/
theorem exists_factor_openProfile {g : ℂ → ℂ} (hg : ContinuousOn g unitIntervalC) (hg0 : g 0 = 0)
    (hg1 : g 1 = 0) :
    ∃ h : ℂ → ℂ, ContinuousOn h (openProfile '' unitIntervalC) ∧ h 0 = 0 ∧
      ∀ z ∈ unitIntervalC, h (openProfile z) = g z := by
  classical
  haveI : CompactSpace unitIntervalC := isCompact_iff_compactSpace.mp isCompact_unitIntervalC
  set Y := openProfile '' unitIntervalC
  let f : C(unitIntervalC, Y) :=
    ⟨fun x => ⟨openProfile x, mem_image_of_mem _ x.2⟩,
      (continuous_openProfile.comp continuous_subtype_val).subtype_mk _⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨_, z, hz, rfl⟩; exact ⟨⟨z, hz⟩, rfl⟩
  have hq := Topology.IsQuotientMap.of_surjective_continuous hsurj f.continuous
  let g' : C(unitIntervalC, ℂ) := ⟨fun x => g x, continuousOn_iff_continuous_restrict.mp hg⟩
  have hfac : Function.FactorsThrough g' f := by
    rintro ⟨_, t, ht, rfl⟩ ⟨_, u, hu, rfl⟩ hfu
    have hk : openProfile t = openProfile u := congrArg Subtype.val hfu
    change g t = g u
    rcases openProfile_eq_iff hk with htu | ⟨ht0, hu0⟩
    · rw [htu]
    · have key : ∀ v : ℝ, v * (1 - v) = 0 → g v = 0 := fun v hv => by
        rcases endpoint_of_mul_one_sub_eq_zero hv with rfl | rfl
        · simpa using hg0
        · simpa using hg1
      rw [key t ht0, key u hu0]
  let h₀ := hq.lift g' hfac
  have hcomp := hq.lift_comp g' hfac
  refine ⟨fun z => if hz : z ∈ Y then h₀ ⟨z, hz⟩ else 0, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    convert h₀.continuous using 1
    funext ⟨z, hz⟩
    simp [hz]
  · have h0Y : (0 : ℂ) ∈ Y := ⟨0, zero_mem_unitIntervalC, openProfile_zero⟩
    simp only [h0Y, dite_true]
    have := congrArg (fun F : C(unitIntervalC, ℂ) => F ⟨0, zero_mem_unitIntervalC⟩) hcomp
    simp only [ContinuousMap.comp_apply] at this
    change h₀ ⟨openProfile 0, _⟩ = _ at this
    convert this using 2
    · exact Subtype.ext openProfile_zero.symm
    · exact hg0.symm
  · intro z hz
    have hzY : openProfile z ∈ Y := mem_image_of_mem _ hz
    simp only [hzY, dite_true]
    have := congrArg (fun F : C(unitIntervalC, ℂ) => F ⟨z, hz⟩) hcomp
    simp only [ContinuousMap.comp_apply] at this
    exact this

/-! ## The open-history ideal is the suspension `C_0((0,1))` -/

section Suspension

variable (hinj : Function.Injective T) (hH : ¬ FiniteDimensional ℂ H)

include hinj hH in
/-- Every function of `e` vanishing at both endpoints lies in `J_T`. -/
theorem cfcₙ_mem_openHistoryIdeal {g : ℂ → ℂ} (hg : ContinuousOn g unitIntervalC) (hg0 : g 0 = 0)
    (hg1 : g 1 = 0) : cfcₙ g (unitGerm hT hcpt) ∈ openHistoryIdeal hT hcpt := by
  have hσ := quasispectrum_unitGerm hT hcpt hinj hH
  have hn := isStarNormal_unitGerm hT hcpt
  obtain ⟨h, hh, hh0, hhg⟩ := exists_factor_openProfile hg hg0 hg1
  have hcomp : cfcₙ g (unitGerm hT hcpt) = cfcₙ h (cfcₙ openProfile (unitGerm hT hcpt)) := by
    rw [← cfcₙ_comp h openProfile (unitGerm hT hcpt) (by rwa [hσ]) hh0
      (by rw [hσ]; exact continuous_openProfile.continuousOn) openProfile_zero]
    refine cfcₙ_congr fun z hz => ?_
    rw [hσ] at hz
    exact (hhg z hz).symm
  rw [hcomp]
  exact NonUnitalStarAlgebra.elemental.le_of_mem (isClosed_openHistoryIdeal hT hcpt)
    (cfcₙ_openProfile_mem hT hcpt hinj hH) (cfcₙ_mem_elemental _ _)

include hinj hH in
theorem one_mem_quasispectrum_unitGerm : (1 : ℂ) ∈ quasispectrum ℂ (unitGerm hT hcpt) := by
  rw [quasispectrum_unitGerm hT hcpt hinj hH]
  exact ⟨1, ⟨zero_le_one, le_rfl⟩, Complex.ofReal_one⟩

/-- The functions on `σ(e) = [0,1]` vanishing at the closed endpoint `1`: the suspension
`C_0((0,1))` inside the cone `C_0((0,1])`. -/
def endpointKernel {a : BoundaryCorona H} (h1 : (1 : ℂ) ∈ quasispectrum ℂ a) :
    NonUnitalStarSubalgebra ℂ C(quasispectrum ℂ a, ℂ)₀ where
  carrier := {g | g ⟨1, h1⟩ = 0}
  add_mem' {f g} hf hg := by simp only [Set.mem_setOf_eq] at hf hg ⊢; simp [hf, hg]
  zero_mem' := rfl
  mul_mem' {f g} hf hg := by simp only [Set.mem_setOf_eq] at hf hg ⊢; simp [hf]
  smul_mem' c f hf := by simp only [Set.mem_setOf_eq] at hf ⊢; simp [hf]
  star_mem' {f} hf := by simp only [Set.mem_setOf_eq] at hf ⊢; simp [hf]

theorem isClosed_endpointKernel {a : BoundaryCorona H} (h1 : (1 : ℂ) ∈ quasispectrum ℂ a) :
    IsClosed (endpointKernel h1 : Set C(quasispectrum ℂ a, ℂ)₀) :=
  isClosed_eq (continuous_eval_const _) continuous_const

include hinj hH in
/-- **(SAC.6)** The open-history ideal is the image of the suspension `C_0((0,1))` under the
functional calculus of `e`: `J_T = {g(e) : g(0) = g(1) = 0}`. -/
theorem openHistoryIdeal_eq_map :
    openHistoryIdeal hT hcpt = (endpointKernel (one_mem_quasispectrum_unitGerm hT hcpt hinj hH)).map
      (cfcₙHom (R := ℂ) (isStarNormal_unitGerm hT hcpt)) := by
  have hσ := quasispectrum_unitGerm hT hcpt hinj hH
  have hn := isStarNormal_unitGerm hT hcpt
  have h1 := one_mem_quasispectrum_unitGerm hT hcpt hinj hH
  apply le_antisymm
  · have hcl : IsClosed (((endpointKernel h1).map (cfcₙHom (R := ℂ) hn) :
        NonUnitalStarSubalgebra ℂ (BoundaryCorona H)) : Set (BoundaryCorona H)) := by
      rw [NonUnitalStarSubalgebra.coe_map]
      exact (cfcₙHom_isClosedEmbedding (R := ℂ) hn).isClosedMap _ (isClosed_endpointKernel h1)
    refine NonUnitalStarSubalgebra.topologicalClosure_minimal _
      (NonUnitalStarAlgebra.adjoin_le ?_) hcl
    rintro _ ⟨c, d, hc, hd, rfl⟩
    have hcc : ContinuousOn (scaleChange c) (quasispectrum ℂ (unitGerm hT hcpt)) := by
      rw [hσ]; exact continuousOn_scaleChange hc
    have hcd : ContinuousOn (scaleChange d) (quasispectrum ℂ (unitGerm hT hcpt)) := by
      rw [hσ]; exact continuousOn_scaleChange hd
    have h0c : scaleChange c 0 = 0 := by simp [scaleChange]
    have h0d : scaleChange d 0 = 0 := by simp [scaleChange]
    rw [scaleGerm_eq_cfcₙ hT hcpt hinj hH hc, scaleGerm_eq_cfcₙ hT hcpt hinj hH hd,
      ← cfcₙ_sub _ _ _ hcc h0c hcd h0d,
      cfcₙ_apply (fun x => scaleChange c x - scaleChange d x) _ (hcc.sub hcd)
        (by simp [h0c, h0d])]
    refine ⟨_, ?_, rfl⟩
    change scaleChange c 1 - scaleChange d 1 = 0
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    simp [scaleChange, div_self hc', div_self hd']
  · rintro _ ⟨g, hg, rfl⟩
    classical
    set g' : ℂ → ℂ := fun z => if hz : z ∈ quasispectrum ℂ (unitGerm hT hcpt) then g ⟨z, hz⟩ else 0
    have hg'c : ContinuousOn g' (quasispectrum ℂ (unitGerm hT hcpt)) := by
      rw [continuousOn_iff_continuous_restrict]
      convert (g : C(quasispectrum ℂ (unitGerm hT hcpt), ℂ)).continuous using 1
      funext ⟨z, hz⟩
      simp [g', hz]
    have hg'0 : g' 0 = 0 := by
      simp only [g', quasispectrum.zero_mem ℂ _, dite_true]
      exact g.map_zero'
    have hg'1 : g' 1 = 0 := by
      simp only [g', h1, dite_true]
      exact hg
    have hmem := cfcₙ_mem_openHistoryIdeal hT hcpt hinj hH (by rwa [← hσ]) hg'0 hg'1
    rw [cfcₙ_apply _ _ hg'c hg'0] at hmem
    have hgeq : (⟨⟨_, hg'c.restrict⟩, hg'0⟩ : C(quasispectrum ℂ (unitGerm hT hcpt), ℂ)₀) = g := by
      ext ⟨z, hz⟩
      simp [g']
    rw [hgeq] at hmem
    exact hmem

/-- The endpoint character `C*(e) ≅ C_0((0,1]) → ℂ`, evaluation at the closed aperture `1`. -/
def endpointChar {a : BoundaryCorona H} (h1 : (1 : ℂ) ∈ quasispectrum ℂ a) :
    C(quasispectrum ℂ a, ℂ)₀ →⋆ₙₐ[ℂ] ℂ where
  toFun g := g ⟨1, h1⟩
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

include hinj hH in
/-- **(SAC.7) The endpoint exact sequence** `0 → J_T → C*(e_1) → ℂ → 0`: under the isometric
functional calculus `C_0((0,1]) ≅ C*(e_1)`, the open-history ideal is the kernel of the endpoint
character, the character is onto, and every scale germ lifts the endpoint unit. -/
theorem endpoint_exact_sequence :
    let h1 := one_mem_quasispectrum_unitGerm hT hcpt hinj hH
    let hn := isStarNormal_unitGerm hT hcpt
    Isometry (cfcₙHom (R := ℂ) hn) ∧
      NonUnitalStarAlgHom.range (cfcₙHom (R := ℂ) hn) =
        NonUnitalStarAlgebra.elemental ℂ (unitGerm hT hcpt) ∧
      openHistoryIdeal hT hcpt = (endpointKernel h1).map (cfcₙHom (R := ℂ) hn) ∧
      (∀ g, g ∈ endpointKernel h1 ↔ endpointChar h1 g = 0) ∧
      Function.Surjective (endpointChar h1) ∧
      ∀ (c : ℝ) (hc : 0 < c), ∃ g, cfcₙHom (R := ℂ) hn g = scaleGerm T hT hcpt hc ∧
        endpointChar h1 g = 1 := by
  intro h1 hn
  have hσ := quasispectrum_unitGerm hT hcpt hinj hH
  refine ⟨isometry_cfcₙHom _ hn, range_cfcₙHom ℂ hn, openHistoryIdeal_eq_map hT hcpt hinj hH,
    fun g => Iff.rfl, fun z => ?_, fun c hc => ?_⟩
  · refine ⟨z • ⟨⟨(↑), continuous_subtype_val⟩, rfl⟩, ?_⟩
    change z * (1 : ℂ) = z
    rw [mul_one]
  · have hcc : ContinuousOn (scaleChange c) (quasispectrum ℂ (unitGerm hT hcpt)) := by
      rw [hσ]; exact continuousOn_scaleChange hc
    have h0 : scaleChange c 0 = 0 := by simp [scaleChange]
    refine ⟨_, (cfcₙ_apply (scaleChange c) _ hcc h0).symm.trans
      (scaleGerm_eq_cfcₙ hT hcpt hinj hH hc).symm, ?_⟩
    change scaleChange c 1 = 1
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    simp [scaleChange, div_self hc']

end Suspension

end GaloisForLFunctions.HTGeometry
