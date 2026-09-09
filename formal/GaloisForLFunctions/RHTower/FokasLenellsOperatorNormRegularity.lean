import GaloisForLFunctions.RHTower.FokasLenellsOperatorNormObstruction

/-!
# Exact operator-norm time differentiability of actual scattering multipliers

A bounded second symbol yields a uniform quadratic Taylor remainder.
The lower channel always has this bound. In the upper channel it holds
exactly at compatibility, and the origin obstruction proves necessity.
-/

open MeasureTheory Complex Matrix Filter Topology Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

private theorem first_symbol_lipschitz_of_second_bound (q : SchwartzMap ℝ ℂ) (reverse : Bool)
    (C : ℝ) (hC : ∀ t x z : ℝ, ‖directSecondTimeSymbol q t x reverse z‖ ≤ C) (t s x z : ℝ) :
    ‖directTimeSymbol q s x reverse z-directTimeSymbol q t x reverse z‖ ≤ C*‖s-t‖ := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ (univ : Set ℝ)) => (directTimeSymbol_time_hasDerivAt q r x reverse z).hasDerivWithinAt)
    (fun r _ => hC r x z) convex_univ (mem_univ t) (mem_univ s)
  exact hh

private theorem symbol_taylor_remainder (q : SchwartzMap ℝ ℂ) (reverse : Bool)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ t x z : ℝ, ‖directSecondTimeSymbol q t x reverse z‖ ≤ C) (t s x z : ℝ) :
    ‖directSymbol q s x reverse z-directSymbol q t x reverse z-(s-t) • directTimeSymbol q t x reverse z‖ ≤ C*‖s-t‖^2 := by
  have hd (r : ℝ) : HasDerivAt
      (fun u => directSymbol q u x reverse z-(u-t) • directTimeSymbol q t x reverse z)
      (directTimeSymbol q r x reverse z-directTimeSymbol q t x reverse z) r := by
    simpa only [one_smul,id_eq] using (directSymbol_time_hasDerivAt q r x reverse z).fun_sub
      (((hasDerivAt_id r).sub_const t).smul_const (directTimeSymbol q t x reverse z))
  have hb (r : ℝ) (hr : r ∈ segment ℝ t s) :
      ‖directTimeSymbol q r x reverse z-directTimeSymbol q t x reverse z‖ ≤ C*‖s-t‖ :=
    (first_symbol_lipschitz_of_second_bound q reverse C hC t r x z).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hr) hC0)
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ segment ℝ t s) => (hd r).hasDerivWithinAt) hb (convex_segment t s)
    (left_mem_segment ℝ t s) (right_mem_segment ℝ t s)
  have he : directSymbol q s x reverse z-directSymbol q t x reverse z-(s-t) • directTimeSymbol q t x reverse z =
      (directSymbol q s x reverse z-(s-t) • directTimeSymbol q t x reverse z)-directSymbol q t x reverse z := by abel
  rw [he]
  simpa only [sub_self,zero_smul,sub_zero,pow_two,mul_assoc] using hh

private theorem slope_error_symbol_bound (q : SchwartzMap ℝ ℂ) (reverse : Bool)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ t x z : ℝ, ‖directSecondTimeSymbol q t x reverse z‖ ≤ C)
    (t s x z : ℝ) (hst : s ≠ t) : ‖directTimeSlopeErrorSymbol q t s x reverse z‖ ≤ C*‖s-t‖ := by
  have hst0 : s-t ≠ 0 := sub_ne_zero.mpr hst
  have he : directTimeSlopeErrorSymbol q t s x reverse z =
      (s-t)⁻¹ • (directSymbol q s x reverse z-directSymbol q t x reverse z-(s-t) • directTimeSymbol q t x reverse z) := by
    simp only [directTimeSlopeErrorSymbol,smul_sub,smul_smul,inv_mul_cancel₀ hst0,one_smul]
  rw [he,norm_smul,norm_inv]
  calc
    _ ≤ ‖s-t‖⁻¹*(C*‖s-t‖^2) := mul_le_mul_of_nonneg_left
      (symbol_taylor_remainder q reverse C hC0 hC t s x z) (inv_nonneg.mpr (norm_nonneg _))
    _ = _ := by field_simp [norm_ne_zero_iff.mpr hst0]

private theorem operator_derivative_of_second_bound (q : SchwartzMap ℝ ℂ) (reverse : Bool)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ t x z : ℝ, ‖directSecondTimeSymbol q t x reverse z‖ ≤ C) (t x : ℝ) :
    HasDerivAt (fun s => directMultiplier q s x reverse) (directTimeMultiplier q t x reverse) t := by
  rw [hasDerivAt_iff_tendsto_slope]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    change s ≠ t at hs
    exact norm_le_of_ae_mul (mul_nonneg hC0 (norm_nonneg _))
      (fun z => slope_error_symbol_bound q reverse C hC0 hC t s x z hs)
      (directMultiplier_time_slope_error_ae q t s x reverse)
  · have hc : Continuous (fun s : ℝ => C*‖s-t‖) := continuous_const.mul (continuous_id.sub continuous_const).norm
    simpa only [sub_self,norm_zero,mul_zero] using (hc.tendsto t).mono_left nhdsWithin_le_nhds

private theorem operator_first_derivative_lipschitz (q : SchwartzMap ℝ ℂ) (reverse : Bool)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ t x z : ℝ, ‖directSecondTimeSymbol q t x reverse z‖ ≤ C) (t s x : ℝ) :
    ‖directTimeMultiplier q s x reverse-directTimeMultiplier q t x reverse‖ ≤ C*‖s-t‖ := by
  apply norm_le_of_ae_mul (ψ := fun z => directTimeSymbol q s x reverse z-directTimeSymbol q t x reverse z)
    (mul_nonneg hC0 (norm_nonneg _)) (first_symbol_lipschitz_of_second_bound q reverse C hC t s x)
  intro u
  filter_upwards [Lp.coeFn_sub (directTimeMultiplier q s x reverse u) (directTimeMultiplier q t x reverse u),
    directTimeMultiplier_ae q s x reverse u,directTimeMultiplier_ae q t x reverse u] with z h0 h1 h2
  change (directTimeMultiplier q s x reverse u-directTimeMultiplier q t x reverse u : SoninL2) z = _
  simp only [Pi.sub_apply] at h0
  rw [h0,h1,h2,sub_mul]

private theorem operator_contDiff_of_second_bound (q : SchwartzMap ℝ ℂ) (reverse : Bool)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ t x z : ℝ, ‖directSecondTimeSymbol q t x reverse z‖ ≤ C) (x : ℝ) :
    ContDiff ℝ 1 (fun s => directMultiplier q s x reverse) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (operator_derivative_of_second_bound q reverse C hC0 hC t x).differentiableAt,?_⟩
  have he : deriv (fun s => directMultiplier q s x reverse) = fun s => directTimeMultiplier q s x reverse :=
    funext fun t => (operator_derivative_of_second_bound q reverse C hC0 hC t x).deriv
  rw [he,continuous_iff_continuousAt]
  intro t
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun s => norm_nonneg _) (fun s => operator_first_derivative_lipschitz q reverse C hC0 hC t s x)
  have hc : Continuous (fun s : ℝ => C*‖s-t‖) := continuous_const.mul (continuous_id.sub continuous_const).norm
  simpa only [sub_self,norm_zero,mul_zero] using hc.tendsto t

private theorem uniform_second_bound_from_reflection (q : SchwartzMap ℝ ℂ) (reverse : Bool)
    (C : ℝ) (hC : ∀ z : ℝ, ‖regularSecondInverseReflection (globalSmallScatteringPotential q) reverse z‖ ≤ C) :
    ∀ t x z : ℝ, ‖directSecondTimeSymbol q t x reverse z‖ ≤ (1/4 : ℝ)*C := by
  intro t x z
  rw [directSecondTimeSymbol_norm]
  exact mul_le_mul_of_nonneg_left (hC z) (by positivity)

private theorem operator_derivative_unique_candidate (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool)
    (V : SoninL2 →L[ℂ] SoninL2) (hV : HasDerivAt (fun s => directMultiplier q s x reverse) V t) :
    V = directTimeMultiplier q t x reverse := by
  apply ContinuousLinearMap.ext
  intro u
  have h := ((ContinuousLinearMap.apply ℂ SoninL2 u).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hV
  exact h.unique (directMultiplier_time_hasDerivAt q t x reverse u)

private theorem upper_operator_derivative_requires_compatibility (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (V : SoninL2 →L[ℂ] SoninL2) (hV : HasDerivAt (fun s => directMultiplier q s x true) V t) :
    compatibilityMoment (globalSmallScatteringPotential q) = 0 := by
  have hv := operator_derivative_unique_candidate q t x true V hV
  rw [hv] at hV
  have hlim := (hV.tendsto_slope.sub_const (directTimeMultiplier q t x true)).norm
  simp only [sub_self,norm_zero] at hlim
  have hle : (1/2 : ℝ)*‖compatibilityMoment (globalSmallScatteringPotential q)‖ ≤ 0 :=
    ge_of_tendsto hlim (Eventually.of_forall fun s => directMultiplier_upper_time_slope_error_lower_bound q t s x)
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (compatibilityMoment (globalSmallScatteringPotential q))]

/-- The lower actual multiplier has an operator-norm time derivative for every constructed small Schwartz profile. -/
theorem directMultiplier_lower_operator_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    HasDerivAt (fun s => directMultiplier q s x false) (directTimeMultiplier q t x false) t := by
  obtain ⟨C,hC0,hC⟩ := regularSecondInverseReflection_lower_globalSmall_bounded q
  exact operator_derivative_of_second_bound q false ((1/4 : ℝ)*C) (mul_nonneg (by positivity) hC0)
    (uniform_second_bound_from_reflection q false C hC) t x

/-- The upper actual multiplier has its operator-norm time derivative exactly at nonlinear compatibility. -/
theorem directMultiplier_upper_operator_hasDerivAt_iff (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    HasDerivAt (fun s => directMultiplier q s x true) (directTimeMultiplier q t x true) t ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 := by
  constructor
  · exact upper_operator_derivative_requires_compatibility q t x _
  · intro hm
    obtain ⟨C,hC0,hC⟩ := (regularSecondInverseReflection_upper_globalSmall_bounded_iff q).2 hm
    exact operator_derivative_of_second_bound q true ((1/4 : ℝ)*C) (mul_nonneg (by positivity) hC0)
      (uniform_second_bound_from_reflection q true C hC) t x

/-- Existence of any upper operator-norm derivative has the same exact compatibility criterion. -/
theorem directMultiplier_upper_operator_differentiableAt_iff (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    DifferentiableAt ℝ (fun s => directMultiplier q s x true) t ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 := by
  constructor
  · intro h
    exact upper_operator_derivative_requires_compatibility q t x _ h.hasDerivAt
  · intro hm
    exact ((directMultiplier_upper_operator_hasDerivAt_iff q t x).2 hm).differentiableAt

/-- The lower scattering multiplier is globally C1 in the operator norm without a compatibility condition. -/
theorem directMultiplier_lower_operator_contDiff (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    ContDiff ℝ 1 (fun t => directMultiplier q t x false) := by
  obtain ⟨C,hC0,hC⟩ := regularSecondInverseReflection_lower_globalSmall_bounded q
  exact operator_contDiff_of_second_bound q false ((1/4 : ℝ)*C) (mul_nonneg (by positivity) hC0)
    (uniform_second_bound_from_reflection q false C hC) x

/-- Global upper C1 operator-norm regularity holds exactly on the full nonlinear compatibility locus. -/
theorem directMultiplier_upper_operator_contDiff_iff (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    ContDiff ℝ 1 (fun t => directMultiplier q t x true) ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 := by
  constructor
  · intro h
    exact (directMultiplier_upper_operator_differentiableAt_iff q 0 x).1 ((h.differentiable (by simp)) 0)
  · intro hm
    obtain ⟨C,hC0,hC⟩ := (regularSecondInverseReflection_upper_globalSmall_bounded_iff q).2 hm
    exact operator_contDiff_of_second_bound q true ((1/4 : ℝ)*C) (mul_nonneg (by positivity) hC0)
      (uniform_second_bound_from_reflection q true C hC) x

/-- The same actual Gaussian operator orbit is strongly differentiable on every vector and nowhere differentiable in operator norm. -/
theorem directMultiplier_Gaussian_strong_not_operator_derivative (a t x : ℝ) :
    (∀ u : SoninL2, HasDerivAt (fun s => directMultiplier (compatibilityGaussian a) s x true u)
      (directTimeMultiplier (compatibilityGaussian a) t x true u) t) ∧
    ¬ DifferentiableAt ℝ (fun s => directMultiplier (compatibilityGaussian a) s x true) t := by
  refine ⟨fun u => directMultiplier_time_hasDerivAt _ t x true u,?_⟩
  rw [directMultiplier_upper_operator_differentiableAt_iff]
  exact compatibilityMoment_globalSmallGaussian_ne_zero a

/-- Both operator derivatives exist on the entire internally compatible odd Schwartz subspace. -/
theorem directMultiplier_oddInitialPart_operator_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    HasDerivAt (fun s => directMultiplier (oddInitialPart q) s x reverse)
      (directTimeMultiplier (oddInitialPart q) t x reverse) t := by
  cases reverse
  · exact directMultiplier_lower_operator_hasDerivAt _ t x
  · exact (directMultiplier_upper_operator_hasDerivAt_iff _ t x).2 (compatibilityMoment_globalSmall_oddInitialPart q)

theorem directMultiplier_oddInitialPart_operator_contDiff (q : SchwartzMap ℝ ℂ) (x : ℝ) (reverse : Bool) :
    ContDiff ℝ 1 (fun t => directMultiplier (oddInitialPart q) t x reverse) := by
  cases reverse
  · exact directMultiplier_lower_operator_contDiff _ x
  · exact (directMultiplier_upper_operator_contDiff_iff _ x).2 (compatibilityMoment_globalSmall_oddInitialPart q)

end
end RHTower.FokasLenells
