import GaloisForLFunctions.RHTower.FokasLenellsCausalPointSpectrum

/-! The exact complex resolvent norm is a supremum never attained on a nonzero actual datum. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
local instance : InnerProductSpace ℝ (hardyL2ᗮ) := InnerProductSpace.rclikeToReal ℂ (hardyL2ᗮ)

/-- Exact shifted-generator energy: real damping, imaginary-shift residual, and actual dissipation. -/
theorem causalComplexGeneratorShift_energy_decomposition (z : ℂ) (u : causalGeneratorDomain) :
    ‖causalComplexGeneratorShift z u‖^2 = z.re^2 * ‖u.val‖^2 +
      ‖causalGenerator u-((z.im : ℂ)*I) • u.val‖^2 -
      2*z.re*(inner ℂ u.val (causalGenerator u)).re := by
  have hz : (z.re : ℂ)+(z.im : ℂ)*I = z := by apply Complex.ext <;> simp
  have hscalar : (z.re : ℂ) • u.val + ((z.im : ℂ)*I) • u.val = z • u.val := by
    rw [← add_smul, hz]
  have hreal : z.re • u.val = (z.re : ℂ) • u.val := by
    change z.re • u.val = (algebraMap ℝ ℂ z.re) • u.val
    rw [algebraMap_smul]
  have hs : causalComplexGeneratorShift z u =
      z.re • u.val - (causalGenerator u-((z.im : ℂ)*I) • u.val) := by
    change z • u.val-causalGenerator u = _
    rw [← hscalar, hreal]
    module
  have him : inner ℝ u.val (((z.im : ℂ)*I) • u.val) = 0 := by
    change (inner ℂ u.val (((z.im : ℂ)*I) • u.val)).re = 0
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
    change (((z.im : ℂ)*I) * ((‖u.val‖ : ℝ) : ℂ)^2).re = 0
    rw [← Complex.ofReal_pow, Complex.mul_re]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero]

  have hi : inner ℝ u.val (causalGenerator u-((z.im : ℂ)*I) • u.val) =
      (inner ℂ u.val (causalGenerator u)).re := by
    rw [inner_sub_right, him, sub_zero]
    rfl
  have hm : inner ℝ (z.re • u.val)
      (causalGenerator u-((z.im : ℂ)*I) • u.val) =
      z.re * inner ℝ u.val (causalGenerator u-((z.im : ℂ)*I) • u.val) := by
    exact real_inner_smul_left _ _ _
  rw [hi] at hm
  rw [hs, norm_sub_sq_real, hm]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- Equality in right-half-plane generator coercivity is possible only at the zero domain vector. -/
theorem causalComplexGeneratorShift_norm_eq_iff (z : {z : ℂ // 0 < z.re})
    (u : causalGeneratorDomain) :
    ‖causalComplexGeneratorShift z.val u‖ = z.val.re * ‖u.val‖ ↔ u = 0 := by
  constructor
  · intro he
    have hd := causalComplexGeneratorShift_energy_decomposition z.val u
    rw [he, mul_pow] at hd
    have hdamp : 2*z.val.re*(inner ℂ u.val (causalGenerator u)).re ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) z.property.le) (causalGenerator_re_inner_nonpos u)
    have hn : ‖causalGenerator u-((z.val.im : ℂ)*I) • u.val‖ = 0 := by
      nlinarith only [hd, hdamp, norm_nonneg (causalGenerator u-((z.val.im : ℂ)*I) • u.val)]
    have hG := sub_eq_zero.mp (norm_eq_zero.mp hn)
    apply causalComplexGeneratorShift_imaginary_injective z.val.im
    rw [map_zero]
    change ((z.val.im : ℂ)*I) • u.val-causalGenerator u = 0
    rw [hG, sub_self]
  · intro he
    simp [he]

/-- No nonzero actual datum attains the sharp reciprocal-real-part complex resolvent bound. -/
theorem causalComplexResolvent_norm_eq_iff (z : {z : ℂ // 0 < z.re}) (u : hardyL2ᗮ) :
    ‖causalComplexResolvent z u‖ = z.val.re⁻¹ * ‖u‖ ↔ u = 0 := by
  constructor
  · intro he
    have hs : ‖causalComplexGeneratorShift z.val (causalComplexResolvent z u)‖ =
        z.val.re * ‖(causalComplexResolvent z u).val‖ := by
      rw [causalComplexGeneratorShift_resolvent]
      change ‖u‖ = z.val.re * ‖causalComplexResolvent z u‖
      rw [he, ← mul_assoc, mul_inv_cancel₀ z.property.ne', one_mul]
    have hz := (causalComplexGeneratorShift_norm_eq_iff z (causalComplexResolvent z u)).1 hs
    have h := congrArg (causalComplexGeneratorShift z.val) hz
    rw [causalComplexGeneratorShift_resolvent, map_zero] at h
    exact h
  · intro he
    simp [he]

/-- Every nonzero actual datum has a strict resolvent estimate, despite the sharp operator norm. -/
theorem causalComplexResolvent_norm_lt_iff (z : {z : ℂ // 0 < z.re}) (u : hardyL2ᗮ) :
    ‖causalComplexResolvent z u‖ < z.val.re⁻¹ * ‖u‖ ↔ u ≠ 0 := by
  constructor
  · intro h hu
    simp only [hu, map_zero, norm_zero, mul_zero, lt_self_iff_false] at h
  · intro hu
    exact lt_of_le_of_ne (causalComplexResolvent_norm_le z u)
      (fun he => hu ((causalComplexResolvent_norm_eq_iff z u).1 he))

/-- The complex construction agrees exactly with the original positive real Laplace resolvent. -/
theorem causalComplexResolvent_positive (a : ℝ) :
    causalComplexResolvent ⟨(Real.exp a : ℂ), Real.exp_pos a⟩ = causalResolvent a := by
  apply ContinuousLinearMap.ext
  intro u
  apply causalGeneratorShift_injective a
  have h := causalComplexGeneratorShift_resolvent ⟨(Real.exp a : ℂ), Real.exp_pos a⟩ u
  change causalGeneratorShift a
    (causalComplexResolvent ⟨(Real.exp a : ℂ), Real.exp_pos a⟩ u) = u at h
  rw [h, causalGeneratorShift_resolvent]

/-- The original positive real maximal-domain resolvent attains its sharp bound only at zero. -/
theorem causalResolvent_norm_eq_iff (a : ℝ) (u : hardyL2ᗮ) :
    ‖causalResolvent a u‖ = (Real.exp a)⁻¹ * ‖u‖ ↔ u = 0 := by
  have h := causalComplexResolvent_norm_eq_iff ⟨(Real.exp a : ℂ), Real.exp_pos a⟩ u
  rw [causalComplexResolvent_positive] at h
  exact h

/-- The literal positive Laplace integral has a sharp bound never attained by nonzero data. -/
theorem causalLaplaceIntegral_norm_eq_iff (a : ℝ) (u : hardyL2ᗮ) :
    ‖causalLaplaceIntegral a u‖ = (Real.exp a)⁻¹ * ‖u‖ ↔ u = 0 := by
  change ‖causalResolvent a u‖ = (Real.exp a)⁻¹ * ‖u‖ ↔ u = 0
  exact causalResolvent_norm_eq_iff a u

end
end RHTower.FokasLenells
