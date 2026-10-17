import GaloisForLFunctions.HTGeometry.TiltedTentTwoFlankSurplus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Causal exponential tent densities and their exact moments. -/

open MeasureTheory Set
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

def causalTent (δ x : ℝ) : ℝ := max 0 (min x (2*δ-x))

theorem continuous_causalTent (δ : ℝ) : Continuous (causalTent δ) := by
  unfold causalTent
  fun_prop

theorem causalTent_nonneg (δ x : ℝ) : 0 ≤ causalTent δ x := le_max_left _ _

theorem causalTent_le {δ : ℝ} (hδ : 0 ≤ δ) (x : ℝ) : causalTent δ x ≤ δ := by
  unfold causalTent
  apply max_le hδ
  by_cases hx : x ≤ δ
  · exact (min_le_left _ _).trans hx
  · exact (min_le_right _ _).trans (by linarith)

theorem causalTent_zero_left (δ : ℝ) {x : ℝ} (hx : x ≤ 0) : causalTent δ x = 0 := by
  exact max_eq_left ((min_le_left _ _).trans hx)

theorem causalTent_zero_right (δ : ℝ) {x : ℝ} (hx : 2*δ ≤ x) : causalTent δ x = 0 := by
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

theorem causalTent_left {δ x : ℝ} (hx : x ∈ Icc 0 δ) : causalTent δ x = x := by
  rw [causalTent, min_eq_left (by linarith [hx.2]), max_eq_right hx.1]

theorem causalTent_right {δ x : ℝ} (hx : x ∈ Icc δ (2*δ)) : causalTent δ x = 2*δ-x := by
  rw [causalTent, min_eq_right (by linarith [hx.1]), max_eq_right (by linarith [hx.2])]

theorem hasCompactSupport_causalTent (δ : ℝ) : HasCompactSupport (causalTent δ) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Icc 0 (2*δ)) isCompact_Icc
  intro x hx
  constructor
  · by_contra! h
    exact hx (causalTent_zero_left δ h.le)
  · by_contra! h
    exact hx (causalTent_zero_right δ h.le)

/-- The causal tent moment is the translated bilateral tent transform. -/
theorem integral_exp_causalTent {δ a : ℝ} (hδ : 0 ≤ δ) (ha : a ≠ 0) :
    (∫ x in Icc 0 (2*δ), Real.exp (a*x)*causalTent δ x) =
      ((Real.exp (a*δ)-1)/a)^2 := by
  rcases hδ.eq_or_lt with hδ0 | hδ
  · subst δ
    simp
  have ht (x : ℝ) (hx : x ∈ Icc (-δ) δ) : causalTent δ (x+δ) = δ-|x| := by
    by_cases h : x ≤ 0
    · rw [causalTent_left ⟨by linarith [hx.1], by linarith⟩, abs_of_nonpos h]
      ring
    · rw [causalTent_right ⟨by linarith, by linarith [hx.2]⟩, abs_of_nonneg (by linarith : 0 ≤ x)]
      ring
  have hs : (∫ x in -δ..δ, Real.exp (a*(x+δ))*causalTent δ (x+δ)) =
      ∫ x in (0 : ℝ)..2*δ, Real.exp (a*x)*causalTent δ x := by
    simpa only [neg_add_cancel, show δ+δ = 2*δ by ring] using
      (intervalIntegral.integral_comp_add_right (fun x => Real.exp (a*x)*causalTent δ x) δ
        (a := -δ) (b := δ))
  have heq : (∫ x in -δ..δ, Real.exp (a*(x+δ))*causalTent δ (x+δ)) =
      ∫ x in -δ..δ, (Real.exp (a*δ)*δ)*GaloisForLFunctions.HTGeometry.tiltedTentFullProfile a δ x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith : -δ ≤ δ)] at hx
    dsimp only
    rw [ht x hx, show a*(x+δ) = a*δ+a*x by ring, Real.exp_add]
    unfold GaloisForLFunctions.HTGeometry.tiltedTentFullProfile
    field_simp
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : 0 ≤ 2*δ),
    ← hs, heq, intervalIntegral.integral_const_mul,
    GaloisForLFunctions.HTGeometry.integral_tiltedTentFullProfile ha hδ, Real.cosh_eq]
  have hh : Real.exp (a*δ)*Real.exp (-(a*δ)) = 1 := by
    rw [← Real.exp_add]
    simp
  field_simp
  nlinarith

/-- A probability density on the causal collar. -/
def exponentialTentDensity (δ x : ℝ) : ℝ :=
  Real.exp x * causalTent δ x / (Real.exp δ-1)^2

def exponentialTentSource (δ x : ℝ) : ℝ := Real.exp (x/2)*exponentialTentDensity δ x

theorem continuous_exponentialTentDensity (δ : ℝ) : Continuous (exponentialTentDensity δ) :=
  (Real.continuous_exp.mul (continuous_causalTent δ)).div_const _

theorem continuous_exponentialTentSource (δ : ℝ) : Continuous (exponentialTentSource δ) :=
  (Real.continuous_exp.comp (continuous_id.div_const 2)).mul (continuous_exponentialTentDensity δ)

theorem exponentialTentDensity_nonneg (δ x : ℝ) : 0 ≤ exponentialTentDensity δ x :=
  div_nonneg (mul_nonneg (Real.exp_pos x).le (causalTent_nonneg δ x)) (sq_nonneg _)

theorem exponentialTentDensity_zero_of_not_mem (δ : ℝ) {x : ℝ}
    (hx : x ∉ Icc 0 (2*δ)) : exponentialTentDensity δ x = 0 := by
  have ht : causalTent δ x = 0 := by
    by_cases h0 : 0 ≤ x
    · apply causalTent_zero_right δ
      by_contra! hh
      exact hx ⟨h0, hh.le⟩
    · exact causalTent_zero_left δ (by linarith)
  simp [exponentialTentDensity, ht]

theorem hasCompactSupport_exponentialTentDensity (δ : ℝ) :
    HasCompactSupport (exponentialTentDensity δ) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Icc 0 (2*δ)) isCompact_Icc
  intro x hx
  by_contra hn
  exact hx (exponentialTentDensity_zero_of_not_mem δ hn)

theorem hasCompactSupport_exponentialTentSource (δ : ℝ) :
    HasCompactSupport (exponentialTentSource δ) :=
  (hasCompactSupport_exponentialTentDensity δ).mul_left

theorem integral_Icc_exponentialTentDensity {δ : ℝ} (hδ : 0 < δ) :
    (∫ x in Icc 0 (2*δ), exponentialTentDensity δ x) = 1 := by
  have he : Real.exp δ-1 ≠ 0 := by have := Real.exp_lt_exp.mpr hδ; simp only [Real.exp_zero] at this; linarith
  unfold exponentialTentDensity
  rw [integral_div]
  have hm := integral_exp_causalTent (a := 1) hδ.le (by norm_num)
  simp only [one_mul, div_one] at hm
  rw [hm]
  field_simp

theorem integral_exp_exponentialTentDensity {δ : ℝ} (hδ : 0 < δ) :
    (∫ x in Icc 0 (2*δ), Real.exp x*exponentialTentDensity δ x) =
      ((Real.exp δ+1)/2)^2 := by
  have he : Real.exp δ-1 ≠ 0 := by have := Real.exp_lt_exp.mpr hδ; simp only [Real.exp_zero] at this; linarith
  have hf : (fun x => Real.exp x*exponentialTentDensity δ x) =
      fun x => Real.exp (2*x)*causalTent δ x/(Real.exp δ-1)^2 := by
    funext x
    unfold exponentialTentDensity
    rw [show 2*x = x+x by ring, Real.exp_add]
    ring
  rw [hf, integral_div, integral_exp_causalTent hδ.le (by norm_num : (2 : ℝ) ≠ 0)]
  rw [show 2*δ = δ+δ by ring, Real.exp_add]
  field_simp
  ring

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
