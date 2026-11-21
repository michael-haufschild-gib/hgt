import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! The variation of a complex power along a positive real interval. -/

open Complex

namespace QH

theorem norm_cpow_increment_le {ρ : ℂ} (hρ : ρ ≠ 0) {z h σ : ℝ}
    (hz : 1 ≤ z) (hh : 0 ≤ h) (hσ : σ ≤ 1) (hre : ρ.re ≤ σ) :
    ‖((z + h : ℝ) : ℂ) ^ ρ - (z : ℂ) ^ ρ‖ ≤ ‖ρ‖ * z ^ (σ - 1) * h := by
  have hz₀ : 0 < z := zero_lt_one.trans_le hz
  have hz₁ : z ≤ z + h := le_add_of_nonneg_right hh
  have hder (u : ℝ) (hu : u ∈ Set.Icc z (z + h)) :
      HasDerivWithinAt (fun u : ℝ => (u : ℂ) ^ ρ) (ρ * (u : ℂ) ^ (ρ - 1)) (Set.Icc z (z + h)) u :=
    (hasDerivAt_ofReal_cpow_const (hz₀.trans_le hu.1).ne' hρ).hasDerivWithinAt
  have hbound (u : ℝ) (hu : u ∈ Set.Icc z (z + h)) :
      ‖ρ * (u : ℂ) ^ (ρ - 1)‖ ≤ ‖ρ‖ * z ^ (σ - 1) := by
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (hz₀.trans_le hu.1), sub_re, one_re]
    exact mul_le_mul_of_nonneg_left
      ((Real.rpow_le_rpow_of_exponent_le (hz.trans hu.1) (sub_le_sub_right hre 1)).trans
        (Real.rpow_le_rpow_of_nonpos hz₀ hu.1 (sub_nonpos.mpr hσ))) (norm_nonneg _)
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound
    (convex_Icc z (z + h)) (Set.left_mem_Icc.mpr hz₁) (Set.right_mem_Icc.mpr hz₁)
  simpa only [add_sub_cancel_left, Real.norm_of_nonneg hh] using hm

end QH
