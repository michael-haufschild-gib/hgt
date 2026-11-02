import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.AutomorphicHeckeReturn
import GaloisForLFunctions.RHTower.EisensteinResonantStateNorm

/-!
# A fixed core region with a single dyadic return

On `|x|≤1/4`, `7/4≤y≤15/8`, only the central return disk contributes.
Its modulus therefore cannot be reduced by interference between return phases.
-/

open Complex MeasureTheory Set UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

noncomputable section

/-- A fixed rectangle in the interior of the modular fundamental domain. -/
def coreRectangle : Set ℍ := {z | |z.re| ≤ 1 / 4 ∧ 7 / 4 ≤ z.im ∧ z.im ≤ 15 / 8}

theorem coreRectangle_subset_fd : coreRectangle ⊆ fd := by
  intro z hz
  have hx := abs_le.mp hz.1
  refine ⟨?_, by change |z.re| ≤ 1 / 2; linarith [hz.1]⟩
  rw [Complex.normSq_apply]
  change 1 ≤ z.re * z.re + z.im * z.im
  nlinarith [hz.2.1, sq_nonneg z.re]

/-- Exactly the central disk returns on the core rectangle. -/
theorem coreRectangle_returns {z : ℍ} (hz : z ∈ coreRectangle) :
    1 < returnHeight 0 z ∧ returnHeight 1 z ≤ 1 ∧ returnHeight (-1) z ≤ 1 := by
  have hx := abs_le.mp hz.1
  have hylo := hz.2.1
  have hyhi := hz.2.2
  have hx2 : z.re ^ 2 ≤ 1 / 16 := by nlinarith
  have hy2 : (z.im - 1) ^ 2 ≤ 49 / 64 := by nlinarith
  have hy2lo : 9 / 16 ≤ (z.im - 1) ^ 2 := by nlinarith
  refine ⟨(returnHeight_gt_one_iff 0 z).mpr ?_, ?_, ?_⟩
  · norm_num only [Int.cast_zero, add_zero]
    linarith
  · apply le_of_not_gt
    rw [returnHeight_gt_one_iff]
    norm_num only [Int.cast_one]
    nlinarith
  · apply le_of_not_gt
    rw [returnHeight_gt_one_iff]
    norm_num only [Int.cast_neg, Int.cast_one]
    nlinarith

/-- Difference between coordinate and automorphic Hecke truncation at height one. -/
def dyadicReturnDefect (u : ℂ) (z : ℍ) : ℂ :=
  heckeTruncated 2 u 1 z - dyadicHecke (automorphicTruncation u 1) z

theorem dyadicReturnDefect_on_core {u : ℂ} (hAu : msA u = 0)
    {z : ℍ} (hz : z ∈ coreRectangle) :
    dyadicReturnDefect u z = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * msB u *
      (returnHeight 0 z : ℂ) ^ (1 / 2 - u) := by
  obtain ⟨h0, h1, hm⟩ := coreRectangle_returns hz
  rw [dyadicReturnDefect, resonant_automorphic_dyadic_correction hAu
    (coreRectangle_subset_fd hz), if_pos h0, if_neg (not_lt.mpr h1),
    if_neg (not_lt.mpr hm)]
  ring

/-- The local return has a fixed positive squared modulus, independent of frequency. -/
theorem dyadicReturnDefect_norm_sq_lower {u : ℂ} (hur : u.re < 0)
    (hAu : msA u = 0) {z : ℍ} (hz : z ∈ coreRectangle) :
    ‖msB u‖ ^ 2 / 2 ≤ ‖dyadicReturnDefect u z‖ ^ 2 := by
  have h0 := (coreRectangle_returns hz).1
  have hn : ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ)‖ ^ 2 = 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [dyadicReturnDefect_on_core hAu hz]
  simp only [norm_mul, mul_pow, hn,
    Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans h0)]
  have hp : 1 ≤ (returnHeight 0 z) ^ ((1 / 2 - u : ℂ).re) :=
    Real.one_le_rpow h0.le (by simp; linarith)
  have hps : 1 ≤ ((returnHeight 0 z) ^ ((1 / 2 - u : ℂ).re)) ^ 2 := by
    nlinarith only [hp]
  nlinarith only [mul_nonneg (sq_nonneg ‖msB u‖) (sub_nonneg.mpr hps)]

end

end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates
