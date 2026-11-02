import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.CoreHeckeResidual

/-!
# Exact interference in the compact-core Hecke residual

The residual square separates into the masses of the direct and returning Weyl
terms and their single oscillatory cross term. Maass–Selberg cancels the common
scattering coefficient in the normalized square.
-/

open Complex MeasureTheory Set UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

noncomputable section

private theorem real_cpow_re {r : ℝ} (hr : 0 < r) (w : ℂ) :
    ((r : ℂ) ^ w).re = r ^ w.re * Real.cos (w.im * Real.log r) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    ← Complex.ofReal_log hr.le, Complex.exp_re, Real.rpow_def_of_pos hr]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero]
  rw [mul_comm (Real.log r) w.im]

private theorem scalar_gap_norm_sq {r : ℝ} (hr : 0 < r) (u : ℂ) :
    ‖2 * (r : ℂ) ^ (u - 1 / 2) - 1‖ ^ 2 =
      (2 * r ^ (u.re - 1 / 2)) ^ 2 + 1 -
        4 * r ^ (u.re - 1 / 2) * Real.cos (u.im * Real.log r) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_one,
    map_one, mul_one, Complex.normSq_eq_norm_sq, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hr]
  have hre := real_cpow_re hr (u - 1 / 2)
  have hwre : (u - 1 / 2 : ℂ).re = u.re - 1 / 2 := by simp
  have hwim : (u - 1 / 2 : ℂ).im = u.im := by simp
  simp only [hwre, hwim] at hre ⊢
  norm_num [Complex.mul_re, hre]
  <;> ring

/-- Exact square of the full automorphic residual, with its unique interference phase. -/
theorem dyadicEigenResidual_norm_sq_expansion {u : ℂ} (hAu : msA u = 0)
    {z : ℍ} (hz : z ∈ coreRectangle) :
    ‖dyadicEigenResidual u z‖ ^ 2 =
      ‖msB u‖ ^ 2 / 2 * (returnHeight 0 z ^ (1 / 2 - u.re)) ^ 2 *
        ((2 * returnRatio z ^ (u.re - 1 / 2)) ^ 2 + 1 -
          4 * returnRatio z ^ (u.re - 1 / 2) * Real.cos (u.im * Real.log (returnRatio z))) := by
  rw [dyadicEigenResidual_factor hAu hz, norm_mul, mul_pow,
    dyadicReturnDefect_norm_sq_on_core hAu hz, scalar_gap_norm_sq (returnRatio_pos z)]

/-- The surviving Weyl coefficient is nonzero throughout the resonant half-strip. -/
theorem msB_ne_zero_of_negative_re {u : ℂ} (hu : u ∈ eisensteinLineDomain)
    (hur : u.re < 0) : msB u ≠ 0 := by
  have hr : (1 + 2 * u : ℂ).re < 1 := by simp; linarith
  have hi : (1 + 2 * u : ℂ).im ≠ 0 := by simp; linarith [hu.2]
  have hn := reflectedCompletedLambda_sub_one_ne_zero hr hi
  simpa only [show (1 + 2 * u : ℂ) - 1 = 2 * u by ring, msB] using hn

/-- The norm-normalized source square depends only on the resonance parameter and geometry. -/
theorem dyadicEigenResidual_normalized_expansion {u : ℂ}
    (hu : u ∈ eisensteinLineDomain) (hur : u.re < 0) (hAu : msA u = 0)
    {z : ℍ} (hz : z ∈ coreRectangle) :
    ‖dyadicEigenResidual u z‖ ^ 2 / (∫ w in fd, ‖truncatedLineModel u 1 w‖ ^ 2) =
      (-2 * u.re) / 2 * (returnHeight 0 z ^ (1 / 2 - u.re)) ^ 2 *
        ((2 * returnRatio z ^ (u.re - 1 / 2)) ^ 2 + 1 -
          4 * returnRatio z ^ (u.re - 1 / 2) * Real.cos (u.im * Real.log (returnRatio z))) := by
  rw [dyadicEigenResidual_norm_sq_expansion hAu hz,
    integral_norm_sq_of_msA_eq_zero hu hur hAu (by norm_num)]
  simp only [Real.one_rpow, mul_one]
  have hB : ‖msB u‖ ≠ 0 := norm_ne_zero_iff.mpr (msB_ne_zero_of_negative_re hu hur)
  field_simp [hB]

end

end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates
