import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-!
# Three phase samples detect logarithmic-chirp nonstationarity

A nonzero complex amplitude cannot have the same real part at three
successive rotations by a nonreal unit. The logarithmic-chirp rotation
at the prime two lies strictly between zero and pi, so this obstruction
requires no irrationality statement about logarithms and pi.
-/

noncomputable section
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Three equal real parts along a nonreal unit rotation force the amplitude to vanish. -/
theorem complex_three_rotation_rigidity (A w : ℂ) (hw : ‖w‖ = 1) (hwi : w.im ≠ 0)
    (h01 : A.re = (A * w).re) (h12 : (A * w).re = (A * w * w).re) : A = 0 := by
  have hnorm : w.re * w.re + w.im * w.im = 1 := by
    simpa only [Complex.normSq_apply, hw, one_pow] using (Complex.sq_norm w).symm
  have hwr : w.re ≠ 1 := by
    intro he
    rw [he] at hnorm
    have hi : 0 < w.im * w.im := mul_self_pos.mpr hwi
    nlinarith only [hnorm, hi]
  have hrec : (A * w * w).re + A.re = 2 * w.re * (A * w).re := by
    have he := congrArg (fun x : ℝ => A.re * x) hnorm
    simp only [Complex.mul_re, Complex.mul_im]
    nlinarith only [he]
  rw [← h12, ← h01] at hrec
  have hrprod : A.re * (w.re - 1) = 0 := by nlinarith only [hrec]
  have hr : A.re = 0 := (mul_eq_zero.mp hrprod).resolve_right (sub_ne_zero.mpr hwr)
  have hiprod : A.im * w.im = 0 := by
    simp only [Complex.mul_re, hr, zero_mul, zero_sub] at h01
    exact neg_eq_zero.mp h01.symm
  have hi : A.im = 0 := (mul_eq_zero.mp hiprod).resolve_right hwi
  apply Complex.ext
  · exact hr
  · exact hi

/-- Every rotation strictly between zero and pi detects a nonzero amplitude in three samples. -/
theorem complex_three_rotation_not_constant (A : ℂ) (hA : A ≠ 0)
    (θ : ℝ) (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    ¬(A.re = (A * Complex.exp ((θ : ℂ) * Complex.I)).re ∧
      (A * Complex.exp ((θ : ℂ) * Complex.I)).re =
        (A * Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I)).re) := by
  rintro ⟨h01, h12⟩
  apply hA
  apply complex_three_rotation_rigidity A (Complex.exp ((θ : ℂ) * Complex.I)) _ _ h01 h12
  · rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, Real.exp_zero]
  · have hi : (Complex.exp ((θ : ℂ) * Complex.I)).im = Real.sin θ := by
      simp only [Complex.exp_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
        mul_one, add_zero, Real.exp_zero, one_mul]
    rw [hi]
    exact (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ).ne'

/-- The exact prime-two chirp increment is a nondegenerate angle below pi. -/
theorem logarithmicChirp_two_angle :
    0 < 2 * Real.log 2 ^ 2 ∧ 2 * Real.log 2 ^ 2 < Real.pi := by
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hle : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hs : Real.log 2 ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hp.le hle 2
  exact ⟨mul_pos (by norm_num) (sq_pos_of_pos hp), by linarith only [hs, Real.pi_gt_three]⟩

/-- The prime-two logarithmic-chirp rotation cannot preserve three nonzero real samples. -/
theorem logarithmicChirp_two_rotation_not_constant (A : ℂ) (hA : A ≠ 0) :
    ¬(A.re = (A * Complex.exp (((2 * Real.log 2 ^ 2 : ℝ) : ℂ) * Complex.I)).re ∧
      (A * Complex.exp (((2 * Real.log 2 ^ 2 : ℝ) : ℂ) * Complex.I)).re =
        (A * Complex.exp (((2 * Real.log 2 ^ 2 : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((2 * Real.log 2 ^ 2 : ℝ) : ℂ) * Complex.I)).re) :=
  complex_three_rotation_not_constant A hA _ logarithmicChirp_two_angle.1
    logarithmicChirp_two_angle.2

end GaloisForLFunctions.BiarithmeticGeometry

