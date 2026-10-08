import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.Trigonometric

/-!
# The positive two-term polynomial weight

The critical-line weight is a squared norm. Its expansion in the exact
scaled-contour normalization includes both scale two and scale one-half.
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace RHTower.WeilSingularArithmetic

def sourceTwoPointFactor (c : ℝ) (s : ℂ) : ℂ :=
  1 - c * Complex.exp (-(Real.log 2 : ℂ) * s)

def sourceTwoPointWeight (c : ℝ) (s : ℂ) : ℂ :=
  sourceTwoPointFactor c s * sourceTwoPointFactor c (1 - s)

theorem differentiable_sourceTwoPointWeight (c : ℝ) :
    Differentiable ℂ (sourceTwoPointWeight c) := by
  unfold sourceTwoPointWeight sourceTwoPointFactor
  fun_prop

theorem sourceTwoPointFactor_conj (c : ℝ) (s : ℂ) :
    sourceTwoPointFactor c (conj s) = conj (sourceTwoPointFactor c s) := by
  simp only [sourceTwoPointFactor, map_sub, map_one, map_mul, map_neg,
    conj_ofReal, ← Complex.exp_conj]

theorem sourceTwoPointWeight_conj (c : ℝ) (s : ℂ) :
    sourceTwoPointWeight c (conj s) = conj (sourceTwoPointWeight c s) := by
  simp only [sourceTwoPointWeight, map_mul, ← sourceTwoPointFactor_conj]
  congr 1
  simp

theorem sourceTwoPointWeight_one_sub (c : ℝ) (s : ℂ) :
    sourceTwoPointWeight c (1 - s) = sourceTwoPointWeight c s := by
  simp only [sourceTwoPointWeight, sub_sub_cancel]
  ring

theorem sourceTwoPointWeight_critical (c t : ℝ) :
    sourceTwoPointWeight c ((1 / 2 : ℂ) + t * I) =
      ((‖sourceTwoPointFactor c ((1 / 2 : ℂ) + t * I)‖ ^ 2 : ℝ) : ℂ) := by
  unfold sourceTwoPointWeight
  rw [show 1 - ((1 / 2 : ℂ) + t * I) = conj ((1 / 2 : ℂ) + t * I) by
    simp only [map_add, map_div₀, map_ofNat, map_one, map_mul, conj_ofReal, conj_I]; ring,
    sourceTwoPointFactor_conj, Complex.mul_conj']
  norm_cast

private theorem norm_sourceTwoPointFactor_le (c : ℝ) {s : ℂ} (hs : -(1 / 2) ≤ s.re) :
    ‖sourceTwoPointFactor c s‖ ≤ 1 + |c| * Real.exp (2 * Real.log 2) := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have he : ‖Complex.exp (-(Real.log 2 : ℂ) * s)‖ ≤ Real.exp (2 * Real.log 2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
    nlinarith
  unfold sourceTwoPointFactor
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖(c : ℂ) * Complex.exp (-(Real.log 2 : ℂ) * s)‖ := norm_sub_le _ _
    _ = 1 + |c| * ‖Complex.exp (-(Real.log 2 : ℂ) * s)‖ := by
      rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ _ := by gcongr

theorem exists_sourceTwoPointWeight_strip_bound (c : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 2 →
      ‖sourceTwoPointWeight c s‖ ≤ B := by
  refine ⟨(1 + |c| * Real.exp (2 * Real.log 2)) ^ 2, sq_nonneg _, fun s hs0 hs1 => ?_⟩
  unfold sourceTwoPointWeight
  rw [norm_mul, pow_two]
  exact mul_le_mul (norm_sourceTwoPointFactor_le c (by linarith))
    (norm_sourceTwoPointFactor_le c (by simp only [Complex.sub_re, Complex.one_re]; linarith))
    (norm_nonneg _) (by positivity)

/-- Expansion in the literal normalization of the scaled arithmetic contour. -/
theorem sourceTwoPointWeight_expansion (c : ℝ) (s : ℂ) :
    sourceTwoPointWeight c s = 1 + (c : ℂ) ^ 2 / 2 -
      ((c : ℂ) / 2) * (2 : ℂ) ^ (1 - s) - (c : ℂ) * (1 / 2 : ℂ) ^ (1 - s) := by
  have hl : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    exact (Complex.ofReal_log (x := 2) (by norm_num)).symm
  have hh : Complex.log (1 / 2 : ℂ) = -(Real.log 2 : ℂ) := by
    simpa only [one_div, Real.log_inv, Complex.ofReal_inv, Complex.ofReal_ofNat,
      Complex.ofReal_neg] using (Complex.ofReal_log (x := (2 : ℝ)⁻¹) (by positivity)).symm
  have he : Complex.exp (Real.log 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_exp, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hen : Complex.exp (-(Real.log 2 : ℂ)) = 1 / 2 := by
    rw [Complex.exp_neg, he]
    norm_num
  have hm : Complex.exp (-(Real.log 2 : ℂ) * s) *
      Complex.exp (-(Real.log 2 : ℂ) * (1 - s)) = 1 / 2 := by
    rw [← Complex.exp_add, show -(Real.log 2 : ℂ) * s +
      -(Real.log 2 : ℂ) * (1 - s) = -(Real.log 2 : ℂ) by ring, hen]
  have hs : Complex.exp ((Real.log 2 : ℂ) * (1 - s)) =
      2 * Complex.exp (-(Real.log 2 : ℂ) * s) := by
    rw [show (Real.log 2 : ℂ) * (1 - s) =
      (Real.log 2 : ℂ) + (-(Real.log 2 : ℂ) * s) by ring, Complex.exp_add, he]
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0),
    Complex.cpow_def_of_ne_zero (by norm_num : (1 / 2 : ℂ) ≠ 0), hl, hh, hs]
  unfold sourceTwoPointWeight sourceTwoPointFactor
  calc
    _ = 1 + (c : ℂ) ^ 2 * (Complex.exp (-(Real.log 2 : ℂ) * s) *
        Complex.exp (-(Real.log 2 : ℂ) * (1 - s))) -
        c * Complex.exp (-(Real.log 2 : ℂ) * s) -
        c * Complex.exp (-(Real.log 2 : ℂ) * (1 - s)) := by ring
    _ = _ := by rw [hm]; ring

end RHTower.WeilSingularArithmetic
