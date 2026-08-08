import GaloisForLFunctions.RHTower.BurnolCoPoissonSubWindowSource

/-!
# The coefficient-faithful prime-two Burnol--Xi completion multiplier

This module isolates the explicit pre-divisor multiplier

`C₂(w) = w² (w - 1) / (2 (2^w - 1))`

from its later Xi landing.  Nonvanishing in the open critical strip is source-native: the dyadic
factor cannot vanish when `Re w > 0`, and the two polar factors stay away from `0` and `1`.
-/

open Complex Real

noncomputable section

namespace RHTower

/-- Critical-line path used by the source completion before any Xi-divisor specialization. -/
def burnolXiCriticalLineArgument (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) + Complex.I * (x : ℂ)

@[simp] theorem burnolXiCriticalLineArgument_re (x : ℝ) :
    (burnolXiCriticalLineArgument x).re = 1 / 2 := by
  simp [burnolXiCriticalLineArgument]

/-- Exact coefficient-faithful multiplier carrying the fixed prime-two Burnol source to Xi. -/
def burnolXiCompletionMultiplier (w : ℂ) : ℂ :=
  w ^ 2 * (w - 1) / (2 * ((2 : ℂ) ^ w - 1))

theorem half_cpow_neg_eq_two_cpow (w : ℂ) :
    ((1 / 2 : ℝ) : ℂ) ^ (-w) = (2 : ℂ) ^ w := by
  have harg : Complex.arg (2 : ℂ) ≠ Real.pi := by
    change Complex.arg (((2 : ℝ) : ℂ)) ≠ Real.pi
    rw [Complex.arg_ofReal_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact ne_of_lt Real.pi_pos
  rw [show (((1 / 2 : ℝ) : ℂ)) = (2 : ℂ)⁻¹ by norm_num,
    Complex.inv_cpow _ _ harg, Complex.cpow_neg, inv_inv]

theorem two_cpow_sub_one_ne_zero {w : ℂ} (hw : 0 < w.re) :
    (2 : ℂ) ^ w - 1 ≠ 0 := by
  have hfactor := subWindowFactor_ne_zero
    (c := (1 / 2 : ℝ)) (d := 1) (by norm_num) (by norm_num) hw
  norm_num only [Complex.ofReal_one] at hfactor
  rw [Complex.one_cpow, half_cpow_neg_eq_two_cpow] at hfactor
  exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hfactor))

/-- The prime-two completion is nonzero throughout the open critical strip. -/
theorem burnolXiCompletionMultiplier_ne_zero
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    burnolXiCompletionMultiplier w ≠ 0 := by
  have hwne0 : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw0
    linarith
  have hwne1 : w ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hw1
    linarith
  exact div_ne_zero
    (mul_ne_zero (pow_ne_zero 2 hwne0) (sub_ne_zero.mpr hwne1))
    (mul_ne_zero two_ne_zero (two_cpow_sub_one_ne_zero hw0))

/-- The coefficient-faithful completion multiplier is complex differentiable throughout the
positive half-plane, hence in particular on the open critical strip. -/
theorem differentiableAt_burnolXiCompletionMultiplier
    {w : ℂ} (hw0 : 0 < w.re) (_hw1 : w.re < 1) :
    DifferentiableAt ℂ burnolXiCompletionMultiplier w := by
  have hden : 2 * ((2 : ℂ) ^ w - 1) ≠ 0 :=
    mul_ne_zero two_ne_zero (two_cpow_sub_one_ne_zero hw0)
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) ^ z) w :=
    differentiableAt_id.const_cpow (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
  unfold burnolXiCompletionMultiplier
  exact ((differentiableAt_id.pow 2).mul
      (differentiableAt_id.sub (differentiableAt_const (c := (1 : ℂ))))).div
    ((differentiableAt_const (c := (2 : ℂ))).mul
      (hpow.sub (differentiableAt_const (c := (1 : ℂ))))) hden

end RHTower
