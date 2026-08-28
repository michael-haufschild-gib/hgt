import GaloisForLFunctions.RHTower.FZZCigarParityKreinAntiunitaryCriticalEigenline

/-!
# Phase-window classification of the FZZ parity Krein eigenline

The balanced coordinate of the literal positive-imaginary FZZ source eigenline is not an
arbitrary unit phase.  Its real part is strictly negative and its imaginary part strictly positive
at every physical scale.  Hence its principal phase lies in the open upper-left quadrant.

This file computes that quadrant exactly, classifies every logarithmic lift of the corresponding
dyadic Mellin carrier, and proves an exact fibre theorem on the critical line.  Every source lift
has ordinate in one open quarter-period window

`(2*pi*k + pi/2, 2*pi*k + pi) / log 2`.

Thus completeness of this literal one-eigenline source family requires the target divisor's
ordinates to lie in this proper periodic window set.  The classification is unconditional; the
separate arithmetic question is whether zeta-zero ordinates escape those windows.
-/

open Complex

namespace RHTower

noncomputable section

/-- Exact real part of the balanced positive-imaginary source eigenline coordinate. -/
theorem fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_re (beta : ℝ) :
    (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta).re =
      -fzzCigarParitySourceMetricReflectionScale beta * fzzKreinPAt beta /
        fzzKreinQAt beta := by
  rw [fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_eq,
    fzzCigarParityDilatedTwoScaleKreinEigenvalue]
  simp

/-- Exact imaginary part of the balanced positive-imaginary source eigenline coordinate. -/
theorem fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_im (beta : ℝ) :
    (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta).im =
      fzzCigarParitySourceMetricReflectionScale beta *
          Real.sqrt (fzzCigarParityDilatedTwoScaleKreinDiscriminant beta) /
        fzzKreinQAt beta := by
  rw [fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_eq,
    fzzCigarParityDilatedTwoScaleKreinEigenvalue]
  simp

/-- The balanced positive-imaginary source eigenline lies strictly left of the imaginary axis. -/
theorem fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_re_neg
    {beta : ℝ} (hbeta : 0 < beta) :
    (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta).re < 0 := by
  rw [fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_re]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos
      (neg_lt_zero.mpr (fzzCigarParitySourceMetricReflectionScale_pos hbeta))
      (fzzKreinPAt_pos hbeta))
    (fzzKreinQAt_pos hbeta)

/-- The balanced positive-imaginary source eigenline lies strictly above the real axis. -/
theorem fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_im_pos
    {beta : ℝ} (hbeta : 0 < beta) :
    0 < (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta).im := by
  rw [fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_im]
  exact div_pos
    (mul_pos (fzzCigarParitySourceMetricReflectionScale_pos hbeta)
      (Real.sqrt_pos.2
        (fzzCigarParityDilatedTwoScaleKreinDiscriminant_pos hbeta)))
    (fzzKreinQAt_pos hbeta)

/-- Lower endpoint of the source eigenline's open upper-left quadrant. -/
theorem fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_pi_div_two_lt_arg
    {beta : ℝ} (hbeta : 0 < beta) :
    Real.pi / 2 <
      Complex.arg (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta) := by
  rw [lt_iff_not_ge]
  intro harg
  rcases Complex.arg_le_pi_div_two_iff.mp harg with hre | him
  · exact (not_le_of_gt
      (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_re_neg hbeta)) hre
  · exact (not_lt_of_ge
      (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_im_pos hbeta).le) him

/-- Upper endpoint of the source eigenline's open upper-left quadrant. -/
theorem fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_arg_lt_pi
    {beta : ℝ} (hbeta : 0 < beta) :
    Complex.arg (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta) <
      Real.pi := by
  exact Complex.arg_lt_pi_iff.mpr
    (Or.inr (ne_of_gt
      (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_im_pos hbeta)))

/-- Imaginary coordinate of the principal critical Mellin parameter. -/
theorem fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter_im (beta : ℝ) :
    (fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter beta).im =
      Complex.arg (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta) /
        Real.log 2 := by
  rw [fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter,
    Complex.add_im, Complex.mul_im]
  have hhalf : ((1 / 2 : ℂ)).im = 0 := by norm_num
  rw [hhalf]
  simp only [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The principal source Mellin ordinate lies in the first open quarter-period window. -/
theorem fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter_im_window
    {beta : ℝ} (hbeta : 0 < beta) :
    Real.pi / (2 * Real.log 2) <
        (fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter beta).im ∧
      (fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter beta).im <
        Real.pi / Real.log 2 := by
  rw [fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter_im]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · have hrewrite : Real.pi / (2 * Real.log 2) =
        (Real.pi / 2) / Real.log 2 := by
      field_simp
    rw [hrewrite]
    exact (div_lt_div_iff_of_pos_right hlog).2
      (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_pi_div_two_lt_arg hbeta)
  · exact (div_lt_div_iff_of_pos_right hlog).2
      (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_arg_lt_pi hbeta)

/-- Every logarithmic lift of the source eigenline's centered dyadic Mellin parameter. -/
def fzzCigarParityDilatedKreinEigenlineCriticalMellinLift (beta : ℝ) (k : ℤ) : ℂ :=
  fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter beta +
    Complex.I * (((2 * Real.pi * (k : ℝ)) / Real.log 2 : ℝ) : ℂ)

/-- Every logarithmic lift remains on the critical line. -/
theorem fzzCigarParityDilatedKreinEigenlineCriticalMellinLift_re
    (beta : ℝ) (k : ℤ) :
    (fzzCigarParityDilatedKreinEigenlineCriticalMellinLift beta k).re = 1 / 2 := by
  rw [fzzCigarParityDilatedKreinEigenlineCriticalMellinLift, Complex.add_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter_re]
  norm_num

/-- Exact ordinate formula for every logarithmic lift. -/
theorem fzzCigarParityDilatedKreinEigenlineCriticalMellinLift_im
    (beta : ℝ) (k : ℤ) :
    (fzzCigarParityDilatedKreinEigenlineCriticalMellinLift beta k).im =
      (Complex.arg (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta) +
          2 * Real.pi * (k : ℝ)) /
        Real.log 2 := by
  rw [fzzCigarParityDilatedKreinEigenlineCriticalMellinLift, Complex.add_im,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter_im]
  ring

/-- Every logarithmic lift has exactly the literal source eigenline's dyadic Mellin character. -/
theorem fzzCigarParityDyadicMellinCharacter_eigenlineCriticalMellinLift
    {beta : ℝ} (hbeta : 0 < beta) (k : ℤ) :
    fzzCigarParityDyadicMellinCharacter
        (fzzCigarParityDilatedKreinEigenlineCriticalMellinLift beta k) =
      fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta := by
  rw [← fzzCigarParityDyadicMellinCharacter_eigenlineCriticalParameter hbeta,
    fzzCigarParityDyadicMellinCharacter, fzzCigarParityDyadicMellinCharacter,
    centeredComplexModularCharacter, centeredComplexModularCharacter]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨k, ?_⟩
  rw [fzzCigarParityDilatedKreinEigenlineCriticalMellinLift]
  have hlog : (Real.log 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  push_cast
  field_simp [hlog]
  ring

/-- Every logarithmic lift occupies one strict quarter of its dyadic Mellin phase period. -/
theorem fzzCigarParityDilatedKreinEigenlineCriticalMellinLift_im_window
    {beta : ℝ} (hbeta : 0 < beta) (k : ℤ) :
    (2 * Real.pi * (k : ℝ) + Real.pi / 2) / Real.log 2 <
        (fzzCigarParityDilatedKreinEigenlineCriticalMellinLift beta k).im ∧
      (fzzCigarParityDilatedKreinEigenlineCriticalMellinLift beta k).im <
        (2 * Real.pi * (k : ℝ) + Real.pi) / Real.log 2 := by
  rw [fzzCigarParityDilatedKreinEigenlineCriticalMellinLift_im]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · apply (div_lt_div_iff_of_pos_right hlog).2
    linarith [
      fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_pi_div_two_lt_arg hbeta]
  · apply (div_lt_div_iff_of_pos_right hlog).2
    linarith [fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_arg_lt_pi hbeta]

/-- Exact critical-line fibre of the literal source eigenline character: there is no freedom
beyond the integer logarithm branch. -/
theorem fzzCigarParityDyadicMellinCharacter_eq_eigenline_iff_lift_ordinate
    {beta : ℝ} (hbeta : 0 < beta) {rho : ℂ} (hrho : rho.re = 1 / 2) :
    fzzCigarParityDyadicMellinCharacter rho =
        fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta ↔
      ∃ k : ℤ,
        rho.im =
          (Complex.arg (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta) +
              2 * Real.pi * (k : ℝ)) /
            Real.log 2 := by
  constructor
  · intro hchar
    have hprincipal :=
      fzzCigarParityDyadicMellinCharacter_eigenlineCriticalParameter hbeta
    have heq :
        fzzCigarParityDyadicMellinCharacter rho =
          fzzCigarParityDyadicMellinCharacter
            (fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter beta) :=
      hchar.trans hprincipal.symm
    rw [fzzCigarParityDyadicMellinCharacter,
      fzzCigarParityDyadicMellinCharacter,
      centeredComplexModularCharacter, centeredComplexModularCharacter,
      Complex.exp_eq_exp_iff_exists_int] at heq
    obtain ⟨k, hk⟩ := heq
    refine ⟨k, ?_⟩
    have hrholift :
        rho = fzzCigarParityDilatedKreinEigenlineCriticalMellinLift beta k := by
      rw [fzzCigarParityDilatedKreinEigenlineCriticalMellinLift]
      have hlog : (Real.log 2 : ℂ) ≠ 0 := by
        exact_mod_cast (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
      push_cast at hk ⊢
      field_simp [hlog]
      linear_combination hk
    rw [hrholift, fzzCigarParityDilatedKreinEigenlineCriticalMellinLift_im]
  · rintro ⟨k, him⟩
    have hrhoeq :
        rho = fzzCigarParityDilatedKreinEigenlineCriticalMellinLift beta k := by
      apply Complex.ext
      · rw [hrho, fzzCigarParityDilatedKreinEigenlineCriticalMellinLift_re]
      · rw [him, fzzCigarParityDilatedKreinEigenlineCriticalMellinLift_im]
    rw [hrhoeq]
    exact fzzCigarParityDyadicMellinCharacter_eigenlineCriticalMellinLift hbeta k

end

end RHTower
