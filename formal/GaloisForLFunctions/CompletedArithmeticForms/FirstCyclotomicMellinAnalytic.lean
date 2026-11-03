import GaloisForLFunctions.CompletedArithmeticForms.FirstCyclotomicMellinNoncancellation
import GaloisForLFunctions.HTGeometry.DaiYoshikawa.MellinSplit
import GaloisForLFunctions.HTGeometry.PhaseGridApproximation
import GaloisForLFunctions.RHTower.XiWardCriticalBudgetProbe

/-!
# Analyticity and zero retention of the first cyclotomic multiplier

The kernel vanishes linearly at the origin, so its Mellin transform is
holomorphic on `Re s > -1`. The unconditional ordinate gap puts every
upper right Xi zero inside its nonvanishing region.
-/

noncomputable section
set_option autoImplicit false

open Complex MeasureTheory Set

namespace GaloisForLFunctions.CompletedArithmeticForms

open GaloisForLFunctions.HTGeometry.DaiYoshikawa

/-- Difference kernel of one full cyclotomic turn. -/
def firstCyclotomicKernel (t : ℝ) : ℂ :=
  1 - Complex.exp (Complex.I * (2 * Real.pi) * t)

theorem continuous_firstCyclotomicKernel : Continuous firstCyclotomicKernel := by
  unfold firstCyclotomicKernel
  fun_prop

/-- The phase arc is Lipschitz in its angle. -/
theorem norm_firstCyclotomicKernel_le (t : ℝ) :
    ‖firstCyclotomicKernel t‖ ≤ 2 * Real.pi * |t| := by
  have hphase : Complex.I * (2 * Real.pi) * t =
      ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [firstCyclotomicKernel, hphase, norm_sub_rev]
  have h := GaloisForLFunctions.HTGeometry.norm_exp_mul_I_sub_one_le (2 * Real.pi * t)
  simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos Real.pi_pos] using h

private theorem firstCyclotomicMellin_eq_mellinHead :
    firstCyclotomicMellin = mellinHead firstCyclotomicKernel := by
  funext s
  rw [mellinHead_eq_setIntegral,
    firstCyclotomicMellin, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [firstCyclotomicKernel, smul_eq_mul]

/-- Linear vanishing of the kernel extends holomorphy across the imaginary axis. -/
theorem differentiableAt_firstCyclotomicMellin {s : ℂ} (hs : -1 < s.re) :
    DifferentiableAt ℂ firstCyclotomicMellin s := by
  rw [firstCyclotomicMellin_eq_mellinHead]
  exact differentiableAt_mellinHead continuous_firstCyclotomicKernel
    (fun t ht => by simpa only [abs_of_pos ht.1] using norm_firstCyclotomicKernel_le t) hs

/-- The first cyclotomic multiplier cannot cancel an upper right Xi zero. -/
theorem firstCyclotomicMellin_at_right_zero_ne_zero
    (q : _root_.RHTower.XiRightUpperZeroCopy) :
    firstCyclotomicMellin (_root_.RHTower.xiRightCenteredZero q.1) ≠ 0 := by
  apply firstCyclotomicMellin_ne_zero (_root_.RHTower.xiRightCenteredZero_re_pos q.1)
  have hh := _root_.RHTower.xiWard_offlinePair_abs_im_gt_eight q
  rw [abs_of_pos q.2] at hh
  linarith only [Real.pi_lt_four, hh]

#print axioms differentiableAt_firstCyclotomicMellin
#print axioms firstCyclotomicMellin_at_right_zero_ne_zero

end GaloisForLFunctions.CompletedArithmeticForms
