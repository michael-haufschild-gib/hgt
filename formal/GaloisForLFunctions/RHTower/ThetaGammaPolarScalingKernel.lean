import GaloisForLFunctions.RHTower.ThetaCuspGammaSourceAction
import GaloisForLFunctions.RHTower.ThetaCuspPolarSourceAction

/-!
# The continuous Gamma/pole shift has both signs

The exact combined Gamma and pole integrand splits into a diagonal term
and a continuous translation coefficient. That coefficient is negative
at `log (5/4)` and positive at `log 2`. Thus the diagonal quadratic
identity does not turn the full Gamma/pole operator into a positive jump
measure. The factorization below retains the precise coefficient for a
future comparison with the discrete prime energy.
-/

noncomputable section

namespace RHTower.ThetaSourceWard

def thetaGammaPolarScalingKernel (u : ℝ) : ℝ :=
  2 * Real.cosh (u / 2) - Real.exp (-u / 2) / (1 - Real.exp (-2 * u))

/-- Exact coefficient of the off-diagonal continuous source translation. -/
theorem thetaGammaPolarScalingKernel_source_decomposition (x u : ℝ) :
    (gammaSourceTerm x u : ℂ) + polarSourceTerm (1 / 2) x u + polarSourceTerm (-1 / 2) x u =
      ((Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) * thetaCuspFullSource x +
        thetaGammaPolarScalingKernel u * thetaCuspFullSource (x + u) : ℝ) : ℂ) := by
  rw [add_assoc, polarSource_half_point, ← Complex.ofReal_add]
  congr 1
  unfold gammaSourceTerm thetaGammaPolarScalingKernel
  ring

theorem thetaGammaPolarScalingKernel_factor (u : ℝ) :
    thetaGammaPolarScalingKernel u = Real.exp (-u / 2) *
      (Real.exp u + 1 - 1 / (1 - Real.exp (-2 * u))) := by
  have he : Real.exp (u / 2) = Real.exp (-u / 2) * Real.exp u := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold thetaGammaPolarScalingKernel
  rw [Real.cosh_eq, he]
  simp only [neg_div]
  ring

private theorem exp_neg_two_log (r : ℝ) (hr : 0 < r) :
    Real.exp (-2 * Real.log r) = (r ^ 2)⁻¹ := by
  rw [show -2 * Real.log r = -(Real.log (r ^ 2)) by rw [Real.log_pow]; ring,
    Real.exp_neg, Real.exp_log (sq_pos_of_pos hr)]

/-- A literal positive shift with negative Gamma/pole translation coefficient. -/
theorem thetaGammaPolarScalingKernel_log_five_fourths_neg :
    thetaGammaPolarScalingKernel (Real.log (5 / 4 : ℝ)) < 0 := by
  rw [thetaGammaPolarScalingKernel_factor, Real.exp_log (by norm_num : (0 : ℝ) < 5 / 4),
    exp_neg_two_log _ (by norm_num)]
  apply mul_neg_of_pos_of_neg (Real.exp_pos _)
  norm_num

/-- The same exact coefficient becomes positive at another positive shift. -/
theorem thetaGammaPolarScalingKernel_log_two_pos :
    0 < thetaGammaPolarScalingKernel (Real.log (2 : ℝ)) := by
  rw [thetaGammaPolarScalingKernel_factor, Real.exp_log zero_lt_two,
    exp_neg_two_log _ zero_lt_two]
  apply mul_pos (Real.exp_pos _)
  norm_num

theorem thetaGammaPolarScalingKernel_both_signs :
    (∃ u : ℝ, 0 < u ∧ thetaGammaPolarScalingKernel u < 0) ∧
      ∃ u : ℝ, 0 < u ∧ 0 < thetaGammaPolarScalingKernel u := by
  exact ⟨⟨Real.log (5 / 4 : ℝ), Real.log_pos (by norm_num),
    thetaGammaPolarScalingKernel_log_five_fourths_neg⟩,
    Real.log 2, Real.log_pos one_lt_two, thetaGammaPolarScalingKernel_log_two_pos⟩

end RHTower.ThetaSourceWard
