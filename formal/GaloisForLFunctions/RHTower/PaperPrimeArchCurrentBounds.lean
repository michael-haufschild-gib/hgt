import GaloisForLFunctions.RHTower.PaperPrimeArchCurrent
import GaloisForLFunctions.RHTower.XiCDerivStripDecay

/-! # Uniform decay of the complete signed current

The original current is bounded without saturating, normalizing or discarding its sign.
One exponential envelope works throughout the open upper half-strip.
-/

namespace RHTower.PaperPrimeArch
noncomputable section

theorem abs_current_le_product (a : Height) (x : ℝ) :
    |current a x| ≤ ‖deriv XiC (point a x)‖ * ‖XiC (point a x)‖ := by
  simpa only [current, abs_neg, norm_mul, norm_star] using
    Complex.abs_im_le_norm (deriv XiC (point a x) * star (XiC (point a x)))

theorem exists_decay_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ a : Height, ∀ x : ℝ,
    |current a x| ≤ C * Real.exp (-(Real.pi / 4 * |x|)) := by
  have hd0 : 0 ≤ Real.pi / 8 := by positivity
  have hd : 2 * (Real.pi / 8) < Real.pi / 2 := by linarith [Real.pi_pos]
  obtain ⟨C, hC, hX⟩ := exists_norm_XiC_horizontal_le (A := 1 / 2) (by norm_num) hd0 hd
  obtain ⟨D, hD, hDX⟩ := exists_norm_XiC_deriv_horizontal_le
    (A := 1 / 2) (by norm_num) hd0 hd
  refine ⟨D * C, mul_nonneg hD hC, fun a x => ?_⟩
  have ha : |(a : ℝ)| ≤ 1 / 2 := by
    rw [abs_of_pos a.property.1]
    exact a.property.2.le
  calc
    |current a x| ≤ ‖deriv XiC (point a x)‖ * ‖XiC (point a x)‖ :=
      abs_current_le_product a x
    _ ≤ (D * Real.exp (-(Real.pi / 8 * |x|))) *
        (C * Real.exp (-(Real.pi / 8 * |x|))) :=
      mul_le_mul (hDX x a ha) (hX x a ha) (norm_nonneg _) (by positivity)
    _ = D * C * Real.exp (-(Real.pi / 4 * |x|)) := by
      rw [mul_mul_mul_comm, ← Real.exp_add]
      congr 2
      ring

def decayBudget : ℝ := exists_decay_bound.choose

theorem decayBudget_nonneg : 0 ≤ decayBudget := exists_decay_bound.choose_spec.1

theorem abs_current_le_decay (a : Height) (x : ℝ) :
    |current a x| ≤ decayBudget * Real.exp (-(Real.pi / 4 * |x|)) :=
  exists_decay_bound.choose_spec.2 a x

theorem abs_current_le (a : Height) (x : ℝ) : |current a x| ≤ decayBudget := by
  apply (abs_current_le_decay a x).trans
  exact mul_le_of_le_one_right decayBudget_nonneg
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))

theorem norm_current_le (a : Height) (x : ℝ) : ‖(current a x : ℂ)‖ ≤ decayBudget := by
  simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_current_le a x

end
end RHTower.PaperPrimeArch
