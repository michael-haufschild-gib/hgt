import GaloisForLFunctions.HTGeometry.ClockSeriesDerivative
import GaloisForLFunctions.HTGeometry.ClockStripStepOperator

/-!
# The step operator commutes with a convergent series

Summing the recursion that defines the clock iterates requires the step operator to pass through the
sum. It is linear, so this is the term-by-term differentiation of the previous file together with
the elementary behaviour of a sum under multiplication by a fixed value and division by a constant.

The summability of the second derivatives is Cauchy's estimate applied to the summable bound on the
functions themselves.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

/-- **The step operator commutes with a series of holomorphic functions.** -/
theorem clockStripStep_tsum {ρ₂ ρ₁ ρ' : ℝ} (h21 : ρ₂ < ρ₁) (h1ρ : ρ₁ < ρ')
    {V : ℂ → ℂ} {f : ℕ → ℂ → ℂ} {M : ℕ → ℝ}
    (hf : ∀ m, DifferentiableOn ℂ (f m) (imStrip ρ'))
    (hM : ∀ m, ∀ w ∈ imStrip ρ', ‖f m w‖ ≤ M m) (hMs : Summable M)
    {z : ℂ} (hz : z ∈ imStrip ρ₂) :
    clockStripStep V (fun w => ∑' m, f m w) z = ∑' m, clockStripStep V (f m) z := by
  have h2ρ : ρ₂ < ρ' := lt_trans h21 h1ρ
  have hgap : (0 : ℝ) < ρ' - ρ₂ := by linarith
  have hz' : z ∈ imStrip ρ' := imStrip_mono h2ρ.le hz
  -- summability of the second derivatives, by Cauchy's estimate
  have hsum1 : Summable fun m => deriv (deriv (f m)) z := by
    refine Summable.of_norm_bounded
      (g := fun m => 16 * M m / (ρ' - ρ₂) ^ 2) ?_ fun m => ?_
    · simpa [mul_div_assoc] using (hMs.mul_left 16).div_const ((ρ' - ρ₂) ^ 2)
    · exact norm_deriv_deriv_le_on_imStrip h2ρ (hf m) (hM m) (le_of_lt (mem_imStrip.mp hz))
  have hsumf : Summable fun m => f m z :=
    Summable.of_norm_bounded hMs fun m => hM m z hz'
  have hsum2 : Summable fun m => V z * f m z := hsumf.mul_left _
  have hlhs : clockStripStep V (fun w => ∑' m, f m w) z
      = (deriv (deriv fun w => ∑' m, f m w) z + V z * ∑' m, f m z) / 4 := rfl
  have hrhs : ∀ m, clockStripStep V (f m) z = (deriv (deriv (f m)) z + V z * f m z) / 4 :=
    fun m => rfl
  rw [hlhs, deriv_deriv_tsum_of_holomorphic h21 h1ρ hf hM hMs hz, ← tsum_mul_left,
    ← hsum1.tsum_add hsum2, ← tsum_div_const]
  exact tsum_congr fun m => (hrhs m).symm

end GaloisForLFunctions.HTGeometry
