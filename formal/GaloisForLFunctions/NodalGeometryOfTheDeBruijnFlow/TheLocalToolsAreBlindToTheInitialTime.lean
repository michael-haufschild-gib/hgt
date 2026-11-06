import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheFrequencyIsAChaosLevel
import GaloisForLFunctions.RHTower.DeBruijnStripThreshold

/-!
# The local tools are blind to the initial time

The fake that limits every tool of the programme. For `τ > 0` the backward-heated kernel `Φ_τ(x) = Φ(x) e^{−τx²}` is again of super-Gaussian decay (`shiftKernel_superGaussian`), and its caloric flow is
the time shift `u_t = H_{t−τ}` (`caloric_shiftKernel`). So the Fock identity, the frequency, its monotonicity, the order law and the doubling inequality hold for the shifted flow exactly as for `H_t`
(`order_le_two_mul_frequency_shift`). But the shifted flow has non-real zeros at every time `0 ≤ t < τ`, of unbounded depth at large height (`exists_deep_zero_shift`). So no statement using only the parabolic structure and the decay of the kernel can see
the time `t = 0` as special: it cannot give the reality of the zeros at `t = 0`, nor the central inequality. An input must distinguish `Φ` among the kernels `Φ_τ`, and that is the content of RH.

The local Dyson laws are blind in the same way: a pair born at a collision of the flow, at any time, has the same gap law. And `H_{−τ}` is not the only fake. The pair model of route ZCG shows the same for sources that satisfy the functional equation and the Riemann–von Mangoldt spacing.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-- The backward-heated kernel. -/
def shiftKernel (τ x : ℝ) : ℝ := riemannKernelReal x * Real.exp (-τ * x ^ 2)

/-- **The shifted kernel has the same decay.** -/
theorem shiftKernel_superGaussian (τ : ℝ) : SuperGaussian (shiftKernel τ) := by
  refine ⟨riemannKernel_superGaussian.continuous.mul (by fun_prop), fun c => ?_⟩
  refine (riemannKernel_superGaussian.integrable_mul_exp (c - τ)).congr (Eventually.of_forall fun x => ?_)
  simp only [shiftKernel]
  rw [abs_mul, Real.abs_exp, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **The caloric flow of the shifted kernel is the time shift.** -/
theorem caloric_shiftKernel (τ t : ℝ) : caloric (shiftKernel τ) t = riemannHeat (t - τ) := by
  rw [← caloric_riemannKernel]
  funext z
  unfold caloric
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [shiftKernel]
  have h : riemannKernelReal y * Real.exp (-τ * y ^ 2) * Real.exp (t * y ^ 2) =
      riemannKernelReal y * Real.exp ((t - τ) * y ^ 2) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [h]

/-- **The order law does not see the shift.** At every time and every point, the order of a zero of `H_{t−τ}` is at most twice the frequency of the shifted flow. -/
theorem order_le_two_mul_frequency_shift (τ t : ℝ) {σ : ℝ} (hσ : 0 < σ) {z₀ : ℂ} {k : ℕ}
    (hvan : ∀ n < k, iteratedDeriv n (riemannHeat (t - τ)) z₀ = 0)
    (hk : iteratedDeriv k (riemannHeat (t - τ)) z₀ ≠ 0) :
    (k : ℝ) ≤ 2 * frequency (shiftKernel τ) t z₀ σ := by
  rw [← caloric_shiftKernel] at hvan hk
  exact order_le_two_mul_frequency (shiftKernel_superGaussian τ) t hσ hvan
    (lineEnergy_pos (shiftKernel_superGaussian τ) t hσ hk)

/-- **The frequency is monotone for the shifted flow as well.** -/
theorem frequency_shift_le (τ t : ℝ) {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (h : σ₁ ≤ σ₂) {z₀ : ℂ} {k : ℕ}
    (hk : iteratedDeriv k (riemannHeat (t - τ)) z₀ ≠ 0) :
    frequency (shiftKernel τ) t z₀ σ₁ ≤ frequency (shiftKernel τ) t z₀ σ₂ := by
  rw [← caloric_shiftKernel] at hk
  exact frequency_le_frequency (shiftKernel_superGaussian τ) t hσ₁ h
    (lineEnergy_pos (shiftKernel_superGaussian τ) t hσ₁ hk)

/-- **The fake.** Before the time `τ` the shifted flow has zeros of unbounded depth at arbitrarily large height. -/
theorem exists_deep_zero_shift {τ t : ℝ} (ht : t < τ) (D R : ℝ) :
    ∃ z : ℂ, caloric (shiftKernel τ) t z = 0 ∧ R ≤ z.re ∧ D < |z.im| := by
  rw [caloric_shiftKernel]
  exact exists_riemannHeat_zero_abs_im_gt_of_neg (by linarith only [ht]) D R

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
