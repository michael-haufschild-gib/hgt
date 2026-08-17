import GaloisForLFunctions.HTGeometry.L2DerivativeFourier
import GaloisForLFunctions.HTGeometry.L2FourierMultiplier

/-!
# A weighted split of a bounded multiplier

A bounded multiplier obeys the bound of its symbol, but that crude estimate is useless when the
symbol is small only on a set where the datum is concentrated and the sharp bound on that set grows.
The weighted form keeps a pointwise majorant `B` of the symbol on a set `S` and the global bound off
`S`:

`‖M_φ g‖² ≤ ∫_S B² ‖g‖² + C² ∫_{Sᶜ} ‖g‖²`.

This is what a wave-packet comparison needs: the on-band majorant may grow, provided it is
integrable against the packet, while off band only the total mass of the tail enters.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

theorem norm_lpBoundedMulCLM_sq_split {φ : ℝ → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖φ x‖ ≤ C) {S : Set ℝ} (hS : MeasurableSet S) {B : ℝ → ℝ}
    (hB : ∀ x ∈ S, ‖φ x‖ ≤ B x)
    (g : Lp (α := ℝ) (μ := (volume : Measure ℝ)) ℂ 2)
    (hint : IntegrableOn (fun x => (B x) ^ 2 * ‖(g : ℝ → ℂ) x‖ ^ 2) S) :
    ‖lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) hφ hC0 hC g‖ ^ 2
      ≤ (∫ x in S, (B x) ^ 2 * ‖(g : ℝ → ℂ) x‖ ^ 2)
        + C ^ 2 * ∫ x in Sᶜ, ‖(g : ℝ → ℂ) x‖ ^ 2 := by
  have hgint : Integrable (fun x : ℝ => ‖(g : ℝ → ℂ) x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).1 (Lp.memLp g)
  have hmeas : AEStronglyMeasurable (fun x : ℝ => ‖φ x * (g : ℝ → ℂ) x‖ ^ 2)
      (volume : Measure ℝ) :=
    ((hφ.aestronglyMeasurable.mul (Lp.aestronglyMeasurable g)).norm.pow 2)
  have hpointwise : ∀ x : ℝ, ‖φ x * (g : ℝ → ℂ) x‖ ^ 2 ≤ C ^ 2 * ‖(g : ℝ → ℂ) x‖ ^ 2 := by
    intro x
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hC x) 2) (by positivity)
  have hprodint : Integrable (fun x : ℝ => ‖φ x * (g : ℝ → ℂ) x‖ ^ 2) := by
    refine Integrable.mono (hgint.const_mul (C ^ 2)) hmeas ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    exact hpointwise x
  have hval : ‖lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) hφ hC0 hC g‖ ^ 2
      = ∫ x : ℝ, ‖φ x * (g : ℝ → ℂ) x‖ ^ 2 := by
    rw [norm_lpTwo_sq (μ := (volume : Measure ℝ))]
    refine integral_congr_ae ?_
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ)) hφ hC0 hC g]
      with x hx
    rw [hx]
  rw [hval, ← integral_add_compl hS hprodint]
  have hband : ∫ x in S, ‖φ x * (g : ℝ → ℂ) x‖ ^ 2
      ≤ ∫ x in S, (B x) ^ 2 * ‖(g : ℝ → ℂ) x‖ ^ 2 := by
    refine setIntegral_mono_on hprodint.integrableOn hint hS ?_
    intro x hx
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hB x hx) 2) (by positivity)
  have htail : ∫ x in Sᶜ, ‖φ x * (g : ℝ → ℂ) x‖ ^ 2
      ≤ C ^ 2 * ∫ x in Sᶜ, ‖(g : ℝ → ℂ) x‖ ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on hprodint.integrableOn
      ((hgint.const_mul (C ^ 2)).integrableOn) hS.compl ?_
    intro x _
    exact hpointwise x
  linarith [hband, htail]

end GaloisForLFunctions.HTGeometry
