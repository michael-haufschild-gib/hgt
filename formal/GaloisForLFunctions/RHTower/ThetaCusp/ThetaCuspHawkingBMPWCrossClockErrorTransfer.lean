import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPWThreePowerDominance

/-!
The two analytic facts needed to transport the PW-B cross-clock cusp charge
from the explicit particular responses to the full responses. The weight in
the second theorem is the exact log-height residue weight, not a stronger
auxiliary moment. Actual-source substitution is kept in a separate leaf.
-/

open Complex MeasureTheory
open RHTower.D4BMPWThreePowerDominance

namespace RHTower.D4BMPWCrossClockErrorTransfer
noncomputable section
set_option autoImplicit false

/-- On the left half of the Xi strip the reflected third Weyl power is the
sharp growth envelope of the whole particular response. -/
theorem reflectedThreePower_left_sharp_bound
    (rho c0 c1 c2 : ℂ) (hleft : rho.re < 1/2)
    (y : ℝ) (hy : 1 ≤ y) :
    ‖reflectedThreePower rho c0 c1 c2 y‖ ≤
      (‖c0‖ + ‖c1‖ + ‖c2‖) * y ^ (2 - 2 * rho).re := by
  have hypos : 0 < y := by linarith
  have hp0 : (2 * rho).re ≤ (2 - 2 * rho).re := by
    norm_num [Complex.sub_re, Complex.mul_re]
    linarith
  have hp1 : (1 : ℂ).re ≤ (2 - 2 * rho).re := by
    norm_num [Complex.sub_re, Complex.mul_re]
    linarith
  have h0 : y ^ (2 * rho).re ≤ y ^ (2 - 2 * rho).re :=
    Real.rpow_le_rpow_of_exponent_le hy hp0
  have h1 : y ^ (1 : ℂ).re ≤ y ^ (2 - 2 * rho).re :=
    Real.rpow_le_rpow_of_exponent_le hy hp1
  dsimp [reflectedThreePower]
  calc
    _ ≤ ‖c0 * (y : ℂ) ^ (2 * rho)‖ +
        ‖c1 * (y : ℂ) ^ (1 : ℂ)‖ +
        ‖c2 * (y : ℂ) ^ (2 - 2 * rho)‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖c0‖ * y ^ (2 * rho).re + ‖c1‖ * y ^ (1 : ℂ).re +
        ‖c2‖ * y ^ (2 - 2 * rho).re := by
      rw [norm_mul, norm_mul, norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos hypos,
        Complex.norm_cpow_eq_rpow_re_of_pos hypos,
        Complex.norm_cpow_eq_rpow_re_of_pos hypos]
    _ ≤ ‖c0‖ * y ^ (2 - 2 * rho).re + ‖c1‖ * y ^ (2 - 2 * rho).re +
        ‖c2‖ * y ^ (2 - 2 * rho).re := by
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left h0 (norm_nonneg _))
        (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))) le_rfl
    _ = _ := by simp only [Complex.sub_re]; norm_num; ring

/-- Exact cross-error transfer: two native `L²` remainders cannot create a
nonintegrable weighted cross term when the weighted principal channels are
`L²` and the weight is bounded by one. -/
theorem weighted_cross_error_integrable
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (K₀ K₁ R₀ R₁ w : α → ℂ)
    (hK₀ : MemLp (fun x => w x * K₀ x) 2 μ)
    (hK₁ : MemLp (fun x => w x * K₁ x) 2 μ)
    (hR₀ : MemLp R₀ 2 μ) (hR₁ : MemLp R₁ 2 μ)
    (hw : AEStronglyMeasurable w μ)
    (hw_bound : ∀ᵐ x ∂μ, ‖w x‖ ≤ 1) :
    Integrable (fun x => w x *
      ((K₀ x + R₀ x) * (K₁ x + R₁ x) - K₀ x * K₁ x)) μ := by
  have hwR₀ : MemLp (fun x => w x * R₀ x) 2 μ := by
    apply MemLp.of_le_mul (c := 1) hR₀ (hw.mul hR₀.aestronglyMeasurable)
    filter_upwards [hw_bound] with x hx
    change ‖w x * R₀ x‖ ≤ 1 * ‖R₀ x‖
    rw [norm_mul, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hx
  have h₀ := hK₀.integrable_mul hR₁
  have h₁ := hK₁.integrable_mul hR₀
  have h₂ := hwR₀.integrable_mul hR₁
  apply ((h₀.add h₁).add h₂).congr
  filter_upwards with x
  dsimp
  ring

end
end RHTower.D4BMPWCrossClockErrorTransfer
