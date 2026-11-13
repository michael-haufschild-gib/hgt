import GaloisForLFunctions.HTGeometry.HardyBoundary.UnitaryRealDilation
import GaloisForLFunctions.HTGeometry.HardyBoundary.LogarithmicFourierDomain

/-!
# Dilation of logarithmic Fourier energy

Positive unitary dilations preserve absolute logarithmic integrability.
The signed energy gains the logarithm of the scale times square mass.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped FourierTransform
namespace GaloisForLFunctions.HTGeometry

/-- The signed logarithmic spectral energy, in the `2π` Fourier convention. -/
def logarithmicFourierEnergy (f : ℝ → ℝ) : ℝ :=
  ∫ ξ, Real.log |ξ| * ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2

private theorem abs_log_mul_le {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    |Real.log (|a * ξ|)| ≤ |Real.log a| + |Real.log (|ξ|)| := by
  by_cases hξ : ξ = 0
  · simp only [hξ, mul_zero, abs_zero, Real.log_zero, add_zero]
    exact abs_nonneg _
  · rw [abs_mul, abs_of_pos ha, Real.log_mul ha.ne' (abs_pos.mpr hξ).ne']
    exact abs_add_le _ _

/-- Positive unitary dilations preserve the absolute logarithmic Fourier domain. -/
theorem integrable_abs_log_fourier_sq_unitaryRealDilation {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℝ} (hf1 : Integrable f) (hf2 : MemLp (fun u => (f u : ℂ)) 2 volume)
    (hlog : Integrable (fun ξ => |Real.log (|ξ|)| * ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2)) :
    Integrable (fun ξ => |Real.log (|ξ|)| *
      ‖𝓕 (fun u => (unitaryRealDilation a f u : ℂ)) ξ‖ ^ 2) := by
  apply integrable_weighted_fourier_sq_unitaryRealDilation ha f (fun ξ => |Real.log (|ξ|)|)
  have hF := RHTower.continuous_fourier_of_integrable
    (f := fun u => (f u : ℂ)) (hf1.ofReal (𝕜 := ℂ))
  have hm : Integrable (fun ξ : ℝ => ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2) :=
    RHTower.integrable_norm_sq_fourier (f := fun u => (f u : ℂ))
      (hf1.ofReal (𝕜 := ℂ)) hf2
  have hmeas : Measurable (fun ξ => |Real.log (|a * ξ|)| *
      ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2) := by fun_prop
  apply ((hm.const_mul |Real.log a|).add hlog).mono' hmeas.aestronglyMeasurable
  exact Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    simpa only [add_mul, Pi.add_apply] using
      mul_le_mul_of_nonneg_right (abs_log_mul_le ha ξ) (sq_nonneg ‖𝓕 (fun u => (f u : ℂ)) ξ‖)

/-- Dilation adds the logarithm of its scale times square mass to the spectral energy. -/
theorem logarithmicFourierEnergy_unitaryRealDilation {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℝ} (hf1 : Integrable f) (hf2 : MemLp (fun u => (f u : ℂ)) 2 volume)
    (hlog : Integrable (fun ξ => |Real.log (|ξ|)| * ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2)) :
    logarithmicFourierEnergy (unitaryRealDilation a f) =
      logarithmicFourierEnergy f + Real.log a * ∫ u, f u ^ 2 := by
  have hF := RHTower.continuous_fourier_of_integrable
    (f := fun u => (f u : ℂ)) (hf1.ofReal (𝕜 := ℂ))
  have hm : Integrable (fun ξ : ℝ => ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2) :=
    RHTower.integrable_norm_sq_fourier (f := fun u => (f u : ℂ))
      (hf1.ofReal (𝕜 := ℂ)) hf2
  have hi : Integrable (fun ξ => Real.log |ξ| * ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2) := by
    have hmeas : Measurable (fun ξ => Real.log |ξ| *
        ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2) := by fun_prop
    apply hlog.mono' hmeas.aestronglyMeasurable
    exact Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (sq_nonneg ‖𝓕 (fun u => (f u : ℂ)) ξ‖)]
  unfold logarithmicFourierEnergy
  rw [integral_weighted_fourier_sq_unitaryRealDilation ha f (fun ξ => Real.log |ξ|)]
  have hn : ∀ᵐ ξ : ℝ, ξ ≠ 0 := by simp [ae_iff]
  calc
    _ = ∫ ξ, Real.log |ξ| * ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2 +
        Real.log a * ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hn] with ξ hξ
      rw [abs_mul, abs_of_pos ha, Real.log_mul ha.ne' (abs_pos.mpr hξ).ne']
      ring
    _ = _ := by
      rw [integral_add hi (hm.const_mul (Real.log a)),
        integral_const_mul, RHTower.integral_norm_sq_fourier_eq
          (f := fun u => (f u : ℂ)) (hf1.ofReal (𝕜 := ℂ)) hf2]
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

#print axioms integrable_abs_log_fourier_sq_unitaryRealDilation
#print axioms logarithmicFourierEnergy_unitaryRealDilation
end GaloisForLFunctions.HTGeometry
