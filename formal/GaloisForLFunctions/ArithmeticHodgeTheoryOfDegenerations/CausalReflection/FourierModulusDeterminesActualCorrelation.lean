import GaloisForLFunctions.RHTower.MellinLinePolarization
import GaloisForLFunctions.HTGeometry.FourierDecayFromDerivative

/-!
# Fourier modulus determines every actual translated correlation

Polarized Plancherel and the translation character express each correlation
through the squared Fourier modulus. The statement applies to literal L¹∩L²
representatives without smoothness or compact support.
-/

noncomputable section
open MeasureTheory Filter FourierTransform

namespace GaloisForLFunctions.HTGeometry

private theorem conj_mul_self_eq_norm_sq (z : ℂ) :
    (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext <;> norm_num [Complex.sq_norm, Complex.normSq_apply] <;> ring

/-- Equal Fourier moduli give equal literal correlations at every translation. -/
theorem integral_conj_mul_translate_eq_of_fourier_norm
    {f g : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2 volume)
    (hg1 : Integrable g) (hg2 : MemLp g 2 volume)
    (hmod : ∀ᵐ ξ : ℝ, ‖𝓕 f ξ‖ = ‖𝓕 g ξ‖) (t : ℝ) :
    (∫ u, (starRingEnd ℂ) (f u) * f (u + t)) =
      ∫ u, (starRingEnd ℂ) (g u) * g (u + t) := by
  have hft : MemLp (fun u => f (u + t)) 2 volume :=
    hf2.comp_measurePreserving (measurePreserving_add_right volume t)
  have hgt : MemLp (fun u => g (u + t)) 2 volume :=
    hg2.comp_measurePreserving (measurePreserving_add_right volume t)
  rw [← _root_.RHTower.integral_conj_fourier_mul_fourier hf1 hf2 (hf1.comp_add_right t) hft,
    ← _root_.RHTower.integral_conj_fourier_mul_fourier hg1 hg2 (hg1.comp_add_right t) hgt]
  refine integral_congr_ae ?_
  filter_upwards [hmod] with ξ hξ
  rw [fourier_translate f t ξ, fourier_translate g t ξ]
  calc
    _ = ((Real.fourierChar (t * ξ) : Circle) : ℂ) *
        ((starRingEnd ℂ) (𝓕 f ξ) * 𝓕 f ξ) := by ring
    _ = ((Real.fourierChar (t * ξ) : Circle) : ℂ) *
        ((starRingEnd ℂ) (𝓕 g ξ) * 𝓕 g ξ) := by
      rw [conj_mul_self_eq_norm_sq, conj_mul_self_eq_norm_sq, hξ]
    _ = _ := by ring

end GaloisForLFunctions.HTGeometry
