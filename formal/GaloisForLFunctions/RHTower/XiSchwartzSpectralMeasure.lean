import GaloisForLFunctions.SchwartzSpectralMeasureForm
import GaloisForLFunctions.RHTower.XiSchwartzMetricSupport

/-!
# The Xi null vector for spectral Schwartz forms

This file joins the constructive spectral-measure form with the Xi support theorem.  If an actual
Schwartz source has Fourier transform `XiC` on the real axis, then nullity of that source forces
the spectral measure to be the sum of its atoms at the real Xi zeros.  Integrability is discharged
from Schwartz decay and temperate growth; it is not an extra hypothesis.
-/

open Complex Function MeasureTheory
open scoped FourierTransform SchwartzMap

namespace RHTower

noncomputable section

/-- The squared Xi norm is integrable against every temperate spectral measure once it is realized
as the Fourier transform of a Schwartz source. -/
theorem integrable_xiRealNormSq_of_fourier_eq_XiC
    (μ : Measure ℝ) [μ.HasTemperateGrowth]
    (k : 𝓢(ℝ, ℂ)) (hk : ∀ t : ℝ, 𝓕 k t = XiC (t : ℂ)) :
    Integrable xiRealNormSq μ := by
  let h : 𝓢(ℝ, ℂ) := SchwartzMap.pointwiseMulConj
    ((SchwartzMap.fourierTransformCLM ℂ) k)
    ((SchwartzMap.fourierTransformCLM ℂ) k)
  have hint : Integrable h μ := h.integrable
  exact hint.re.congr (by
    filter_upwards with t
    change (h t).re = xiRealNormSq t
    simp [h, hk, xiRealNormSq, Complex.mul_conj, Complex.sq_norm])

/-- Exact Xi energy formula for the spectral form of a Schwartz theta source. -/
theorem spectralMeasureForm_self_eq_integral_xiRealNormSq
    (μ : Measure ℝ) [μ.HasTemperateGrowth]
    (k : 𝓢(ℝ, ℂ)) (hk : ∀ t : ℝ, 𝓕 k t = XiC (t : ℂ)) :
    SchwartzMap.spectralMeasureForm μ k k =
      ∫ t, (xiRealNormSq t : ℂ) ∂μ := by
  rw [SchwartzMap.spectralMeasureForm_apply]
  apply integral_congr_ae
  filter_upwards with t
  rw [hk]
  simp [xiRealNormSq, Complex.mul_conj, Complex.sq_norm]

/-- A null Schwartz source with Fourier transform `XiC` forces the complete atomic Xi-zero
decomposition of its temperate spectral measure. -/
theorem spectralMeasure_eq_sum_smul_dirac_xiRealZeroSet_of_null_source
    (μ : Measure ℝ) [μ.HasTemperateGrowth]
    (k : 𝓢(ℝ, ℂ)) (hk : ∀ t : ℝ, 𝓕 k t = XiC (t : ℂ))
    (hnull : SchwartzMap.spectralMeasureForm μ k k = 0) :
    μ = Measure.sum
      (fun t : xiRealZeroSet => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) := by
  have hint := integrable_xiRealNormSq_of_fourier_eq_XiC μ k hk
  apply measure_eq_sum_smul_dirac_xiRealZeroSet_of_integral_normSq_eq_zero μ hint
  have hcomplex : (∫ t, (xiRealNormSq t : ℂ) ∂μ) = 0 := by
    rw [← spectralMeasureForm_self_eq_integral_xiRealNormSq μ k hk]
    exact hnull
  rw [integral_complex_ofReal] at hcomplex
  exact_mod_cast hcomplex

end

end RHTower
