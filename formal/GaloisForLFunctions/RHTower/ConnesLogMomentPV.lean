import GaloisForLFunctions.RHTower.ConnesLogMomentVanishing
import GaloisForLFunctions.RHTower.ConnesSgnFourierKernel

/-!
# The regularized principal value on functions vanishing at the origin

For a Schwartz `φ` with `φ(0) = 0` Connes' logarithmically regularized principal value converges,
and its limit is the Fourier log moment.  This is the "away from the origin" half of the last §V
identification of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068;

the `δ`-coefficient is invisible here and is fixed separately by the Gaussian.
-/

open MeasureTheory Set Filter Topology FourierTransform
open scoped FourierTransform SchwartzMap

namespace GaloisForLFunctions.RHTower

noncomputable section

theorem connes_sign_mul_integrable (ψ : 𝓢(ℝ, ℂ)) :
    Integrable (fun x : ℝ => (Real.sign x : ℂ) * (ψ : ℝ → ℂ) x) volume := by
  refine Integrable.mono' (ψ.integrable (μ := volume)).norm ?_ ?_
  · exact ((Complex.measurable_ofReal.comp connes_measurable_sign).aestronglyMeasurable).mul
      ψ.continuous.aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul]
    have h1 : ‖((Real.sign x : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact connes_abs_sign_le_one x
    have h2 := mul_le_mul_of_nonneg_right h1 (norm_nonneg ((ψ : ℝ → ℂ) x))
    rwa [one_mul] at h2

/-- The multiplicative-Haar integrand of a Schwartz function vanishing at the origin is
integrable. -/
theorem connes_haar_integrable_of_zero (φ : 𝓢(ℝ, ℂ)) (h0 : (φ : ℝ → ℂ) 0 = 0) :
    Integrable (fun x : ℝ => (φ : ℝ → ℂ) x * ((connesRealMultHaarDensity x : ℝ) : ℂ)) volume := by
  have hfun : (fun x : ℝ => (φ : ℝ → ℂ) x * ((connesRealMultHaarDensity x : ℝ) : ℂ))
      = fun x : ℝ => (Real.sign x : ℂ)
          * ((connesHadamardQuotient φ h0 : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x / 2 :=
    funext (connes_sign_haar_pointwise φ h0)
  rw [hfun]
  exact (connes_sign_mul_integrable (connesHadamardQuotient φ h0)).div_const 2

/-- **The regularized principal value converges on functions vanishing at the origin**, to the
Fourier log moment. -/
theorem connes_logPV_tendsto_of_zero (φ : 𝓢(ℝ, ℂ)) (h0 : (φ : ℝ → ℂ) 0 = 0) :
    Tendsto (fun ε : ℝ => connesRealLogPV ((φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ε) (𝓝[>] 0)
      (𝓝 (- ∫ u : ℝ, 𝓕 ((φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ))) := by
  have h := connesRealLogPV_tendsto_of_zero (f := ((φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) h0
    (connes_haar_integrable_of_zero φ h0)
  rwa [connes_logMoment_of_zero φ h0]

end

end GaloisForLFunctions.RHTower
