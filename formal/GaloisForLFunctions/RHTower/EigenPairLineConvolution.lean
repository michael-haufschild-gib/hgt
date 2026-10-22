import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmLineTransformBridge
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularFourier

/-!
# The eigen-pair line product as one Fourier transform of a convolution

On a horizontal line the eigen-pair product — one transform times the conjugate of the
reflected-height transform — is a single mathlib Fourier transform of the convolution of the
two tilted time-side flows.  Ingredients: the convention bridge, the hypothesis-free
conjugation–reflection law for the Fourier integral, and the corpus's `L¹` convolution theorem.

This is stage 5a-3a of the eigen-pair assembly: with the pair-line expressed as `𝓕(f₁ ⋆ f₂)`,
the frequency integrals of the termwise von Mangoldt swap become Fourier inversions at the
points `±log n`.
-/

namespace RHTower

noncomputable section

open MeasureTheory Complex FourierTransform Convolution

/-- Conjugation of an integrable function is integrable. -/
theorem integrable_conj_comp {g : ℝ → ℂ} (hg : Integrable g) :
    Integrable (fun x : ℝ => (starRingEnd ℂ) (g x)) := by
  refine ⟨Complex.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable, ?_⟩
  have h := hg.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_norm] at h ⊢
  simpa [RCLike.norm_conj] using h

/-- **Conjugation–reflection law for the Fourier integral**, hypothesis-free: the transform of
`x ↦ conj (g (−x))` is the conjugate of the transform of `g`. -/
theorem fourier_conj_reflect (g : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (starRingEnd ℂ) (g (-x))) ξ = (starRingEnd ℂ) (𝓕 g ξ) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq, ← integral_conj]
  rw [← integral_neg_eq_self
    (fun v : ℝ => (starRingEnd ℂ) (Real.fourierChar (-(v * ξ)) • g v)) volume]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  show Real.fourierChar (-(v * ξ)) • (starRingEnd ℂ) (g (-v)) =
    (starRingEnd ℂ) (Real.fourierChar (-(-v * ξ)) • g (-v))
  rw [Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, map_mul]
  congr 1
  rw [Real.fourierChar_apply, Real.fourierChar_apply, ← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring

/-- Tilted integrability of the causal Volterra flow, in real-tilt form. -/
theorem integrable_hedenmalm_realTilt {α : ℂ} (hα : |α.im| < 1) (h0 : XiC α = 0)
    {b : ℝ} (hb : |b| < 1) :
    Integrable (fun x : ℝ => hedenmalmCausalVolterra α x * Complex.exp ((b : ℂ) * (x : ℂ))) := by
  have hz : |((b : ℝ) * Complex.I : ℂ).im| < 1 := by
    simpa using hb
  have h := integrable_hedenmalmThetaEigen_mul_exp hα h0 (z := (b : ℝ) * Complex.I) hz
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  show hedenmalmCausalVolterra α x * Complex.exp (-I * ((b : ℝ) * Complex.I) * (x : ℂ)) =
      hedenmalmCausalVolterra α x * Complex.exp ((b : ℂ) * (x : ℂ))
  congr 2
  linear_combination (-(b : ℂ) * (x : ℂ)) * Complex.I_sq

/-- **The eigen-pair line product is one transform of a convolution.**  For zeros `α, β` and a
line height `|Y| < 1`, at every real frequency `t`:
the transform at `t − iY` times the conjugated transform at `t + iY` equals the Fourier
transform, at `t/(2π)`, of the convolution of the `−Y`-tilted flow of `α` with the
conjugate-reflected `Y`-tilted flow of `β`. -/
theorem transform_pair_line_eq_fourier_convolution {α β : ℂ}
    (hα : |α.im| < 1) (h0α : XiC α = 0) (hβ : |β.im| < 1) (h0β : XiC β = 0)
    {Y : ℝ} (hY : |Y| < 1) (t : ℝ) :
    hedenmalmThetaEigenTransform α ((t : ℂ) - (Y : ℂ) * Complex.I) *
      (starRingEnd ℂ) (hedenmalmThetaEigenTransform β ((t : ℂ) + (Y : ℂ) * Complex.I)) =
    𝓕 ((fun x : ℝ => hedenmalmCausalVolterra α x * Complex.exp (((-Y : ℝ) : ℂ) * (x : ℂ)))
        ⋆[ContinuousLinearMap.mul ℂ ℂ]
       (fun x : ℝ => (starRingEnd ℂ)
          (hedenmalmCausalVolterra β (-x) * Complex.exp ((Y : ℂ) * ((-x : ℝ) : ℂ)))))
      (t / (2 * Real.pi)) := by
  have him₁ : ((t : ℂ) - (Y : ℂ) * Complex.I).im = -Y := by simp
  have hre₁ : ((t : ℂ) - (Y : ℂ) * Complex.I).re = t := by simp
  have him₂ : ((t : ℂ) + (Y : ℂ) * Complex.I).im = Y := by simp
  have hre₂ : ((t : ℂ) + (Y : ℂ) * Complex.I).re = t := by simp
  have hf₁ : Integrable
      (fun x : ℝ => hedenmalmCausalVolterra α x * Complex.exp (((-Y : ℝ) : ℂ) * (x : ℂ))) :=
    integrable_hedenmalm_realTilt hα h0α (by rwa [abs_neg])
  have hg₂ : Integrable
      (fun x : ℝ => hedenmalmCausalVolterra β x * Complex.exp ((Y : ℂ) * (x : ℂ))) :=
    integrable_hedenmalm_realTilt hβ h0β hY
  have hf₂ : Integrable
      (fun x : ℝ => (starRingEnd ℂ)
        (hedenmalmCausalVolterra β (-x) * Complex.exp ((Y : ℂ) * ((-x : ℝ) : ℂ)))) :=
    integrable_conj_comp hg₂.comp_neg
  rw [hedenmalmThetaEigenTransform_eq_fourier α ((t : ℂ) - (Y : ℂ) * Complex.I),
    hedenmalmThetaEigenTransform_eq_fourier β ((t : ℂ) + (Y : ℂ) * Complex.I)]
  simp only [him₁, hre₁, him₂, hre₂]
  rw [← fourier_conj_reflect
    (fun x : ℝ => hedenmalmCausalVolterra β x * Complex.exp ((Y : ℂ) * (x : ℂ)))
    (t / (2 * Real.pi))]
  rw [← Real.fourier_mul_convolution_eq_L1 hf₁ hf₂ (t / (2 * Real.pi))]

end

end RHTower
