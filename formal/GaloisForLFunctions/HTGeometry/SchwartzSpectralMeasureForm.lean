import GaloisForLFunctions.HTGeometry.SchwartzProduct
import GaloisForLFunctions.HTGeometry.SchwartzSesquilinear
import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Spectral measures give continuous Schwartz forms

This is the converse, constructive half of the Bochner--Schwartz bridge needed by the Hedenmalm
metric card.  Every positive measure of temperate growth gives a jointly continuous sesquilinear
form by integrating the product of Fourier transforms.
-/

open Complex Filter Function MeasureTheory
open scoped FourierTransform SchwartzMap Topology

namespace SchwartzMap

noncomputable section

/-- The spectral form represented by a positive measure of temperate growth. -/
def spectralMeasureForm (μ : Measure ℝ) [μ.HasTemperateGrowth] :
    ContinuousSchwartzSesquilinearForm where
  toFun u v := (integralCLM ℂ μ)
    (pointwiseMulConj ((fourierTransformCLM ℂ) u) ((fourierTransformCLM ℂ) v))
  map_add_left u v w := by
    calc
      (integralCLM ℂ μ) (pointwiseMulConj
          ((fourierTransformCLM ℂ) (u + v)) ((fourierTransformCLM ℂ) w)) =
          (integralCLM ℂ μ)
            (pointwiseMulConj ((fourierTransformCLM ℂ) u) ((fourierTransformCLM ℂ) w) +
              pointwiseMulConj ((fourierTransformCLM ℂ) v) ((fourierTransformCLM ℂ) w)) := by
        congr 1
        rw [map_add, pointwiseMulConj_add_left]
      _ = _ := map_add (integralCLM ℂ μ) _ _
  map_smul_left c u v := by
    calc
      (integralCLM ℂ μ) (pointwiseMulConj
          ((fourierTransformCLM ℂ) (c • u)) ((fourierTransformCLM ℂ) v)) =
          (integralCLM ℂ μ) (c • pointwiseMulConj
            ((fourierTransformCLM ℂ) u) ((fourierTransformCLM ℂ) v)) := by
        congr 1
        rw [map_smul, pointwiseMulConj_smul_left]
      _ = c * (integralCLM ℂ μ) (pointwiseMulConj
          ((fourierTransformCLM ℂ) u) ((fourierTransformCLM ℂ) v)) := by
        rw [map_smul, smul_eq_mul]
  map_add_right u v w := by
    calc
      (integralCLM ℂ μ) (pointwiseMulConj
          ((fourierTransformCLM ℂ) u) ((fourierTransformCLM ℂ) (v + w))) =
          (integralCLM ℂ μ)
            (pointwiseMulConj ((fourierTransformCLM ℂ) u) ((fourierTransformCLM ℂ) v) +
              pointwiseMulConj ((fourierTransformCLM ℂ) u) ((fourierTransformCLM ℂ) w)) := by
        congr 1
        rw [map_add, pointwiseMulConj_add_right]
      _ = _ := map_add (integralCLM ℂ μ) _ _
  map_smul_right c u v := by
    calc
      (integralCLM ℂ μ) (pointwiseMulConj
          ((fourierTransformCLM ℂ) u) ((fourierTransformCLM ℂ) (c • v))) =
          (integralCLM ℂ μ)
            ((starRingEnd ℂ) c • pointwiseMulConj
              ((fourierTransformCLM ℂ) u) ((fourierTransformCLM ℂ) v)) := by
        congr 1
        rw [map_smul, pointwiseMulConj_smul_right]
      _ = (starRingEnd ℂ) c *
          (integralCLM ℂ μ) (pointwiseMulConj
            ((fourierTransformCLM ℂ) u) ((fourierTransformCLM ℂ) v)) := by
        rw [map_smul, smul_eq_mul]
  continuous := by
    have hfourier : Continuous
        (fun p : 𝓢(ℝ, ℂ) × 𝓢(ℝ, ℂ) =>
          ((fourierTransformCLM ℂ) p.1, (fourierTransformCLM ℂ) p.2)) :=
      ((fourierTransformCLM ℂ).continuous.comp continuous_fst).prodMk
        ((fourierTransformCLM ℂ).continuous.comp continuous_snd)
    have hproduct : Continuous
        (fun p : 𝓢(ℝ, ℂ) × 𝓢(ℝ, ℂ) => pointwiseMulConj p.1 p.2) :=
      continuous_pointwiseMulConj
    have hcombined : Continuous
        (fun p : 𝓢(ℝ, ℂ) × 𝓢(ℝ, ℂ) =>
          pointwiseMulConj ((fourierTransformCLM ℂ) p.1)
            ((fourierTransformCLM ℂ) p.2)) := hproduct.comp hfourier
    change Continuous (fun p : 𝓢(ℝ, ℂ) × 𝓢(ℝ, ℂ) =>
      (integralCLM ℂ μ) (pointwiseMulConj ((fourierTransformCLM ℂ) p.1)
        ((fourierTransformCLM ℂ) p.2)))
    exact (integralCLM ℂ μ).continuous.comp hcombined

theorem spectralMeasureForm_apply (μ : Measure ℝ) [μ.HasTemperateGrowth]
    (u v : 𝓢(ℝ, ℂ)) :
    spectralMeasureForm μ u v =
      ∫ t, 𝓕 u t * (starRingEnd ℂ) (𝓕 v t) ∂μ := by
  change (integralCLM ℂ μ) (pointwiseMulConj
    ((fourierTransformCLM ℂ) u) ((fourierTransformCLM ℂ) v)) = _
  rw [integralCLM_apply]
  rfl

/-- Every positive spectral measure gives a nonnegative Schwartz form. -/
theorem spectralMeasureForm_isNonnegative (μ : Measure ℝ) [μ.HasTemperateGrowth] :
    (spectralMeasureForm μ).IsNonnegative := by
  intro u
  rw [spectralMeasureForm_apply]
  let h : 𝓢(ℝ, ℂ) := pointwiseMulConj
    ((fourierTransformCLM ℂ) u) ((fourierTransformCLM ℂ) u)
  have hint : Integrable h μ := h.integrable
  have heq : (fun t : ℝ => 𝓕 u t * (starRingEnd ℂ) (𝓕 u t)) = h := by
    funext t
    rfl
  constructor
  · rw [heq]
    change 0 ≤ RCLike.re (∫ t, h t ∂μ)
    rw [← integral_re hint]
    apply integral_nonneg
    intro t
    change 0 ≤ (h t).re
    simp [h, Complex.mul_conj, Complex.normSq]
    nlinarith [sq_nonneg ((𝓕 u t).re), sq_nonneg ((𝓕 u t).im)]
  · rw [heq]
    change RCLike.im (∫ t, h t ∂μ) = 0
    rw [← integral_im hint]
    apply integral_eq_zero_of_ae
    filter_upwards with t
    change (h t).im = 0
    simp [h, Complex.mul_conj]

theorem spectralMeasureForm_isHermitian (μ : Measure ℝ) [μ.HasTemperateGrowth] :
    (spectralMeasureForm μ).IsHermitian :=
  (spectralMeasureForm μ).isHermitian_of_isNonnegative
    (spectralMeasureForm_isNonnegative μ)

/-- Under Fourier transform, the momentum generator `-i d/dx` is multiplication by the real
spectral coordinate `2πt`. -/
theorem fourier_negI_deriv_apply (u : 𝓢(ℝ, ℂ)) (t : ℝ) :
    (fourierTransformCLM ℂ ((-I) • derivCLM ℂ ℂ u)) t =
      ((2 * Real.pi * t : ℝ) : ℂ) * (fourierTransformCLM ℂ u) t := by
  rw [map_smul]
  change (-I) * (fourierTransformCLM ℂ (derivCLM ℂ ℂ u)) t = _
  have h := congrFun (Real.fourier_deriv u.integrable u.differentiable
    (derivCLM ℂ ℂ u).integrable) t
  have hderivfun : deriv (u : ℝ → ℂ) = (derivCLM ℂ ℂ u : ℝ → ℂ) := by
    funext x
    rfl
  have h' : (fourierTransformCLM ℂ (derivCLM ℂ ℂ u)) t =
      (2 * Real.pi * I * (t : ℂ)) * (fourierTransformCLM ℂ u) t := by
    rw [fourierTransformCLM_apply, fourierTransformCLM_apply,
      SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
    rw [← hderivfun]
    simpa only [smul_eq_mul] using h
  rw [h']
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Every positive tempered spectral measure symmetrizes the momentum generator. -/
theorem spectralMeasureForm_momentumSymmetric
    (μ : Measure ℝ) [μ.HasTemperateGrowth] :
    (spectralMeasureForm μ).MomentumSymmetric := by
  intro u v
  rw [spectralMeasureForm_apply, spectralMeasureForm_apply]
  apply integral_congr_ae
  filter_upwards with t
  change (fourierTransformCLM ℂ ((-I) • derivCLM ℂ ℂ u)) t *
      (starRingEnd ℂ) ((fourierTransformCLM ℂ v) t) =
    (fourierTransformCLM ℂ u) t *
      (starRingEnd ℂ) ((fourierTransformCLM ℂ ((-I) • derivCLM ℂ ℂ v)) t)
  rw [fourier_negI_deriv_apply, fourier_negI_deriv_apply]
  simp only [map_mul, Complex.conj_ofReal]
  ring

/-- The spectral form is invariant under simultaneous translation of both Schwartz arguments. -/
theorem spectralMeasureForm_translate_pair_invariant
    (μ : Measure ℝ) [μ.HasTemperateGrowth]
    (u v : 𝓢(ℝ, ℂ)) (a : ℝ) :
    spectralMeasureForm μ (translateCLM ℂ a u) (translateCLM ℂ a v) =
      spectralMeasureForm μ u v :=
  (spectralMeasureForm μ).translate_pair_invariant
    (spectralMeasureForm_momentumSymmetric μ) u v a

end

end SchwartzMap
