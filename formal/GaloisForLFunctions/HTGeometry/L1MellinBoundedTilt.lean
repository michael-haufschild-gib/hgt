import GaloisForLFunctions.HTGeometry.L1FourierCompactUniformDecay
import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier

/-!
# Bounded Mellin tilts on a fixed logarithmic aperture

For profiles supported in `[-A,A]`, multiplication by `exp(δx)` is a bounded `L¹` operation. We
realize it globally by cutting the exponential symbol to the aperture. The resulting continuous
linear map agrees almost everywhere with the uncut Mellin tilt on every aperture-supported profile.

Combining the positive and negative tilts with compact-uniform `L¹` Fourier decay gives the exact
fourfold remote-quartet defect used in the compact-detector alternative.
-/

open MeasureTheory Filter Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Exponential Mellin tilt cut to the fixed logarithmic aperture `[-A,A]`. -/
def logMellinCutoffExpTilt (A δ x : ℝ) : ℂ :=
  Set.indicator (Set.Icc (-A) A) (fun y : ℝ => (Real.exp (δ * y) : ℂ)) x

theorem measurable_logMellinCutoffExpTilt (A δ : ℝ) :
    Measurable (logMellinCutoffExpTilt A δ) := by
  unfold logMellinCutoffExpTilt
  exact (Complex.measurable_ofReal.comp
    (Real.measurable_exp.comp (measurable_const.mul measurable_id))).indicator measurableSet_Icc

/-- Uniform bound for the cut exponential symbol. The assertion is valid even for `A < 0`, when
the aperture is empty. -/
theorem norm_logMellinCutoffExpTilt_le (A δ : ℝ) (x : ℝ) :
    ‖logMellinCutoffExpTilt A δ x‖ ≤ Real.exp (|δ| * A) := by
  by_cases hx : x ∈ Set.Icc (-A) A
  · rw [logMellinCutoffExpTilt, Set.indicator_of_mem hx, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have habsx : |x| ≤ A := (abs_le).2 hx
    calc
      δ * x ≤ |δ * x| := le_abs_self _
      _ = |δ| * |x| := abs_mul _ _
      _ ≤ |δ| * A := mul_le_mul_of_nonneg_left habsx (abs_nonneg _)
  · simp only [logMellinCutoffExpTilt, Set.indicator, hx, ↓reduceIte, norm_zero]
    exact (Real.exp_pos _).le

/-- Bounded exponential Mellin tilt as a continuous linear endomorphism of `L¹(ℝ)`. -/
def logMellinBoundedTilt (A δ : ℝ) : LogMellinL1 →L[ℂ] LogMellinL1 :=
  MeasureTheory.lpBoundedMulCLM (p := (1 : ENNReal))
    (measurable_logMellinCutoffExpTilt A δ) (Real.exp_pos _).le
    (norm_logMellinCutoffExpTilt_le A δ)

/-- The `L¹` profile vanishes almost everywhere outside the fixed logarithmic aperture. -/
def SupportedInLogAperture (A : ℝ) (f : LogMellinL1) : Prop :=
  ∀ᵐ x : ℝ, x ∉ Set.Icc (-A) A → f x = 0

/-- On an aperture-supported profile, the bounded global operator is exactly multiplication by
the uncut exponential Mellin tilt. -/
theorem logMellinBoundedTilt_coeFn_of_supported
    (A δ : ℝ) (f : LogMellinL1) (hf : SupportedInLogAperture A f) :
    ((logMellinBoundedTilt A δ f : LogMellinL1) : ℝ → ℂ) =ᵐ[volume]
      fun x => (Real.exp (δ * x) : ℂ) * f x := by
  have hcoe := MeasureTheory.lpBoundedMulCLM_coeFn
    (p := (1 : ENNReal)) (μ := (volume : Measure ℝ))
    (measurable_logMellinCutoffExpTilt A δ) (Real.exp_pos _).le
    (norm_logMellinCutoffExpTilt_le A δ) f
  filter_upwards [hcoe, hf] with x hx hfx
  have hx' :
      (((logMellinBoundedTilt A δ f : LogMellinL1) : ℝ → ℂ) x) =
        logMellinCutoffExpTilt A δ x * f x := by
    simpa only [logMellinBoundedTilt] using hx
  by_cases hxin : x ∈ Set.Icc (-A) A
  · simpa [logMellinCutoffExpTilt, hxin] using hx'
  · rw [hx', hfx hxin]
    simp [logMellinCutoffExpTilt, hxin]

/-- Exact compact-uniform remote-quartet decay for opposite bounded Mellin tilts. -/
theorem compact_logMellinBoundedTilt_quartetDefect_uniformVanishes
    (A δ : ℝ) {K : Set LogMellinL1} (hK : IsCompact K) :
    UniformlyVanishesAlong (cocompact ℝ) K
      (fun t f =>
        (4 * (logMellinL1Fourier (logMellinBoundedTilt A δ f) t *
          logMellinL1Fourier (logMellinBoundedTilt A (-δ) f) t).re : ℝ)) :=
  compact_logMellinL1Fourier_quartetDefect_uniformVanishes
    (logMellinBoundedTilt A δ) (logMellinBoundedTilt A (-δ)) hK

end

end GaloisForLFunctions.HTGeometry
