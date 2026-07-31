/-
BRIDGE (classical harmonic-analysis infrastructure).

Reflection on `L²(ℝ)` commutes with the unitary Fourier transform.  The proof establishes the
identity on Schwartz functions by the change-of-variables formula and extends it by density.
-/
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.FourierTransform

noncomputable section

open MeasureTheory FourierTransform SchwartzMap
open scoped ENNReal

namespace RHTower

abbrev FourierRealL2 := Lp (α := ℝ) ℂ 2

/-- Reflection `f(x) ↦ f(-x)` as a linear isometry on `L²(ℝ)`. -/
def l2ReflectionIsometry : FourierRealL2 →ₗᵢ[ℂ] FourierRealL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => -x)
    (Measure.measurePreserving_neg (volume : Measure ℝ))

/-- Reflection `f(x) ↦ f(-x)` as a continuous linear operator on `L²(ℝ)`. -/
def l2Reflection : FourierRealL2 →L[ℂ] FourierRealL2 :=
  l2ReflectionIsometry.toContinuousLinearMap

private def negSchwartz (g : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv) g

private theorem l2Reflection_toLp (g : SchwartzMap ℝ ℂ) :
    l2Reflection (g.toLp 2) = (negSchwartz g).toLp 2 := by
  rfl

private theorem fourier_negSchwartz (g : SchwartzMap ℝ ℂ) :
    𝓕 (negSchwartz g) = negSchwartz (𝓕 g) := by
  ext x
  exact Real.fourier_comp_linearIsometry
    (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) g x

private theorem fourier_l2Reflection_toLp (g : SchwartzMap ℝ ℂ) :
    𝓕 (l2Reflection (g.toLp 2)) = l2Reflection (𝓕 (g.toLp 2)) := by
  rw [l2Reflection_toLp, SchwartzMap.toLp_fourier_eq]
  rw [fourier_negSchwartz, SchwartzMap.toLp_fourier_eq, l2Reflection_toLp]

/-- The unitary Fourier transform on `L²(ℝ)` commutes with reflection. -/
theorem l2_fourier_reflection (f : FourierRealL2) :
    (Lp.fourierTransformₗᵢ ℝ ℂ) (l2Reflection f) =
      l2Reflection ((Lp.fourierTransformₗᵢ ℝ ℂ) f) := by
  let p : FourierRealL2 → Prop := fun f =>
    (Lp.fourierTransformₗᵢ ℝ ℂ) (l2Reflection f) =
      l2Reflection ((Lp.fourierTransformₗᵢ ℝ ℂ) f)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact (Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp l2Reflection.continuous
    · exact l2Reflection.continuous.comp (Lp.fourierTransformₗᵢ ℝ ℂ).continuous
  · exact fourier_l2Reflection_toLp

private theorem negSchwartz_negSchwartz (g : SchwartzMap ℝ ℂ) :
    negSchwartz (negSchwartz g) = g := by
  ext x
  show g (-(-x)) = g x
  rw [neg_neg]

private theorem fourier_fourier_schwartz (g : SchwartzMap ℝ ℂ) :
    𝓕 (𝓕 g) = negSchwartz g := by
  have h : 𝓕⁻ (𝓕 g) = g := fourierInv_fourier_eq g
  rw [SchwartzMap.fourierInv_apply_eq] at h
  calc 𝓕 (𝓕 g) = negSchwartz (negSchwartz (𝓕 (𝓕 g))) :=
        (negSchwartz_negSchwartz _).symm
    _ = negSchwartz g := congrArg negSchwartz h

private theorem fourier_fourier_toLp (g : SchwartzMap ℝ ℂ) :
    𝓕 (𝓕 (g.toLp 2)) = l2Reflection (g.toLp 2) := by
  rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq, l2Reflection_toLp,
    fourier_fourier_schwartz]

/-- **The unitary Fourier transform on `L²(ℝ)` squares to reflection.**  Fourier inversion on
Schwartz functions, extended by density. -/
theorem l2_fourier_fourier (f : FourierRealL2) :
    (Lp.fourierTransformₗᵢ ℝ ℂ) ((Lp.fourierTransformₗᵢ ℝ ℂ) f) = l2Reflection f := by
  let p : FourierRealL2 → Prop := fun f =>
    (Lp.fourierTransformₗᵢ ℝ ℂ) ((Lp.fourierTransformₗᵢ ℝ ℂ) f) = l2Reflection f
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact (Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp (Lp.fourierTransformₗᵢ ℝ ℂ).continuous
    · exact l2Reflection.continuous
  · exact fourier_fourier_toLp

end RHTower
