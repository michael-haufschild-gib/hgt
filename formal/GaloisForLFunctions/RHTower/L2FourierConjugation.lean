/-
BRIDGE (classical harmonic-analysis infrastructure).

Complex conjugation turns the unitary Fourier transform on `L²(ℝ)` into its inverse:

```text
star (𝖥 (star f)) = l2Reflection (𝖥 f).
```

Pointwise this is `conj (∫ f(x) e^{-2πixξ} dx) = ∫ conj (f x) e^{2πixξ} dx`, established on Schwartz
functions and extended by density.

Two supporting gaps are filled here.  `𝓢(ℝ, ℂ)` carries no `Star` instance in mathlib, so the
conjugate Schwartz function is built by postcomposing with `Complex.conjLIE`, whose isometry makes
every Schwartz seminorm bound transfer unchanged.  And `Lp ℂ 2 volume` has a `Star` operation but
no synthesizable `StarAddMonoid`, so additivity and the norm identity for `star` are proved
directly from `Lp.coeFn_star`.
-/
import GaloisForLFunctions.RHTower.L2FourierReflection
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

noncomputable section

open MeasureTheory FourierTransform SchwartzMap Real
open scoped ENNReal

namespace RHTower

/-- Conjugating the datum of a Fourier integral reflects the frequency. -/
theorem conj_fourierIntegral_conj (g : ℝ → ℂ) (ξ : ℝ) :
    (starRingEnd ℂ) (𝓕 (fun x => (starRingEnd ℂ) (g x)) ξ) = 𝓕 g (-ξ) := by
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_conj]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [Circle.smul_def, Real.fourierChar_apply, ← Complex.exp_conj]
  left
  congr 2
  rw [map_ofNat]

/-- Complex conjugation of a Schwartz function. -/
def starSchwartz (g : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ where
  toFun := fun x => (starRingEnd ℂ) (g x)
  smooth' := Complex.conjCLE.contDiff.comp g.smooth'
  decay' := by
    intro k n
    obtain ⟨C, hC⟩ := g.decay' k n
    refine ⟨C, fun x => ?_⟩
    have hiter : iteratedFDeriv ℝ n
        (⇑(Complex.conjLIE.toLinearIsometry.toContinuousLinearMap) ∘ g.toFun) x
        = (Complex.conjLIE.toLinearIsometry.toContinuousLinearMap).compContinuousMultilinearMap
            (iteratedFDeriv ℝ n g.toFun x) :=
      ContinuousLinearMap.iteratedFDeriv_comp_left _ (g.smooth'.contDiffAt) (by exact_mod_cast le_top)
    show ‖x‖ ^ k * ‖iteratedFDeriv ℝ n
        (⇑(Complex.conjLIE.toLinearIsometry.toContinuousLinearMap) ∘ g.toFun) x‖ ≤ C
    rw [hiter, LinearIsometry.norm_compContinuousMultilinearMap]
    exact hC x

@[simp] theorem starSchwartz_apply (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    starSchwartz g x = (starRingEnd ℂ) (g x) := rfl

/-- Reflection of a Schwartz function. -/
def negSchwartz' (g : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv) g

@[simp] theorem negSchwartz'_apply (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    negSchwartz' g x = g (-x) := rfl

theorem l2Reflection_toLp' (g : SchwartzMap ℝ ℂ) :
    l2Reflection (g.toLp 2) = (negSchwartz' g).toLp 2 := rfl

theorem star_toLp (g : SchwartzMap ℝ ℂ) :
    star (g.toLp (μ := (volume : Measure ℝ)) 2) = (starSchwartz g).toLp 2 := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [MeasureTheory.Lp.coeFn_star (g.toLp (μ := (volume : Measure ℝ)) 2),
    SchwartzMap.coeFn_toLp (μ := (volume : Measure ℝ)) (p := 2) g,
    SchwartzMap.coeFn_toLp (μ := (volume : Measure ℝ)) (p := 2) (starSchwartz g)] with x h1 h2 h3
  rw [h1, Pi.star_apply, h2, h3, starSchwartz_apply]
  rfl

theorem norm_lpStar (f : Lp ℂ 2 (volume : Measure ℝ)) : ‖star f‖ = ‖f‖ := by
  rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def]
  congr 1
  refine MeasureTheory.eLpNorm_congr_ae (MeasureTheory.Lp.coeFn_star f) |>.trans ?_
  exact MeasureTheory.eLpNorm_star

theorem continuous_lpStar :
    Continuous (fun f : Lp ℂ 2 (volume : Measure ℝ) => star f) := by
  refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun f g => ?_)
  have hsub : star f - star g = star (f - g) := by
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [MeasureTheory.Lp.coeFn_sub (star f) (star g),
      MeasureTheory.Lp.coeFn_star f, MeasureTheory.Lp.coeFn_star g,
      MeasureTheory.Lp.coeFn_star (f - g), MeasureTheory.Lp.coeFn_sub f g] with x h1 h2 h3 h4 h5
    simp only [h1, h4, Pi.sub_apply, Pi.star_apply, h2, h3, h5]
    exact (star_sub _ _).symm
  rw [dist_eq_norm, dist_eq_norm, hsub, norm_lpStar]
  simp

/-- **Conjugation converts the Fourier transform into its inverse.**  On `L²(ℝ)` the map
`f ↦ star (𝖥 (star f))` is the reflected Fourier transform, i.e. the inverse transform. -/
theorem star_fourier_star (f : Lp ℂ 2 (volume : Measure ℝ)) :
    star ((Lp.fourierTransformₗᵢ ℝ ℂ) (star f))
      = l2Reflection ((Lp.fourierTransformₗᵢ ℝ ℂ) f) := by
  let p : Lp ℂ 2 (volume : Measure ℝ) → Prop := fun f =>
    star ((Lp.fourierTransformₗᵢ ℝ ℂ) (star f))
      = l2Reflection ((Lp.fourierTransformₗᵢ ℝ ℂ) f)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact continuous_lpStar.comp
        ((Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp continuous_lpStar)
    · exact l2Reflection.continuous.comp (Lp.fourierTransformₗᵢ ℝ ℂ).continuous
  · intro g
    show star ((Lp.fourierTransformₗᵢ ℝ ℂ) (star (g.toLp 2)))
      = l2Reflection ((Lp.fourierTransformₗᵢ ℝ ℂ) (g.toLp 2))
    rw [star_toLp g]
    have h2 : (Lp.fourierTransformₗᵢ ℝ ℂ) ((starSchwartz g).toLp (μ := (volume : Measure ℝ)) 2)
        = (𝓕 (starSchwartz g)).toLp 2 := SchwartzMap.toLp_fourier_eq _
    have h3 : (Lp.fourierTransformₗᵢ ℝ ℂ) (g.toLp (μ := (volume : Measure ℝ)) 2)
        = (𝓕 g).toLp 2 := SchwartzMap.toLp_fourier_eq _
    rw [h2, h3, star_toLp, l2Reflection_toLp']
    congr 1
    ext x
    exact conj_fourierIntegral_conj (fun y => g y) x

end RHTower
