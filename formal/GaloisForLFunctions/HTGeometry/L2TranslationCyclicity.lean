import GaloisForLFunctions.RHTower.RealCharacterDenseL2
import GaloisForLFunctions.RHTower.L2MellinUnitary

/-!
# Translation cyclicity from an almost-everywhere nonzero Fourier profile

Fourier uniqueness kills every continuous functional annihilating the character
orbit of an almost-everywhere nonzero L2 vector. Plancherel transports the result
to translations, without a lower bound on the Fourier profile.
-/

noncomputable section
open Complex MeasureTheory Set
open scoped FourierTransform SchwartzMap
namespace GaloisForLFunctions.HTGeometry
open RHTower RHTower.MellinL2

/-- An almost-everywhere nonzero L2 vector has dense character orbit. -/
theorem isCyclicFamily_fourierPhase_of_ae_ne_zero
    (f : Lp (α := ℝ) ℂ 2 volume) (hf : ∀ᵐ x : ℝ, f x ≠ 0) :
    IsCyclicFamily (𝕜 := ℂ) (fun a : ℝ => fourierPhaseMulUnitary a f) := by
  apply dense_span_of_forall_dual_eq_zero
  intro L hL
  let g : Lp (α := ℝ) ℂ 2 volume :=
    (InnerProductSpace.toDual ℂ (Lp (α := ℝ) ℂ 2 volume)).symm L
  have hinner (a : ℝ) : inner ℂ g (fourierPhaseMulUnitary a f) = 0 := by
    simpa only [g, InnerProductSpace.toDual_symm_apply] using hL a
  let F : ℝ → ℂ := fun x => inner ℂ (g x) (f x)
  have hFm : Measurable F :=
    ((Lp.stronglyMeasurable g).inner (Lp.stronglyMeasurable f)).measurable
  have hFi : Integrable F := L2.integrable_inner g f
  have hFourier (t : ℝ) : ∫ x, realProbCharacter t x * F x = 0 := by
    have ht := hinner (t / (2 * Real.pi))
    rw [L2.inner_def] at ht
    have hphase (x : ℝ) :
        fourierPhase (t / (2 * Real.pi)) x = realProbCharacter t x := by
      rw [fourierPhase, realProbCharacter, Real.fourierChar_apply]
      congr 1
      push_cast
      field_simp [Real.pi_ne_zero]
    have hpoint :
        (fun x : ℝ => inner ℂ (g x) (fourierPhaseMulUnitary (t / (2 * Real.pi)) f x)) =ᵐ[volume]
          fun x => realProbCharacter t x * F x := by
      filter_upwards [fourierPhaseMulAux_ae (t / (2 * Real.pi)) f] with x hx
      change inner ℂ (g x) (fourierPhaseMulAux (t / (2 * Real.pi)) f x) = _
      rw [hx, hphase]
      simp only [F, inner]
      ring
    rw [integral_congr_ae hpoint] at ht
    exact ht
  have hFzero := ae_eq_zero_of_integral_realProbCharacter_mul_eq_zero_complex
    (volume : Measure ℝ) hFm hFi hFourier
  have hgzero : g = 0 := by
    apply Lp.ext
    filter_upwards [hFzero, hf, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx hfx hz
    rw [hz]
    have hmul : f x * star (g x) = 0 := by simpa only [F, inner, Pi.zero_apply] using hx
    have hgstar : star (g x) = 0 := (mul_eq_zero.mp hmul).resolve_left hfx
    have he := congrArg star hgstar
    simpa only [star_star, star_zero, Pi.zero_apply] using he
  calc
    L = (InnerProductSpace.toDual ℂ (Lp (α := ℝ) ℂ 2 volume)) g := by
      symm
      exact (InnerProductSpace.toDual ℂ (Lp (α := ℝ) ℂ 2 volume)).apply_symm_apply L
    _ = 0 := by rw [hgzero]; simp only [map_zero]

/-- A nonvanishing Fourier profile makes the ordinary L2 translation orbit cyclic. -/
theorem isCyclicFamily_translation_of_fourier_ae_ne_zero
    (f : Lp (α := ℝ) ℂ 2 volume)
    (hf : ∀ᵐ x : ℝ, (𝓕 f : Lp (α := ℝ) ℂ 2 volume) x ≠ 0) :
    IsCyclicFamily (𝕜 := ℂ) (fun a : ℝ => additiveTranslationUnitary a f) := by
  apply dense_span_of_forall_dual_eq_zero
  intro L hL
  let LF : Lp (α := ℝ) ℂ 2 volume →L[ℂ] ℂ :=
    L.comp (Lp.fourierTransformₗᵢ ℝ ℂ).symm.toLinearIsometry.toContinuousLinearMap
  have hLF (a : ℝ) : LF (fourierPhaseMulUnitary a (𝓕 f)) = 0 := by
    change L ((Lp.fourierTransformₗᵢ ℝ ℂ).symm
      (fourierPhaseMulUnitary a (𝓕 f))) = 0
    rw [← fourier_additiveTranslation]
    change L ((Lp.fourierTransformₗᵢ ℝ ℂ).symm
      ((Lp.fourierTransformₗᵢ ℝ ℂ) (additiveTranslationUnitary a f))) = 0
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hL a
  have hzero := continuousLinearFunctional_eq_zero_of_isCyclicFamily
    (isCyclicFamily_fourierPhase_of_ae_ne_zero (𝓕 f) hf) LF hLF
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg
    (fun M : Lp (α := ℝ) ℂ 2 volume →L[ℂ] ℂ => M ((Lp.fourierTransformₗᵢ ℝ ℂ) x)) hzero
  change L ((Lp.fourierTransformₗᵢ ℝ ℂ).symm ((Lp.fourierTransformₗᵢ ℝ ℂ) x)) = 0 at hx
  simpa only [LinearIsometryEquiv.symm_apply_apply, ContinuousLinearMap.zero_apply] using hx

end GaloisForLFunctions.HTGeometry

