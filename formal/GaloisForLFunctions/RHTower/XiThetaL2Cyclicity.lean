import GaloisForLFunctions.RHTower.RealCharacterDenseL2
import GaloisForLFunctions.RHTower.L2MellinUnitary
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspSchwartzFourierXi

/-!
# Ordinary `L²` cyclicity of the Hedenmalm theta source

The normalized theta-cusp Schwartz source has Fourier transform `XiC`, whose
real zero set is Lebesgue-null.  Fourier uniqueness therefore makes its
character orbit dense in `L²`; Plancherel transports this to the translation
orbit of the physical theta source.
-/

open Complex MeasureTheory Set
open scoped FourierTransform SchwartzMap

namespace RHTower

open MellinL2

noncomputable section

/-- The normalized Hedenmalm theta source in ordinary complex `L²`. -/
def xiThetaSourceL2 : Lp (α := ℝ) ℂ 2 volume :=
  xiThetaSchwartzSource.toLp 2 volume

/-- Its exact Schwartz Fourier profile as an `L²` vector. -/
def xiThetaFourierSourceL2 : Lp (α := ℝ) ℂ 2 volume :=
  (𝓕 xiThetaSchwartzSource).toLp 2 volume

/-- The Fourier-character orbit of the completed theta source. -/
def xiThetaFourierPhaseOrbit (a : ℝ) : Lp (α := ℝ) ℂ 2 volume :=
  fourierPhaseMulUnitary a xiThetaFourierSourceL2

/-- The physical translation orbit of the completed theta source. -/
def xiThetaTranslationOrbit (a : ℝ) : Lp (α := ℝ) ℂ 2 volume :=
  additiveTranslationUnitary a xiThetaSourceL2

/-- The `L²` Fourier profile is almost everywhere the actual centered
completed function on the real spectral axis. -/
theorem xiThetaFourierSourceL2_ae :
    xiThetaFourierSourceL2 =ᵐ[volume] fun t : ℝ ↦ XiC (t : ℂ) := by
  filter_upwards [(𝓕 xiThetaSchwartzSource).coeFn_toLp
    (p := 2) (μ := (volume : Measure ℝ))] with t ht
  rw [xiThetaFourierSourceL2, ht, fourier_xiThetaSchwartzSource]

/-- The probability-character and mathlib Fourier-character conventions
agree after the exact frequency rescaling. -/
theorem fourierPhase_div_twoPi_eq_realProbCharacter (t x : ℝ) :
    fourierPhase (t / (2 * Real.pi)) x = realProbCharacter t x := by
  rw [fourierPhase, realProbCharacter, Real.fourierChar_apply]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- The all-height Fourier-character orbit of the completed theta source is
cyclic in ordinary `L²`. -/
theorem isCyclicFamily_xiThetaFourierPhaseOrbit :
    IsCyclicFamily (𝕜 := ℂ) xiThetaFourierPhaseOrbit := by
  apply dense_span_of_forall_dual_eq_zero
  intro L hL
  let g : Lp (α := ℝ) ℂ 2 volume :=
    (InnerProductSpace.toDual ℂ (Lp (α := ℝ) ℂ 2 volume)).symm L
  have hinner (a : ℝ) : inner ℂ g (xiThetaFourierPhaseOrbit a) = 0 := by
    have h := hL a
    change L (xiThetaFourierPhaseOrbit a) = 0 at h
    simpa [g, InnerProductSpace.toDual_symm_apply] using h
  let f : ℝ → ℂ := fun x ↦ inner ℂ (g x) (xiThetaFourierSourceL2 x)
  have hfmeas : Measurable f := by
    exact ((Lp.stronglyMeasurable g).inner
      (Lp.stronglyMeasurable xiThetaFourierSourceL2)).measurable
  have hfint : Integrable f := by
    exact L2.integrable_inner g xiThetaFourierSourceL2
  have hfourier (t : ℝ) :
      ∫ x, realProbCharacter t x * f x = 0 := by
    let a : ℝ := t / (2 * Real.pi)
    have ht := hinner a
    rw [L2.inner_def] at ht
    have hpoint :
        (fun x : ℝ ↦ inner ℂ (g x) (xiThetaFourierPhaseOrbit a x)) =ᵐ[volume]
          fun x ↦ realProbCharacter t x * f x := by
      filter_upwards [fourierPhaseMulAux_ae a xiThetaFourierSourceL2] with x hx
      change inner ℂ (g x) (fourierPhaseMulAux a xiThetaFourierSourceL2 x) = _
      rw [hx, fourierPhase_div_twoPi_eq_realProbCharacter]
      simp only [f, inner]
      ring
    rw [integral_congr_ae hpoint] at ht
    exact ht
  have hfzero :=
    ae_eq_zero_of_integral_realProbCharacter_mul_eq_zero_complex
      (volume : Measure ℝ) hfmeas hfint hfourier
  have hgzero : g = 0 := by
    apply Lp.ext
    filter_upwards [hfzero, xiThetaFourierSourceL2_ae,
      ae_XiC_ofReal_ne_zero, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)]
      with x hfx hprofile hxi hzero
    rw [hzero]
    have hmul : XiC (x : ℂ) * (starRingEnd ℂ) (g x) = 0 := by
      simpa [f, hprofile] using hfx
    have hgstar : (starRingEnd ℂ) (g x) = 0 :=
      (mul_eq_zero.mp hmul).resolve_left hxi
    have := congrArg (starRingEnd ℂ) hgstar
    simpa using this
  calc
    L = (InnerProductSpace.toDual ℂ (Lp (α := ℝ) ℂ 2 volume)) g := by
      symm
      exact (InnerProductSpace.toDual ℂ
        (Lp (α := ℝ) ℂ 2 volume)).apply_symm_apply L
    _ = 0 := by rw [hgzero]; simp

/-- Plancherel sends the normalized physical theta source to its displayed
Schwartz Fourier profile. -/
theorem fourier_xiThetaSourceL2 :
    𝓕 xiThetaSourceL2 = xiThetaFourierSourceL2 := by
  rw [xiThetaSourceL2, xiThetaFourierSourceL2,
    SchwartzMap.toLp_fourier_eq]

/-- Translation of the physical theta source is exactly the phase orbit after
the `L²` Fourier equivalence. -/
theorem fourier_xiThetaTranslationOrbit (a : ℝ) :
    𝓕 (xiThetaTranslationOrbit a) = xiThetaFourierPhaseOrbit a := by
  rw [xiThetaTranslationOrbit, xiThetaFourierPhaseOrbit,
    fourier_additiveTranslation, fourier_xiThetaSourceL2]

/-- **Ordinary `L²` Wiener cyclicity of the Hedenmalm theta source.**  The
closed complex linear span of all real translations of the normalized
theta-cusp source is the whole ambient `L²(R)`. -/
theorem isCyclicFamily_xiThetaTranslationOrbit :
    IsCyclicFamily (𝕜 := ℂ) xiThetaTranslationOrbit := by
  apply dense_span_of_forall_dual_eq_zero
  intro L hL
  let LF : Lp (α := ℝ) ℂ 2 volume →L[ℂ] ℂ :=
    L.comp (Lp.fourierTransformₗᵢ ℝ ℂ).symm.toLinearIsometry.toContinuousLinearMap
  have hLF (a : ℝ) : LF (xiThetaFourierPhaseOrbit a) = 0 := by
    change L ((Lp.fourierTransformₗᵢ ℝ ℂ).symm
      (xiThetaFourierPhaseOrbit a)) = 0
    rw [← fourier_xiThetaTranslationOrbit]
    change L ((Lp.fourierTransformₗᵢ ℝ ℂ).symm
      ((Lp.fourierTransformₗᵢ ℝ ℂ) (xiThetaTranslationOrbit a))) = 0
    simpa using hL a
  have hLFzero := continuousLinearFunctional_eq_zero_of_isCyclicFamily
    isCyclicFamily_xiThetaFourierPhaseOrbit LF hLF
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg
    (fun M : Lp (α := ℝ) ℂ 2 volume →L[ℂ] ℂ ↦
      M ((Lp.fourierTransformₗᵢ ℝ ℂ) x)) hLFzero
  change L ((Lp.fourierTransformₗᵢ ℝ ℂ).symm
    ((Lp.fourierTransformₗᵢ ℝ ℂ) x)) = 0 at hx
  simpa using hx

end

end RHTower
