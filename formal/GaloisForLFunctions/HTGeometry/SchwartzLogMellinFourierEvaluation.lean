import GaloisForLFunctions.HTGeometry.SchwartzLogApertureCompactDecay

/-!
# Normalized Fourier--Mellin evaluation on fixed-aperture Schwartz tests

Mathlib's real Fourier transform uses the character `exp(-2πixt)`. This file makes the exact
frequency conversion to the Mellin-height character `exp(iTx)`, identifies bounded exponential
tilts with shifted Mellin integrals, and proves compact-uniform decay of the physically oriented
quartet product with heights `T` and `-T`.
-/

open MeasureTheory Filter Set
open scoped ENNReal FourierTransform Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Fourier frequency normalized so height `T` gives the character `x ↦ exp(iTx)`. -/
def logMellinHeightEvaluation (f : LogMellinL1) (T : ℝ) : ℂ :=
  logMellinL1Fourier f (-T / (2 * Real.pi))

/-- Exact normalization map from Mellin height to Fourier frequency preserves escape to infinity. -/
theorem tendsto_neg_div_two_pi_cocompact :
    Tendsto (fun T : ℝ => -T / (2 * Real.pi)) (cocompact ℝ) (cocompact ℝ) := by
  rw [cocompact_eq_atBot_atTop, tendsto_sup]
  constructor
  · exact le_sup_of_le_right
      (Filter.Tendsto.atTop_div_const (by positivity)
        (tendsto_neg_atBot_atTop : Tendsto (fun T : ℝ => -T) atBot atTop))
  · exact le_sup_of_le_left
      (Filter.Tendsto.atBot_div_const (by positivity)
        (tendsto_neg_atTop_atBot : Tendsto (fun T : ℝ => -T) atTop atBot))

/-- Reflection of the height line preserves cocompact escape. -/
theorem tendsto_neg_cocompact :
    Tendsto (fun T : ℝ => -T) (cocompact ℝ) (cocompact ℝ) := by
  rw [cocompact_eq_atBot_atTop, tendsto_sup]
  exact ⟨le_sup_of_le_right tendsto_neg_atBot_atTop,
    le_sup_of_le_left tendsto_neg_atTop_atBot⟩

/-- Uniform vanishing is stable under a change of parameter tending to the original filter. -/
theorem UniformlyVanishesAlong.comp_tendsto
    {Y Z X E : Type*} [Norm E] {lY : Filter Y} {lZ : Filter Z}
    {K : Set X} {F : Y → X → E}
    (hF : UniformlyVanishesAlong lY K F) {g : Z → Y}
    (hg : Tendsto g lZ lY) :
    UniformlyVanishesAlong lZ K (fun z x => F (g z) x) := by
  intro ε hε
  exact hg.eventually (hF ε hε)

/-- A bounded exponential tilt evaluated at normalized Fourier height is exactly the shifted
logarithmic Mellin integral. -/
theorem logMellinHeightEvaluation_boundedTilt_eq_integral
    (A δ T : ℝ) (f : LogApertureSchwartz A) :
    logMellinHeightEvaluation
        (logMellinBoundedTilt A δ (logApertureSchwartzToL1 f)) T =
      ∫ x : ℝ, (Real.exp (δ * x) : ℂ) * f.1 x *
        Complex.exp (((T * x : ℝ) : ℂ) * Complex.I) := by
  rw [logMellinHeightEvaluation, logMellinL1Fourier,
    Real.Lp.fourierTransform_apply]
  have hcoe := logMellinBoundedTilt_coeFn_of_supported A δ
    (logApertureSchwartzToL1 f) (supported_logApertureSchwartzToL1 f)
  rw [Real.fourier_congr_ae hcoe]
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hfcoe := SchwartzMap.coeFn_toLp f.1 1 volume
  refine integral_congr_ae ?_
  filter_upwards [hfcoe] with x hx
  simp only [smul_eq_mul]
  change Complex.exp
      ((↑(-2 * Real.pi * x * (-T / (2 * Real.pi))) : ℂ) * Complex.I) *
        ((Real.exp (δ * x) : ℂ) * ((f.1.toLp 1 volume : LogMellinL1) x)) =
      (Real.exp (δ * x) : ℂ) * f.1 x *
        Complex.exp (((T * x : ℝ) : ℂ) * Complex.I)
  rw [hx]
  have hphase :
      Complex.exp
          ((↑(-2 * Real.pi * x * (-T / (2 * Real.pi))) : ℂ) * Complex.I) =
        Complex.exp (((T * x : ℝ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hphase]
  ring

/-- Shifted Mellin evaluations vanish uniformly on compact fixed-aperture Schwartz families. -/
theorem compact_logApertureSchwartz_heightEvaluation_uniformVanishes
    (A δ : ℝ) {K : Set (LogApertureSchwartz A)} (hK : IsCompact K) :
    UniformlyVanishesAlong (cocompact ℝ) K
      (fun T f => logMellinHeightEvaluation
        (logMellinBoundedTilt A δ (logApertureSchwartzToL1 f)) T) := by
  have himage : IsCompact (logApertureSchwartzToL1 '' K) :=
    hK.image (continuous_logApertureSchwartzToL1 A)
  have hbase := compact_logMellinL1Fourier_compCLM_uniformVanishes
    (logMellinBoundedTilt A δ) himage
  have hheight := hbase.comp_tendsto tendsto_neg_div_two_pi_cocompact
  intro ε hε
  filter_upwards [hheight ε hε] with T hT
  intro f hf
  exact hT (logApertureSchwartzToL1 f) ⟨f, hf, rfl⟩

/-- Contribution of the four points `1/2 ± δ ± iT` for a real-valued test. -/
def logApertureSchwartzQuartetDefect (A δ T : ℝ)
    (f : LogApertureSchwartz A) : ℝ :=
  4 * (logMellinHeightEvaluation
      (logMellinBoundedTilt A δ (logApertureSchwartzToL1 f)) T *
    logMellinHeightEvaluation
      (logMellinBoundedTilt A (-δ) (logApertureSchwartzToL1 f)) (-T)).re

/-- Exact compact-uniform decay of the physically oriented remote-quartet defect. -/
theorem compact_logApertureSchwartz_heightQuartetDefect_uniformVanishes
    (A δ : ℝ) {K : Set (LogApertureSchwartz A)} (hK : IsCompact K) :
    UniformlyVanishesAlong (cocompact ℝ) K
      (fun T f => logApertureSchwartzQuartetDefect A δ T f) := by
  have hplus := compact_logApertureSchwartz_heightEvaluation_uniformVanishes A δ hK
  have hminus :=
    (compact_logApertureSchwartz_heightEvaluation_uniformVanishes A (-δ) hK).comp_tendsto
      tendsto_neg_cocompact
  exact hplus.quartetDefect hminus

end

end GaloisForLFunctions.HTGeometry
