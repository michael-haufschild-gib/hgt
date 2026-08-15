import GaloisForLFunctions.RHTower.SuzukiOnePrimeTerminalForcedHardy
import Mathlib.Analysis.Fourier.LpSpace

/-!
# Canonical rough-primitive Fourier forcing for the one-prime terminal block

An `L²` physical source has a unitary vector Fourier transform.  Dividing that transform by the
derivative multiplier `2π i ξ` produces the canonical frequency forcing of its rough primitive.
Although the quotient is singular at frequency zero, multiplication by `ξ` cancels it exactly;
the origin is harmless because inverse-zero convention assigns value zero there.

This module proves the resulting first-moment bound on both frequency rays and feeds it directly
into the literal nonnormal terminal forced-Hardy theorem at Suzuki's concrete height `σ = 3/4`.
-/

open Complex MeasureTheory Set
open scoped ENNReal FourierTransform

namespace RHTower

noncomputable section

/-- A fixed normalized holomorphic square-root branch of the Gamma quotient. -/
def suzukiGammaRatioSqrtBranch : ℂ → ℂ :=
  Classical.choose GaloisForLFunctions.RHTower.exists_gammaRatioSqrt

theorem suzukiGammaRatioSqrtBranch_sq
    (z : ℂ) (hz : z ∈ GaloisForLFunctions.RHTower.imStrip (-1) 1) :
    suzukiGammaRatioSqrtBranch z ^ 2 = GaloisForLFunctions.RHTower.gammaRatio z :=
  (Classical.choose_spec GaloisForLFunctions.RHTower.exists_gammaRatioSqrt).2.1 z hz

theorem differentiableOn_suzukiGammaRatioSqrtBranch :
    DifferentiableOn ℂ suzukiGammaRatioSqrtBranch
      (GaloisForLFunctions.RHTower.imStrip (-1) 1) :=
  (Classical.choose_spec GaloisForLFunctions.RHTower.exists_gammaRatioSqrt).1

/-- Literal two-coordinate `L²` source space. -/
abbrev OnePrimeTerminalSourceL2 :=
  Lp (α := ℝ) OnePrimeTerminalState 2 (volume : Measure ℝ)

/-- Pointwise representative of the unitary vector Fourier transform of a terminal source. -/
def onePrimeTerminalSourceFourier (h : OnePrimeTerminalSourceL2) :
    ℝ → OnePrimeTerminalState :=
  (𝓕 h : OnePrimeTerminalSourceL2)

/-- Canonical frequency forcing of a rough primitive.  At `ξ = 0` the field inverse is zero. -/
def onePrimeTerminalRoughPrimitiveForcing (h : OnePrimeTerminalSourceL2)
    (xi : ℝ) : OnePrimeTerminalState :=
  (((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (xi : ℂ))⁻¹) •
    onePrimeTerminalSourceFourier h xi

theorem aestronglyMeasurable_onePrimeTerminalRoughPrimitiveForcing
    (h : OnePrimeTerminalSourceL2) :
    AEStronglyMeasurable (onePrimeTerminalRoughPrimitiveForcing h) volume := by
  change AEStronglyMeasurable (fun xi : ℝ =>
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (xi : ℂ))⁻¹) •
      onePrimeTerminalSourceFourier h xi) volume
  have hs : AEStronglyMeasurable (fun xi : ℝ =>
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (xi : ℂ))⁻¹)) volume :=
    (by fun_prop : Measurable fun xi : ℝ =>
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (xi : ℂ))⁻¹)).aestronglyMeasurable
  have hf : AEStronglyMeasurable (onePrimeTerminalSourceFourier h) volume :=
    Lp.aestronglyMeasurable (𝓕 h : OnePrimeTerminalSourceL2)
  refine (hs.smul hf).congr ?_
  exact Filter.Eventually.of_forall fun xi => by rw [Pi.smul_apply']

/-- Away from zero, the first frequency moment cancels the rough-primitive pole exactly. -/
theorem real_smul_onePrimeTerminalRoughPrimitiveForcing
    (h : OnePrimeTerminalSourceL2) {xi : ℝ} (hxi : xi ≠ 0) :
    (xi : ℝ) • onePrimeTerminalRoughPrimitiveForcing h xi =
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) •
        onePrimeTerminalSourceFourier h xi := by
  have hcast : (((xi : ℝ) : ℂ)) • onePrimeTerminalRoughPrimitiveForcing h xi =
      (xi : ℝ) • onePrimeTerminalRoughPrimitiveForcing h xi := by
    rw [← Complex.coe_algebraMap, algebraMap_smul]
  rw [← hcast, onePrimeTerminalRoughPrimitiveForcing, smul_smul]
  congr 1
  have hxiC : (xi : ℂ) ≠ 0 := by exact_mod_cast hxi
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- The unitary Fourier representative has finite squared-enorm integral. -/
theorem lintegral_enorm_sq_onePrimeTerminalSourceFourier_lt_top
    (h : OnePrimeTerminalSourceL2) :
    ∫⁻ xi : ℝ, ‖onePrimeTerminalSourceFourier h xi‖ₑ ^ 2 < ⊤ := by
  have hmem := Lp.memLp (𝓕 h : OnePrimeTerminalSourceL2)
  have hint : Integrable (fun xi : ℝ =>
      ‖onePrimeTerminalSourceFourier h xi‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable (𝓕 h : OnePrimeTerminalSourceL2))).mp hmem
  have htop := hint.lintegral_lt_top
  simpa [onePrimeTerminalSourceFourier, ofReal_norm, ENNReal.ofReal_pow] using htop

/-- Global first-moment admission of the canonical rough-primitive forcing. -/
theorem lintegral_enorm_sq_firstMoment_onePrimeTerminalRoughPrimitiveForcing_lt_top
    (h : OnePrimeTerminalSourceL2) :
    ∫⁻ xi : ℝ, ‖(xi : ℝ) • onePrimeTerminalRoughPrimitiveForcing h xi‖ₑ ^ 2 < ⊤ := by
  set C : ℝ≥0∞ := ENNReal.ofReal
    ‖(((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹)‖ with hC
  have hClt : C < ⊤ := by rw [hC]; exact ENNReal.ofReal_lt_top
  have hpoint : ∀ xi : ℝ,
      ‖(xi : ℝ) • onePrimeTerminalRoughPrimitiveForcing h xi‖ₑ ^ 2 ≤
        C ^ 2 * ‖onePrimeTerminalSourceFourier h xi‖ₑ ^ 2 := by
    intro xi
    by_cases hxi : xi = 0
    · subst xi
      simp
    · rw [real_smul_onePrimeTerminalRoughPrimitiveForcing h hxi, enorm_smul]
      rw [hC, ofReal_norm]
      rw [mul_pow]
  calc
    (∫⁻ xi : ℝ,
      ‖(xi : ℝ) • onePrimeTerminalRoughPrimitiveForcing h xi‖ₑ ^ 2) ≤
        ∫⁻ xi : ℝ, C ^ 2 * ‖onePrimeTerminalSourceFourier h xi‖ₑ ^ 2 :=
      lintegral_mono hpoint
    _ = C ^ 2 * ∫⁻ xi : ℝ, ‖onePrimeTerminalSourceFourier h xi‖ₑ ^ 2 := by
      rw [lintegral_const_mul' _ _ (ne_of_lt (ENNReal.pow_lt_top hClt))]
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.pow_lt_top hClt)
      (lintegral_enorm_sq_onePrimeTerminalSourceFourier_lt_top h)

theorem aestronglyMeasurable_onePrimeTerminalRoughPrimitiveForcing_posRay
    (h : OnePrimeTerminalSourceL2) :
    AEStronglyMeasurable
      (fun t : ℝ => onePrimeTerminalRoughPrimitiveForcing h ((1 : ℝ) * t))
      (volume.restrict (Ioi (1 : ℝ))) := by
  simpa using
    (aestronglyMeasurable_onePrimeTerminalRoughPrimitiveForcing h).mono_measure
      Measure.restrict_le_self

theorem aestronglyMeasurable_onePrimeTerminalRoughPrimitiveForcing_negRay
    (h : OnePrimeTerminalSourceL2) :
    AEStronglyMeasurable
      (fun t : ℝ => onePrimeTerminalRoughPrimitiveForcing h ((-1 : ℝ) * t))
      (volume.restrict (Ioi (1 : ℝ))) := by
  have hneg : AEStronglyMeasurable
      (fun t : ℝ => onePrimeTerminalRoughPrimitiveForcing h (-t)) volume := by
    have hcomp :=
      (aestronglyMeasurable_onePrimeTerminalRoughPrimitiveForcing h).comp_measurePreserving
        (Measure.measurePreserving_neg (volume : Measure ℝ))
    simpa [Function.comp_def] using hcomp
  simpa using hneg.mono_measure Measure.restrict_le_self

/-- Positive-ray first moment. -/
theorem lintegral_enorm_sq_firstMoment_onePrimeTerminalRoughPrimitiveForcing_posRay_lt_top
    (h : OnePrimeTerminalSourceL2) :
    ∫⁻ t in Ioi (1 : ℝ),
      ‖(t : ℝ) • onePrimeTerminalRoughPrimitiveForcing h ((1 : ℝ) * t)‖ₑ ^ 2 < ⊤ := by
  calc
    (∫⁻ t in Ioi (1 : ℝ),
      ‖(t : ℝ) • onePrimeTerminalRoughPrimitiveForcing h ((1 : ℝ) * t)‖ₑ ^ 2) =
        ∫⁻ t in Ioi (1 : ℝ),
          ‖(t : ℝ) • onePrimeTerminalRoughPrimitiveForcing h t‖ₑ ^ 2 := by simp
    _ ≤ ∫⁻ t : ℝ,
        ‖(t : ℝ) • onePrimeTerminalRoughPrimitiveForcing h t‖ₑ ^ 2 :=
      setLIntegral_le_lintegral _ _
    _ < ⊤ :=
      lintegral_enorm_sq_firstMoment_onePrimeTerminalRoughPrimitiveForcing_lt_top h

/-- Negative-ray first moment, obtained by exact reflection rather than a second source estimate. -/
theorem lintegral_enorm_sq_firstMoment_onePrimeTerminalRoughPrimitiveForcing_negRay_lt_top
    (h : OnePrimeTerminalSourceL2) :
    ∫⁻ t in Ioi (1 : ℝ),
      ‖(t : ℝ) • onePrimeTerminalRoughPrimitiveForcing h ((-1 : ℝ) * t)‖ₑ ^ 2 < ⊤ := by
  let moment : ℝ → ℝ≥0∞ := fun x =>
    ‖(x : ℝ) • onePrimeTerminalRoughPrimitiveForcing h x‖ₑ ^ 2
  have hreflect : (∫⁻ t : ℝ, moment (-t)) = ∫⁻ x : ℝ, moment x :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).lintegral_comp_emb
      measurableEmbedding_neg moment
  calc
    (∫⁻ t in Ioi (1 : ℝ),
      ‖(t : ℝ) • onePrimeTerminalRoughPrimitiveForcing h ((-1 : ℝ) * t)‖ₑ ^ 2) =
        ∫⁻ t in Ioi (1 : ℝ), moment (-t) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t _
      simp [moment, neg_smul]
    _ ≤ ∫⁻ t : ℝ, moment (-t) := setLIntegral_le_lintegral _ _
    _ = ∫⁻ x : ℝ, moment x := hreflect
    _ < ⊤ := by
      exact lintegral_enorm_sq_firstMoment_onePrimeTerminalRoughPrimitiveForcing_lt_top h

/-- Unconditional positive-frequency Hardy admission for every literal one-prime `L²` source. -/
theorem lintegral_enorm_sq_onePrimeTerminalRoughPrimitive_forcedStripRay_pos_lt_top
    (h : OnePrimeTerminalSourceL2) (c : OnePrimeTerminalState) :
    ∫⁻ x in Ioi (1 : ℝ),
      ‖GaloisForLFunctions.RHTower.forcedStripRay suzukiGammaRatioSqrtBranch
        onePrimeTerminalAdjacencyCLM c
        (onePrimeTerminalRoughPrimitiveForcing h) (3 / 4 : ℝ) 1 x‖ₑ ^ 2 < ⊤ := by
  exact lintegral_enorm_sq_forcedStripRay_onePrimeTerminal_lt_top
    suzukiGammaRatioSqrtBranch_sq c (onePrimeTerminalRoughPrimitiveForcing h)
    (by norm_num) (by norm_num) (by norm_num)
    (aestronglyMeasurable_onePrimeTerminalRoughPrimitiveForcing_posRay h)
    (lintegral_enorm_sq_firstMoment_onePrimeTerminalRoughPrimitiveForcing_posRay_lt_top h)

/-- Unconditional negative-frequency Hardy admission for every literal one-prime `L²` source. -/
theorem lintegral_enorm_sq_onePrimeTerminalRoughPrimitive_forcedStripRay_neg_lt_top
    (h : OnePrimeTerminalSourceL2) (c : OnePrimeTerminalState) :
    ∫⁻ x in Ioi (1 : ℝ),
      ‖GaloisForLFunctions.RHTower.forcedStripRay suzukiGammaRatioSqrtBranch
        onePrimeTerminalAdjacencyCLM c
        (onePrimeTerminalRoughPrimitiveForcing h) (3 / 4 : ℝ) (-1) x‖ₑ ^ 2 < ⊤ := by
  exact lintegral_enorm_sq_forcedStripRay_onePrimeTerminal_lt_top
    suzukiGammaRatioSqrtBranch_sq c (onePrimeTerminalRoughPrimitiveForcing h)
    (by norm_num) (by norm_num) (by norm_num)
    (aestronglyMeasurable_onePrimeTerminalRoughPrimitiveForcing_negRay h)
    (lintegral_enorm_sq_firstMoment_onePrimeTerminalRoughPrimitiveForcing_negRay_lt_top h)

end

end RHTower
