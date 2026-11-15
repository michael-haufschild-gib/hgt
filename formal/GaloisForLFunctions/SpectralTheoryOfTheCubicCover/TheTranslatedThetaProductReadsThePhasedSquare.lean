import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheTranslatedThetaProductHasOneCuspSubtraction
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheRotatedThetaProductReadsTheRotatedCorrelation

/-!
# The translated theta product reads the phased square

Opposite translations multiply each squared Fourier coefficient by the
additive phase at twice the translation. Parseval identifies this phased
series with the constant term of the translated theta product.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicEisenstein

/-- Translation acts diagonally on the Fourier coefficients. -/
theorem cuspCharacterSeries_translate (a : O → ℂ) (b z : ℂ) :
    cuspCharacterSeries a (z + b) =
      cuspCharacterSeries (fun h => a h * tracePhase (cuspFrequency h * b)) z := by
  unfold cuspCharacterSeries
  refine tsum_congr fun h => ?_
  rw [mul_add, AddChar.map_add_eq_mul]
  ring

def translatedAmplitude (b : O) (v : ℝ) (h : O) : ℂ :=
  rationalSourceModeAmplitude v h * tracePhase (cuspFrequency h * ringComplex b)

theorem translatedTheta_fourier (b : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    sourceTheta (integralComplexMatrix (integralTranslation b) • upperPoint z v hv) =
      cuspCharacterSeries (translatedAmplitude b v) z := by
  rw [integralTranslation_action, show sourceTheta = cubicSourceResidualFunction from rfl,
    cubicSourceResidualFunction_fourier_expansion, cuspCharacterSeries_translate]
  rfl

theorem summable_translatedAmplitude (b : O) (v : ℝ) (hv : 0 < v) :
    Summable (fun h => ‖translatedAmplitude b v h‖) := by
  simpa only [translatedAmplitude, norm_mul, tracePhase_norm, mul_one] using
    rationalSourceModeAmplitude_summable v hv

/-- The squared theta coefficient with its opposite-translation phase. -/
def translatedCoeff (h : O) : ℂ :=
  rationalSourceResidualFourierCoefficient h ^ 2 *
    tracePhase (2 * (cuspFrequency h * ringComplex omega))

theorem translatedAmplitude_mul (v : ℝ) (hv : 0 < v) (h : O) (hh : h ≠ 0) :
    translatedAmplitude omega v h * translatedAmplitude (-omega) v (-h) =
      translatedCoeff h * ((v : ℂ) ^ 2 * besselSq (4 * Real.pi * ‖cuspFrequency h‖ * v)) := by
  have he : tracePhase (cuspFrequency h * ringComplex omega) *
      tracePhase (cuspFrequency (-h) * ringComplex (-omega)) =
        tracePhase (2 * (cuspFrequency h * ringComplex omega)) := by
    rw [← AddChar.map_add_eq_mul, cuspFrequency_neg, map_neg, neg_mul_neg]
    congr 1
    ring
  rw [translatedAmplitude, translatedAmplitude, mul_mul_mul_comm, he,
    rationalSourceModeAmplitude_bessel v hv h hh,
    rationalSourceModeAmplitude_bessel v hv (-h) (neg_ne_zero.mpr hh),
    rationalSourceResidualFourierCoefficient_neg, cuspFrequency_neg, norm_neg,
    translatedCoeff, besselSq]
  ring

/-- Parseval identifies the translated product with the phased squared series. -/
theorem cuspConstantTerm_translatedThetaProduct (v : ℝ) (hv : 0 < v) :
    cuspConstantTerm translatedThetaProduct v =
      periodArea * (thetaCoeff ^ 2 * ((v ^ ((4 : ℝ) / 3) : ℝ) : ℂ) +
        besselRemainder translatedCoeff v) := by
  have ha := summable_translatedAmplitude omega v hv
  have hb := summable_translatedAmplitude (-omega) v hv
  have hθ : ∀ z, translatedThetaProduct (cuspCoordinateLift (v, z)) =
      cuspCharacterSeries (translatedAmplitude omega v) z *
        cuspCharacterSeries (translatedAmplitude (-omega) v) z := fun z => by
    rw [cuspCoordinateLift_positive v z hv, translatedThetaProduct,
      translatedTheta_fourier, translatedTheta_fourier]
  rw [cuspConstantTerm]
  simp_rw [hθ]
  rw [integral_cuspCharacterSeries_mul _ _ ha hb]
  congr 1
  have hsum : Summable (fun h : O => translatedAmplitude omega v h *
      translatedAmplitude (-omega) v (-h)) := by
    refine Summable.of_norm_bounded (ha.mul_right (∑' k, ‖translatedAmplitude (-omega) v k‖))
      fun h => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb.le_tsum (-h) fun k _ => norm_nonneg _) (norm_nonneg _)
  rw [hsum.tsum_eq_add_tsum_ite 0, neg_zero]
  have hz (b : O) : translatedAmplitude b v 0 = rationalSourceModeAmplitude v 0 := by
    simp [translatedAmplitude, cuspFrequency]
  rw [hz, hz, ← sq, rationalSourceModeAmplitude_zero, mul_pow, cpow_two_thirds_sq v hv,
    besselRemainder]
  congr 1
  refine tsum_congr fun h => ?_
  split_ifs with hh
  · rfl
  · exact translatedAmplitude_mul v hv h hh

theorem summable_translatedCoeff {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun h : O => if h = 0 then 0 else
      ‖translatedCoeff h‖ * ‖cuspFrequency h‖ ^ (-σ)) := by
  simpa only [translatedCoeff, norm_mul, norm_pow, tracePhase_norm, mul_one] using
    summable_sourceCoefficient_sq_rpow hσ

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
