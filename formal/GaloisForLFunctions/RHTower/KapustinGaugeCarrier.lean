import GaloisForLFunctions.RHTower.KapustinPowerGaugeKreinIndex
import GaloisForLFunctions.HTGeometry.MeasurableEvenWeightedSignCarrier

open Complex Filter Topology MeasureTheory

noncomputable section

namespace RHTower

def kapustinUniversalGammaCarrier (t : ℝ) : ℂ :=
  ((Real.exp ((-3 / 2 : ℝ) * Real.log (2 * Real.pi)) : ℂ) *
      Complex.exp (I * (t * Real.log (2 * Real.pi) : ℂ))) /
    gammaVerticalValue (1 / 2) t

theorem kapustinUniversalGammaCarrier_eq_formula (t : ℝ) :
    kapustinUniversalGammaCarrier t =
      (((2 * Real.pi : ℝ) : ℂ) ^
        (((-3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) /
      Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
  rw [kapustinUniversalGammaCarrier, kapustinBaseCpow]
  rfl

theorem continuous_kapustinUniversalGammaCarrier :
    Continuous kapustinUniversalGammaCarrier := by
  have hgammaDiff : Differentiable ℝ (gammaVerticalValue (1 / 2)) :=
    fun t => (hasDerivAt_gammaVerticalValue (σ := 1 / 2) (by norm_num) t).differentiableAt
  have hgamma : Continuous (gammaVerticalValue (1 / 2)) := hgammaDiff.continuous
  apply continuous_iff_continuousAt.mpr
  intro t
  unfold kapustinUniversalGammaCarrier
  fun_prop (disch := exact gammaVerticalValue_ne_zero (by norm_num) t)

theorem kapustinUniversalGammaCarrier_neg (t : ℝ) :
    kapustinUniversalGammaCarrier (-t) =
      (starRingEnd ℂ) (kapustinUniversalGammaCarrier t) := by
  rw [kapustinUniversalGammaCarrier_eq_formula, kapustinUniversalGammaCarrier_eq_formula]
  rw [kapustinBaseCpow, kapustinBaseCpow]
  rw [show (((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) =
      (starRingEnd ℂ) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) by
        apply Complex.ext <;> simp,
    Complex.Gamma_conj, map_div₀, map_mul, Complex.conj_ofReal]
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  apply Complex.ext <;> simp

def kapustinGaugeBoundaryQ (φ : ℝ → ℂ) (t : ℝ) : ℂ :=
  kapustinUniversalGammaCarrier t * φ t

theorem kapustinGaugeBoundaryQ_eq_formula (φ : ℝ → ℂ) (t : ℝ) :
    kapustinGaugeBoundaryQ φ t =
      (((2 * Real.pi : ℝ) : ℂ) ^
        (((-3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) * φ t /
      Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
  rw [kapustinGaugeBoundaryQ, kapustinUniversalGammaCarrier_eq_formula]
  ring

def kapustinGaugeBoundaryWeight (φ : ℝ → ℂ) (t : ℝ) : ℝ :=
  (kapustinGaugeBoundaryQ φ t).re

theorem measurable_kapustinGaugeBoundaryQ {φ : ℝ → ℂ} (hφ : Measurable φ) :
    Measurable (kapustinGaugeBoundaryQ φ) :=
  continuous_kapustinUniversalGammaCarrier.measurable.mul hφ

theorem measurable_kapustinGaugeBoundaryWeight {φ : ℝ → ℂ} (hφ : Measurable φ) :
    Measurable (kapustinGaugeBoundaryWeight φ) :=
  Complex.measurable_re.comp (measurable_kapustinGaugeBoundaryQ hφ)

theorem kapustinGaugeBoundaryQ_neg {φ : ℝ → ℂ}
    (hφ : ∀ t, φ (-t) = (starRingEnd ℂ) (φ t)) (t : ℝ) :
    kapustinGaugeBoundaryQ φ (-t) = (starRingEnd ℂ) (kapustinGaugeBoundaryQ φ t) := by
  rw [kapustinGaugeBoundaryQ, kapustinGaugeBoundaryQ, hφ,
    kapustinUniversalGammaCarrier_neg, map_mul]

theorem kapustinGaugeBoundaryWeight_even {φ : ℝ → ℂ}
    (hφ : ∀ t, φ (-t) = (starRingEnd ℂ) (φ t)) (t : ℝ) :
    kapustinGaugeBoundaryWeight φ (-t) = kapustinGaugeBoundaryWeight φ t := by
  rw [kapustinGaugeBoundaryWeight, kapustinGaugeBoundaryWeight,
    kapustinGaugeBoundaryQ_neg hφ, Complex.conj_re]

abbrev KapustinGaugeCarrier (φ : ℝ → ℂ) (hφmeas : Measurable φ)
    (hφsymm : ∀ t, φ (-t) = (starRingEnd ℂ) (φ t)) :=
  GaloisForLFunctions.HTGeometry.signedWeightEvenSubspace
    (measurable_kapustinGaugeBoundaryWeight hφmeas)
    (kapustinGaugeBoundaryWeight_even hφsymm)

abbrev KapustinGaugePositiveSector (φ : ℝ → ℂ) (hφmeas : Measurable φ)
    (hφsymm : ∀ t, φ (-t) = (starRingEnd ℂ) (φ t)) :=
  GaloisForLFunctions.HTGeometry.weightPositiveSector
    (measurable_kapustinGaugeBoundaryWeight hφmeas)
    (kapustinGaugeBoundaryWeight_even hφsymm)

abbrev KapustinGaugeNegativeSector (φ : ℝ → ℂ) (hφmeas : Measurable φ)
    (hφsymm : ∀ t, φ (-t) = (starRingEnd ℂ) (φ t)) :=
  GaloisForLFunctions.HTGeometry.weightNegativeSector
    (measurable_kapustinGaugeBoundaryWeight hφmeas)
    (kapustinGaugeBoundaryWeight_even hφsymm)

/-- Theorem B in its exact boundary form: Theorem A's two positive-measure conclusions force
both Krein sectors of Kapustin's literal even weighted carrier to be infinite-dimensional. -/
theorem kapustinGauge_bilateral_infiniteKreinIndex_of_boundary_polarization
    {φ : ℝ → ℂ} (hφmeas : Measurable φ)
    (hφsymm : ∀ t, φ (-t) = (starRingEnd ℂ) (φ t))
    (hpos : 0 < volume {t | 0 < kapustinGaugeBoundaryWeight φ t})
    (hneg : 0 < volume {t | kapustinGaugeBoundaryWeight φ t < 0}) :
    (¬ FiniteDimensional ℂ (KapustinGaugePositiveSector φ hφmeas hφsymm)) ∧
      (¬ FiniteDimensional ℂ (KapustinGaugeNegativeSector φ hφmeas hφsymm)) := by
  exact GaloisForLFunctions.HTGeometry.evenWeightedCarrier_bilateral_infiniteKreinIndex_of_measure_pos
    (measurable_kapustinGaugeBoundaryWeight hφmeas)
    (kapustinGaugeBoundaryWeight_even hφsymm)
    hpos hneg

end RHTower
