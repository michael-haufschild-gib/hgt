import GaloisForLFunctions.HTGeometry.MakarovPoltoratskiUpperDensity
import GaloisForLFunctions.HTGeometry.MeasurableSignMeasure
import GaloisForLFunctions.RHTower.KapustinGaugeCarrier

open MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Exact terminal assembly of the Kapustin sign argument.  The two forcing maps are the positive
and negative applications of the Hardy/Smirnov bounded-phase multiplier construction; the fixed
reciprocal-Gamma phase obstruction then forces both strict sign sets to have positive measure. -/
theorem kapustinGaugeBoundary_bilateral_of_constantSign_forces_toeplitzWitness
    (φ : ℝ → ℂ)
    (hnonneg :
      (∀ᵐ t ∂volume, 0 ≤ kapustinGaugeBoundaryWeight φ t) →
        Nonempty (SmirnovToeplitzPhaseWitness kapustinToeplitzPhase))
    (hnonpos :
      (∀ᵐ t ∂volume, kapustinGaugeBoundaryWeight φ t ≤ 0) →
        Nonempty (SmirnovToeplitzPhaseWitness kapustinToeplitzPhase)) :
    0 < volume {t | 0 < kapustinGaugeBoundaryWeight φ t} ∧
      0 < volume {t | kapustinGaugeBoundaryWeight φ t < 0} := by
  have hnotNonneg : ¬ ∀ᵐ t ∂volume, 0 ≤ kapustinGaugeBoundaryWeight φ t := by
    intro h
    exact noSmirnovToeplitzPhaseWitness_kapustinToeplitzPhase (hnonneg h)
  have hnotNonpos : ¬ ∀ᵐ t ∂volume, kapustinGaugeBoundaryWeight φ t ≤ 0 := by
    intro h
    exact noSmirnovToeplitzPhaseWitness_kapustinToeplitzPhase (hnonpos h)
  exact ⟨measure_strictPositive_pos_iff_not_ae_nonpos.mpr hnotNonpos,
    measure_strictNegative_pos_iff_not_ae_nonneg.mpr hnotNonneg⟩

/-- Theorem B and the exact literal even weighted carrier follow immediately from the analytic
Toeplitz collision, with no finite-dimensional proxy. -/
theorem kapustinGauge_bilateral_infiniteKreinIndex_of_constantSign_forcing
    (φ : ℝ → ℂ) (hφmeas : Measurable φ)
    (hφsymm : ∀ t, φ (-t) = (starRingEnd ℂ) (φ t))
    (hnonneg :
      (∀ᵐ t ∂volume, 0 ≤ kapustinGaugeBoundaryWeight φ t) →
        Nonempty (SmirnovToeplitzPhaseWitness kapustinToeplitzPhase))
    (hnonpos :
      (∀ᵐ t ∂volume, kapustinGaugeBoundaryWeight φ t ≤ 0) →
        Nonempty (SmirnovToeplitzPhaseWitness kapustinToeplitzPhase)) :
    (¬ FiniteDimensional ℂ (KapustinGaugePositiveSector φ hφmeas hφsymm)) ∧
      (¬ FiniteDimensional ℂ (KapustinGaugeNegativeSector φ hφmeas hφsymm)) := by
  obtain ⟨hpos, hneg⟩ :=
    kapustinGaugeBoundary_bilateral_of_constantSign_forces_toeplitzWitness
      φ hnonneg hnonpos
  exact kapustinGauge_bilateral_infiniteKreinIndex_of_boundary_polarization
    hφmeas hφsymm hpos hneg

end RHTower
