import GaloisForLFunctions.RHTower.StationaryRecurrenceSupportIntervalLaw

/-!
# Universal stationary survival-recurrence law

For every probability spectral measure, centered uniform-time sampling of the
Born survival probability converges to one stationary law.  That law depends
only on the pure-point spectral carrier: it is the normalized pure-point law
scaled by the square of total pure-point mass.  Its support is one interval
whose upper endpoint is exactly that square, so the carrier mass is recovered
from the observable stationary support.

This theorem has no spectral regularity, discreteness, simplicity,
nonresonance, genericity, randomness, chaos, or mixing premise.
-/

open Filter MeasureTheory Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Universal stationary survival-recurrence law.**  The finite-window
survival-fidelity laws converge; the limit is exactly the scaled law of the
normalized pure-point carrier; and its connected support recovers total
pure-point mass from its upper edge. -/
theorem universalStationarySurvivalRecurrenceLaw
    (mu : ProbabilityMeasure ℝ) :
    Tendsto
        (centeredSpectralReturnProbabilityMeasure (mu : Measure ℝ))
        atTop
        (𝓝 (stationarySpectralReturnProbabilityMeasure (mu : Measure ℝ))) ∧
      stationarySpectralReturnProbabilityMeasure (mu : Measure ℝ) =
        scaledPointSpectrumStationaryReturnLaw (mu : Measure ℝ) ∧
      ∃ lower : SpectralReturnFidelityInterval,
        (stationarySpectralReturnProbabilityMeasure (mu : Measure ℝ) :
            Measure SpectralReturnFidelityInterval).support =
            Set.Icc lower
              (pointSpectrumFidelityScale (mu : Measure ℝ)
                oneSpectralReturnFidelity) ∧
        ((pointSpectrumFidelityScale (mu : Measure ℝ)
            oneSpectralReturnFidelity : SpectralReturnFidelityInterval) : ℝ) =
          pointSpectrumMassReal (mu : Measure ℝ) ^ 2 ∧
        pointSpectrumMassReal (mu : Measure ℝ) =
          Real.sqrt
            ((pointSpectrumFidelityScale (mu : Measure ℝ)
              oneSpectralReturnFidelity : SpectralReturnFidelityInterval) : ℝ) := by
  refine ⟨centeredSpectralReturnProbabilityMeasure_tendsto_stationary
      (mu : Measure ℝ),
    stationarySpectralReturnProbabilityMeasure_eq_scaledPointSpectrum
      (mu : Measure ℝ), ?_⟩
  obtain ⟨lower, hsupp⟩ :=
    exists_stationarySpectralReturnProbabilityMeasure_support_Icc
      (mu : Measure ℝ)
  exact ⟨lower, hsupp,
    coe_pointSpectrumFidelityScale_one (mu : Measure ℝ),
    pointSpectrumMassReal_eq_sqrt_stationarySupportEdge (mu : Measure ℝ)⟩

end

end RHTower
