import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.MacroscopicOverlapSpectralAssembly
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.MacroscopicOverlapConductorFloor
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilFormKeepsADefectReserveAtEveryOverlap

/-!
# The boosted-spline reserve in matrix form

The fixed-overlap defect reserve for the boosted unit spline, stated for the normalized Weil
functional of atomic tests, is transported to the complete Weil matrix in Euclidean coordinates.
Together with the common conductor floor, positivity of the complete matrix at a fixed overlap
then reduces to the norm quasimode law of the normalized Ramanujan vectors.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

/-- The boosted-spline complete Weil matrix retains a positive prime-defect fraction at every
fixed overlap, in matrix coordinates. -/
theorem exists_tiltedUnitSpline_completeWeilEnergy_reserve {c : ℝ} (hc : 0 < c) :
    ∃ a : ℝ, ∃ β : ℝ, 0 < β ∧ ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      a * ‖x‖ ^ 2 + β * poleDefect N (primeHorizonExtension x) ≤
        completeWeilEnergy tiltedUnitSpline c N x := by
  obtain ⟨β, hβ, C, -, hres⟩ := exists_tiltedUnitSpline_complete_defect_reserve hc
  refine ⟨-C, β, hβ, ?_⟩
  filter_upwards [hres, eventually_ge_atTop 1] with N hN hN1
  intro x
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw : 0 < c / N := div_pos hc hNR
  have hmass : (∫ u, atomDilate tiltedUnitSpline (c / N) u ^ 2) =
      (c / N) * ∫ u, tiltedUnitSpline u ^ 2 := integral_atomDilate_sq hw
  have h := hN (primeHorizonExtension x)
  rw [sum_primeHorizonExtension_sq] at h
  rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero hc hN1, hmass]
  linarith only [h]

/-- **Reduction to quasimodes.** At a fixed overlap the boosted-spline complete Weil matrix is
eventually positive definite as soon as the normalized Ramanujan vectors are norm quasimodes
with the completed conductor energies. -/
theorem eventually_tiltedUnitSpline_completeWeilMatrix_posDef_of_quasimodes {c : ℝ} (hc : 0 < c)
    (hquasi : ∀ m : ℕ, 0 < m → Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline c m •
          normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, (completeWeilMatrix tiltedUnitSpline c N).PosDef := by
  obtain ⟨a, β, hβ, hres⟩ := exists_tiltedUnitSpline_completeWeilEnergy_reserve hc
  obtain ⟨e, he, hfloor⟩ := exists_tiltedUnitSpline_conductor_floor hc
  exact eventually_completeWeilMatrix_posDef_of_reserve_quasimodes hβ hres hquasi he hfloor

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
