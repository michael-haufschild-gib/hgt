import GaloisForLFunctions.HTGeometry.KerrNewmanNeutralScalarResponseBridge

/-!
# Critical charged Kerr--Newman response and the unit-gap Kerr/AdS2 carrier

For every angular label `ell`, the real charge amplitude `sqrt (ell (ell + 1))` makes the
effective multipole gap exactly one.  The normalized charged Kerr--Newman Gamma core therefore
collapses to the low-frequency Kerr `ell = 0` carrier and, equivalently, to the unit-gap
scalaron-throat carrier.

These are meromorphic Gamma-response identities only.  They do not identify charged
Kerr--Newman partial waves with an AdS2 geometry, nor prove a curved scattering statement.
-/

open Filter Set Topology Function Complex

namespace GaloisForLFunctions.HTGeometry

open Bottcher
open scoped UnivMeroFieldInstances

/-- At the critical charge, every angular label has the same normalized Gamma core as the Kerr
`ell = 0` response. -/
theorem kerrNewmanChargedScalarPhysicalGammaResponseMero_criticalCharge_eq_kerrRight_sWave
    (ell : ℕ) :
    kerrNewmanChargedScalarPhysicalGammaResponseMero ell
      (Real.sqrt ((ell : ℝ) * ((ell : ℝ) + 1)) : ℂ) =
      kerrLowFrequencyRightGammaRatioMero 0 := by
  unfold kerrNewmanChargedScalarPhysicalGammaResponseMero
  rw [kerrNewmanChargedScalarEffectiveMultipoleGap_criticalCharge]
  symm
  simpa using kerrLowFrequencyRightGammaRatioMero_eq_kerrNewmanNeutral 0

/-- Equivalently, critical charge selects the unit-gap scalaron-throat Gamma carrier. -/
theorem kerrNewmanChargedScalarPhysicalGammaResponseMero_criticalCharge_eq_scalaronThroat_unitGap
    (ell : ℕ) :
    kerrNewmanChargedScalarPhysicalGammaResponseMero ell
      (Real.sqrt ((ell : ℝ) * ((ell : ℝ) + 1)) : ℂ) =
      scalaronThroatGammaResponseMero 1 := by
  rw [kerrNewmanChargedScalarPhysicalGammaResponseMero_criticalCharge_eq_kerrRight_sWave]
  simpa using kerrLowFrequencyRightGammaRatioMero_eq_scalaronThroatOddGap 0

/-- The pole-cancelled unit-gap AdS2 response is its fixed normalization times the critical-charge
Kerr--Newman response core. -/
theorem ads2OddRenormalizedScalarResponseMero_unitGap_eq_normalization_mul_kerrNewmanCriticalCharge
    (ell : ℕ) :
    ads2OddRenormalizedScalarResponseMero 0 =
      algebraMap ℂ (meroField Set.univ)
        (ads2NeutralScalarGammaNormalizationOddLimit 0) *
      kerrNewmanChargedScalarPhysicalGammaResponseMero ell
        (Real.sqrt ((ell : ℝ) * ((ell : ℝ) + 1)) : ℂ) := by
  rw [kerrNewmanChargedScalarPhysicalGammaResponseMero_criticalCharge_eq_kerrRight_sWave]
  exact ads2OddRenormalizedScalarResponseMero_eq_normalization_mul_kerrRight 0

end GaloisForLFunctions.HTGeometry
