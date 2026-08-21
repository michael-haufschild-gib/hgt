import GaloisForLFunctions.HTGeometry.KerrNewmanCriticalChargeKerrAdS2Bridge

/-!
# Quantized odd charged Kerr--Newman gaps and the Kerr/AdS2 tower

For `m ≤ ell`, the finite charge that selects effective gap `2m+1` makes the physical
Kerr--Newman Gamma core exactly the low-frequency Kerr `m` carrier.  It is therefore also the
matching odd-gap scalaron-throat carrier, and the pole-cancelled AdS2 response differs only by
its existing frequency-independent normalization.

This is a meromorphic-response identity.  It does not establish a near-horizon geometry or a
finite-frequency charged Kerr--Newman scattering correspondence.
-/

open Filter Set Topology Function Complex

namespace GaloisForLFunctions.HTGeometry

open Bottcher
open scoped UnivMeroFieldInstances

/-- The bounded odd target gap `2m+1` as a member of the finite Kerr--Newman gap family. -/
def kerrNewmanOddQuantizedGapIndex
    (ell : ℕ) (m : Fin (ell + 1)) : Fin (2 * ell + 2) :=
  ⟨2 * m + 1, by omega⟩

/-- A quantized odd charged Kerr--Newman response is exactly the corresponding Kerr Gamma
carrier. -/
theorem kerrNewmanPhysicalResponse_quantizedOddGap_eq_kerrRight
    (ell : ℕ) (m : Fin (ell + 1)) :
    kerrNewmanChargedScalarPhysicalGammaResponseMero ell
      (kerrNewmanChargedScalarQuantizedCharge ell
        (kerrNewmanOddQuantizedGapIndex ell m)) =
      kerrLowFrequencyRightGammaRatioMero m := by
  unfold kerrNewmanChargedScalarPhysicalGammaResponseMero
  rw [kerrNewmanChargedScalarEffectiveMultipoleGap_quantizedCharge]
  simpa [kerrNewmanOddQuantizedGapIndex] using
    (kerrLowFrequencyRightGammaRatioMero_eq_kerrNewmanNeutral m).symm

/-- The same quantized odd charged response is the scalaron-throat carrier at gap `2m+1`. -/
theorem kerrNewmanPhysicalResponse_quantizedOddGap_eq_scalaronThroat
    (ell : ℕ) (m : Fin (ell + 1)) :
    kerrNewmanChargedScalarPhysicalGammaResponseMero ell
      (kerrNewmanChargedScalarQuantizedCharge ell
        (kerrNewmanOddQuantizedGapIndex ell m)) =
      scalaronThroatGammaResponseMero (2 * (m : ℂ) + 1) := by
  rw [kerrNewmanPhysicalResponse_quantizedOddGap_eq_kerrRight]
  exact kerrLowFrequencyRightGammaRatioMero_eq_scalaronThroatOddGap m

/-- The odd-gap pole-cancelled AdS2 response is its fixed normalization times the corresponding
quantized charged Kerr--Newman core. -/
theorem ads2OddResponse_eq_normalization_mul_kerrNewmanQuantizedOddGap
    (ell : ℕ) (m : Fin (ell + 1)) :
    ads2OddRenormalizedScalarResponseMero m =
      algebraMap ℂ (meroField Set.univ)
        (ads2NeutralScalarGammaNormalizationOddLimit m) *
      kerrNewmanChargedScalarPhysicalGammaResponseMero ell
        (kerrNewmanChargedScalarQuantizedCharge ell
          (kerrNewmanOddQuantizedGapIndex ell m)) := by
  rw [kerrNewmanPhysicalResponse_quantizedOddGap_eq_kerrRight]
  exact ads2OddRenormalizedScalarResponseMero_eq_normalization_mul_kerrRight m

end GaloisForLFunctions.HTGeometry
