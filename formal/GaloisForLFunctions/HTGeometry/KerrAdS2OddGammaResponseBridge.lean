import GaloisForLFunctions.HTGeometry.KerrNewmanBelinskiZakharovBridge
import GaloisForLFunctions.HTGeometry.AdS2RenormalizedScalarClockParity

/-!
# Kerr right response and odd-gap AdS2 scalar carrier

The low-frequency Kerr right Gamma ratio is the same meromorphic carrier as the neutral
odd-positive-gap scalaron throat response. The pole-cancelled AdS2 response is this Kerr carrier
multiplied by its frequency-independent odd-gap normalization. This is an exact analytic identity,
not a proof of a geometric near-horizon limit or a finite-frequency Kerr statement.
-/

namespace GaloisForLFunctions.HTGeometry

open Bottcher
open scoped UnivMeroFieldInstances

/-- The low-frequency Kerr right response is exactly the scalaron throat carrier at the matching
positive odd gap. -/
theorem kerrLowFrequencyRightGammaRatioMero_eq_scalaronThroatOddGap
    (ell : ℕ) :
    kerrLowFrequencyRightGammaRatioMero ell =
      scalaronThroatGammaResponseMero (2 * (ell : ℂ) + 1) := by
  rw [scalaronThroatGammaResponseMero]
  exact kerrLowFrequencyRightGammaRatioMero_eq_kerrNewmanNeutral ell

/-- The odd-gap pole-cancelled AdS2 response is a constant normalization times the matching Kerr
right Gamma carrier. -/
theorem ads2OddRenormalizedScalarResponseMero_eq_normalization_mul_kerrRight
    (ell : ℕ) :
    ads2OddRenormalizedScalarResponseMero ell =
      algebraMap ℂ (meroField Set.univ)
        (ads2NeutralScalarGammaNormalizationOddLimit ell) *
      kerrLowFrequencyRightGammaRatioMero ell := by
  unfold ads2OddRenormalizedScalarResponseMero
  rw [← kerrLowFrequencyRightGammaRatioMero_eq_scalaronThroatOddGap]

end GaloisForLFunctions.HTGeometry
