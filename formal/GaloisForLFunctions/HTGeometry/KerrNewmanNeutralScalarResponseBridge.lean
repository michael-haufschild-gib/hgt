import GaloisForLFunctions.HTGeometry.KerrAdS2OddGammaResponseBridge

/-!
# Neutral Kerr--Newman scalar response and the odd AdS2 carrier

The principal effective-multipole gap of the physical charged-scalar Kerr--Newman response is
exactly `2 * ell + 1` at zero scalar charge.  Consequently its frequency-dependent Gamma core is
the low-frequency Kerr right carrier, hence also the odd-gap scalaron-throat carrier.  The
pole-cancelled AdS2 response differs only by its existing frequency-independent normalization.

These are meromorphic-response identities.  They do not prove a Kerr--Newman near-horizon limit,
finite-frequency equivalence, or a statement about a curved Klein--Gordon equation.
-/

namespace GaloisForLFunctions.HTGeometry

open Bottcher
open scoped UnivMeroFieldInstances

/-- The physical neutral Kerr--Newman scalar response has the low-frequency Kerr right carrier. -/
theorem kerrNewmanChargedScalarPhysicalGammaResponseMero_neutral_eq_kerrRight
    (ell : ℕ) :
    kerrNewmanChargedScalarPhysicalGammaResponseMero ell 0 =
      kerrLowFrequencyRightGammaRatioMero ell := by
  unfold kerrNewmanChargedScalarPhysicalGammaResponseMero
  rw [kerrNewmanChargedScalarEffectiveMultipoleGap_neutral]
  exact kerrLowFrequencyRightGammaRatioMero_eq_kerrNewmanNeutral ell |>.symm

/-- The same physical neutral Kerr--Newman carrier is the matching odd-gap scalaron-throat
response. -/
theorem kerrNewmanChargedScalarPhysicalGammaResponseMero_neutral_eq_scalaronThroat
    (ell : ℕ) :
    kerrNewmanChargedScalarPhysicalGammaResponseMero ell 0 =
      scalaronThroatGammaResponseMero (2 * (ell : ℂ) + 1) := by
  rw [kerrNewmanChargedScalarPhysicalGammaResponseMero_neutral_eq_kerrRight]
  exact kerrLowFrequencyRightGammaRatioMero_eq_scalaronThroatOddGap ell

/-- The odd-gap pole-cancelled AdS2 response is its fixed normalization times the physical neutral
Kerr--Newman scalar carrier. -/
theorem ads2OddRenormalizedScalarResponseMero_eq_normalization_mul_kerrNewmanNeutral
    (ell : ℕ) :
    ads2OddRenormalizedScalarResponseMero ell =
      algebraMap ℂ (meroField Set.univ)
        (ads2NeutralScalarGammaNormalizationOddLimit ell) *
      kerrNewmanChargedScalarPhysicalGammaResponseMero ell 0 := by
  rw [kerrNewmanChargedScalarPhysicalGammaResponseMero_neutral_eq_kerrRight]
  exact ads2OddRenormalizedScalarResponseMero_eq_normalization_mul_kerrRight ell

end GaloisForLFunctions.HTGeometry
