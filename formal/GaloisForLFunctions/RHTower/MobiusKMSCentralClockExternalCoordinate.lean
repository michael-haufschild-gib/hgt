import GaloisForLFunctions.RHTower.MobiusIncidencePassiveCompletionNoGo
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardJuliaTransport

open Complex

noncomputable section

namespace RHTower

/-- The unique Möbius boundary coordinate that sends an Euler parameter `sigma` to the
centered KMS clock `I * eta`. -/
def mobiusKMSCentralClockExternalCoordinate (sigma eta : ℝ) : ℝ :=
  ((1 / 2 - eta) - sigma) / (sigma - 1)

/-- The external KMS coordinate lands exactly at the subcritical real source parameter. -/
theorem mobiusCriticalBoundaryParameter_kmsCentralClockExternalCoordinate
    {sigma eta : ℝ} (hsigma : sigma ≠ 1) :
    mobiusCriticalBoundaryParameter sigma
        (mobiusKMSCentralClockExternalCoordinate sigma eta) =
      1 / 2 - eta := by
  unfold mobiusCriticalBoundaryParameter mobiusKMSCentralClockExternalCoordinate
  field_simp [sub_ne_zero.mpr hsigma]
  ring

/-- In centered Xi coordinates this is precisely the positive imaginary KMS clock. -/
theorem xiWardCenteredCoordinate_kmsCentralClockExternalCoordinate
    {sigma eta : ℝ} (hsigma : sigma ≠ 1) :
    xiWardCenteredCoordinate
        (mobiusCriticalBoundaryParameter sigma
          (mobiusKMSCentralClockExternalCoordinate sigma eta) : ℂ) =
      Complex.I * eta := by
  rw [mobiusCriticalBoundaryParameter_kmsCentralClockExternalCoordinate hsigma]
  unfold xiWardCenteredCoordinate
  push_cast
  ring

/-- The forced coordinate is an exterior ray with prescribed `1 / (sigma - 1)` escape. -/
theorem mobiusKMSCentralClockExternalCoordinate_eq_neg_one_sub
    {sigma eta : ℝ} (hsigma : sigma ≠ 1) :
    mobiusKMSCentralClockExternalCoordinate sigma eta =
      -1 - (1 / 2 + eta) / (sigma - 1) := by
  unfold mobiusKMSCentralClockExternalCoordinate
  field_simp [sub_ne_zero.mpr hsigma]
  ring

/-- Every positive KMS clock lies strictly beyond the physical nonnegative Möbius aperture. -/
theorem mobiusKMSCentralClockExternalCoordinate_lt_neg_one
    {sigma eta : ℝ} (hsigma : 1 < sigma) (heta : 0 < eta) :
    mobiusKMSCentralClockExternalCoordinate sigma eta < -1 := by
  rw [mobiusKMSCentralClockExternalCoordinate_eq_neg_one_sub hsigma.ne']
  have hpos : 0 < (1 / 2 + eta) / (sigma - 1) := by positivity
  linarith

end RHTower
