import GaloisForLFunctions.RHTower.MobiusDivisorArityHeadProcessedCoreOrientation
import GaloisForLFunctions.RHTower.MobiusDivisorParityDefectTransport

/-!
# Signed processed-core measure for residual fibres

The usual residual Möbius orientation is exactly a signed measure over
positive processed-core coordinates. Its sign is only the parity of the
processed core. This is the source-native representation of the remaining
changing-core covariance.
-/

noncomputable section
open Finset
namespace RHTower

/-- Each residual-oriented fibre is the signed measure of its canonically
positive processed-core coordinates. -/
theorem mobiusDivisorOrientedFibre_eq_processedCore_signedMeasure
    (M : ℕ) (P R : Finset ℕ) :
    mobiusDivisorOrientedFibre M P R =
      ∑ A ∈ P.powerset, (-1 : ℝ) ^ A.card *
        ((-1 : ℝ) ^ (A.card + R.card) *
          mobiusDivisorSelectionProcessedCoreFibre M P A R) := by
  unfold mobiusDivisorOrientedFibre
  rw [mobiusDivisorSelectionFibre_eq_sum_processedCoreFibre, mul_sum]
  apply sum_congr rfl
  intro A hA
  have hdouble : (-1 : ℝ) ^ (A.card + A.card) = 1 := by
    rw [show A.card + A.card = 2 * A.card by omega, pow_mul]
    norm_num
  have hsign : (-1 : ℝ) ^ A.card * (-1 : ℝ) ^ (A.card + R.card) =
      (-1 : ℝ) ^ R.card := by
    rw [← pow_add, show A.card + (A.card + R.card) =
      (A.card + A.card) + R.card by omega, pow_add, hdouble, one_mul]
  rw [← mul_assoc, hsign]

end RHTower
