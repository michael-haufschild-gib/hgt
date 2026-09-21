import GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTOrderedNeutralCurrent
import GaloisForLFunctions.RHTower.FZZCigarNeutralRadialCrossDepthCoherence

/-!
# FZZ external-BRST ordered neutral cross-depth current

The literal cyclic ordered neutral branch coefficient remains oriented after
pairing with diagonal radial covariance. The diagonal covariance is a strictly
positive Gamma norm square, so it cannot erase the branch current. This gives
an explicit nonzero ordered compact--radial source current from corpus-defined
FZZ ingredients.
-/

open Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Cyclic ordered neutral branch coefficient paired with literal diagonal
radial covariance. -/
def fzzCigarExternalBRSTOrderedNeutralDiagonalCurrent
    (k : ℝ) (j : ℂ) (p ν : ℤ) (u v : ℝ) : ℂ :=
  fzzCigarExternalBRSTOrderedNeutralAngularIntegral k j p ν *
    fzzRadialCouplingCrossDepthCoherence u u v (p : ℝ)

/-- Diagonal literal radial covariance is the positive norm square of its
nonzero radial coupling characteristic. -/
theorem fzzRadialCouplingCrossDepthCoherence_diagonal_eq_normSq
    (u v p : ℝ) :
    fzzRadialCouplingCrossDepthCoherence u u v p =
      ((Complex.normSq (fzzRadialCouplingCharacteristic u v p) : ℝ) : ℂ) := by
  unfold fzzRadialCouplingCrossDepthCoherence
  rw [Complex.mul_conj]

/-- The literal cyclic ordered neutral branch construction has a nonzero
compact--radial source current at every nonzero external charge. -/
theorem fzzCigarExternalBRSTOrderedNeutralDiagonalCurrent_im_ne_zero
    (k : ℝ) (j : ℂ) (p ν : ℤ) (u v : ℝ) (hp : p ≠ 0) :
    (fzzCigarExternalBRSTOrderedNeutralDiagonalCurrent k j p ν u v).im ≠ 0 := by
  rw [fzzCigarExternalBRSTOrderedNeutralDiagonalCurrent,
    fzzRadialCouplingCrossDepthCoherence_diagonal_eq_normSq]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero]
  simpa only [zero_add] using mul_ne_zero
    (fzzCigarExternalBRSTOrderedNeutralAngularIntegral_im_ne_zero k j p ν hp)
    (Complex.normSq_pos.mpr
      (fzzRadialCouplingCharacteristic_ne_zero u v (p : ℝ))).ne'

end

end GaloisForLFunctions.RHTower
