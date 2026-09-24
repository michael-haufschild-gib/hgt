import GaloisForLFunctions.RHTower.PrimeArchHankelDeterminantThree
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMomentThreeFour
import GaloisForLFunctions.RHTower.PrimeArchThetaGateCurvatureIdentity
import GaloisForLFunctions.RHTower.PrimeArchThetaScoreAffineGateAlgebra

/-!
# Affine reduction of the first open prime--archimedean determinant

The score gap and the shifted theta Gram residual are both positive for the
literal source.  Subtracting a multiple of their four-moment Schur constraint
from the quadratic determinant gate cancels its fourth-moment square.  The
remaining obstruction is affine in that moment.
-/

namespace RHTower
noncomputable section

/-- The actual source determinant is an affine gate plus two nonnegative
source terms: a shifted theta Gram residual and a score gap. -/
theorem primeArch_three_det_scoreAffineGate :
    let a := thetaCuspNormalizedEvenMoment 1
    let b := thetaCuspNormalizedEvenMoment 2
    let c := thetaCuspNormalizedEvenMoment 3
    let e := thetaCuspNormalizedEvenMoment 4
    let f := thetaCuspNormalizedEvenMoment 5
    let v := normalizedPrimeArchMoment 1
    let w := normalizedPrimeArchMoment 2
    let u := a * c / 180 + b ^ 2 / 144 - a ^ 2 * b / 12 + a ^ 4 / 8
    let d := a * w - v ^ 2
    let q := a * c - b ^ 2
    let p := a * e ^ 2 - 2 * b * c * e + c ^ 3
    let K₀ := c ^ 3 / 70 -
      d * (-504 * v * c + 15120 * w * b - 181440 * a * u) -
      362880 * (a * u ^ 2 - 2 * v * w * u + w ^ 3)
    let K₁ := -b * c / 35 - 45 * a * d - 144 * (v * w - a * u) +
      145 * d / 303 - 145 * q / 21210
    362880 * (primeArchSourceMomentHankelMatrix 3).det =
      (q * f - p) / 70 + (K₀ + K₁ * e) +
        (q / 70 - d) * (145 * e - 303 * f) / 303 := by
  dsimp only
  rw [det_primeArchSourceMomentHankelMatrix_three,
    normalizedPrimeArchMoment_four_eq_thetaCuspNormalizedEvenMoment,
    normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
  have hm : normalizedPrimeArchMoment 3 =
      thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 3 / 180 +
        thetaCuspNormalizedEvenMoment 2 ^ 2 / 144 -
        thetaCuspNormalizedEvenMoment 1 ^ 2 * thetaCuspNormalizedEvenMoment 2 / 12 +
        thetaCuspNormalizedEvenMoment 1 ^ 4 / 8 -
        thetaCuspNormalizedEvenMoment 4 / 5040 := by
    rw [normalizedPrimeArchMoment_three_eq_thetaCuspNormalizedEvenMoment]
    ring
  rw [hm]
  generalize hu :
      thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 3 / 180 +
        thetaCuspNormalizedEvenMoment 2 ^ 2 / 144 -
        thetaCuspNormalizedEvenMoment 1 ^ 2 * thetaCuspNormalizedEvenMoment 2 / 12 +
        thetaCuspNormalizedEvenMoment 1 ^ 4 / 8 = u
  ring

end
end RHTower
