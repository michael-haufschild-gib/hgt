import GaloisForLFunctions.RHTower.PrimeArchHankelDeterminantThree
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMomentThreeFour

/-!
# The shifted theta Gram residual in the first open source determinant

The fifth normalized theta moment enters the size-three prime--archimedean Hankel
determinant linearly.  This identity separates its shifted theta moment determinant
from a gate depending only on the first four normalized theta moments.

The identity is unconditional.  Strict positivity of the shifted theta determinant
and the sign of the four-moment gate are separate analytic questions.
-/

namespace RHTower

noncomputable section

/-- Exact decomposition of the first open prime--archimedean Hankel determinant into the
shifted theta Gram determinant and a gate involving only theta moments through order four. -/
theorem primeArch_three_det_shifted_theta_decomposition :
    let a := thetaCuspNormalizedEvenMoment 1
    let b := thetaCuspNormalizedEvenMoment 2
    let c := thetaCuspNormalizedEvenMoment 3
    let e := thetaCuspNormalizedEvenMoment 4
    let f := thetaCuspNormalizedEvenMoment 5
    let m₀ := normalizedPrimeArchMoment 0
    let m₁ := normalizedPrimeArchMoment 1
    let m₂ := normalizedPrimeArchMoment 2
    let m₃ := normalizedPrimeArchMoment 3
    let q := a*c-b^2
    let p := a*e^2-2*b*c*e+c^3
    let d := m₀*m₂-m₁^2
    let B := 9*m₀*e-504*m₁*c+15120*m₂*b-181440*m₃*a
    let C := m₀*m₃^2-2*m₁*m₂*m₃+m₂^3
    362880*q*(primeArchSourceMomentHankelMatrix 3).det =
      d*(q*f-p)+(d*p-q*(d*B+362880*C)) := by
  dsimp only
  rw [det_primeArchSourceMomentHankelMatrix_three,
    normalizedPrimeArchMoment_four_eq_thetaCuspNormalizedEvenMoment]
  ring

end

end RHTower
