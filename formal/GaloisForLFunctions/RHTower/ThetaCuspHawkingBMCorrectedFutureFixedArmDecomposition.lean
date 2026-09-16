import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFutureSourceBridge
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCompleteOriginalWeakSource

/-!
The literal cap-corrected future field has an exact physical-interior decomposition.
After multiplying by the full angular parameter, its admitted infinite future
convolution is replaced by the compact future pulse and one explicit horizon
remainder.  The latter has the independent fixed-source-radius representation in
`ThetaCuspHawkingBMFixedSourceHorizon`.
-/

namespace RHTower.D4BMCorrectedFutureFixedArmDecomposition

open D4BMJointSource D4BMModularCore D4BMFullSourceAdvanced D4BMFutureHorizon
open D4BMFuturePulseAdmission D4BMFutureSourceBridge D4BMFutureSeedHorizon
open D4BMCompleteOriginalWeakSource
noncomputable section
set_option autoImplicit false

/-- Exact physical-interior reduction of the literal corrected future field to the
compact pulse response and its one remaining horizon term. -/
theorem correctedFutureField_pulse_cap_decomposition (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (tau : ℝ) (depth : NNReal) (X k : ℝ) :
    parameter q branch*
        correctedFutureField q branch amp ((tau, -(depth : ℝ)), X + Complex.I*k) =
      D4BMFuturePulseAdmission.response q branch amp tau (-(depth : ℝ)) X k+
        (parameter q branch*timeLiftField q branch amp tau (-(depth : ℝ)) ![X, Real.exp k]-
          timeAngularSeedField q branch amp tau (-(depth : ℝ)) ![X, Real.exp k])+
        (seedCapField q branch amp tau (-(depth : ℝ)) X k-
          parameter q branch*capBoundaryField q branch amp tau (-(depth : ℝ)) X k) := by
  have hbalance := future_source_balance q branch amp tau depth X k
  change parameter q branch*
      (timeLiftField q branch amp tau (-(depth : ℝ)) ![X, Real.exp k]+
        D4BMFullSourceAdvanced.response q branch amp tau (-(depth : ℝ)) X k-
        capBoundaryField q branch amp tau (-(depth : ℝ)) X k) = _
  linear_combination hbalance

end
end RHTower.D4BMCorrectedFutureFixedArmDecomposition
