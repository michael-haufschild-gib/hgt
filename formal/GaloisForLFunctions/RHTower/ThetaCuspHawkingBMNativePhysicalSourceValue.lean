import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativePhysicalPairing
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarCutoffBoundaryValue

/-! The complete original angular source at the physical scalar parameter. -/
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse D4BMModularCore
noncomputable section

/-- The actual physical projection retains the native diagonal, reflected moment and all three cutoff channels. -/
theorem continuedAngularSourceProjection_physical_value (q : XiZeroCopy)
    (hq : 1/2 < (q.1:ℂ).re) (branch : Bool) (a w : ℂ) (t : ℝ) :
    continuedAngularSourceProjection q branch (((q.1:ℂ)-1)/2) a w t =
      reducedCoefficient (physicalRate q branch) w a
        (continuedOnset (physicalRate q branch) w) t *
        ((reflectedCompletedLambda (5*(q.1:ℂ)/2-1)*reflectedCompletedLambda ((q.1:ℂ)/2)^2*
          reflectedCompletedLambda (1-3*(q.1:ℂ)/2))/2+
          reflectedCompletedLambda ((q.1:ℂ)-1)*nativePrincipalMomentContinuation q (-((q.1:ℂ)/2)))+
      ∑ i : Fin 3, continuedCutoffRadialCoefficient q branch w a i t*
        scalarCutoffBoundaryValue (((q.1:ℂ)-1)/2) (principalExponent q i) := by
  rw [continuedAngularSourceProjection_eq_cutoff_boundary,scalarResidualPeriod_physical_value q hq]

end
end RHTower.D4BMJointSource
