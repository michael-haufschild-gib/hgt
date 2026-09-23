import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalResolventAssembly
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCompleteAngularSourceBounds

/-! The finite resolvent assembly satisfies the literal complete-source equation, including angular collisions. -/
open Complex Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Re-expressing a principal equation at the physical target retains its exact eigenvalue difference. -/
theorem continuedPrincipalDifference_physical_equation (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (i : Fin 3) (t : ℝ) (ht : t < 0) :
    w^(2 : ℕ)*continuedPrincipalDifference q branch w a i t-continuedPrincipalDifferenceSecond q branch w a i t+
      (horizonCoordinate t:ℂ)*(1/4+physicalRadialFrequency r^(2 : ℕ))*continuedPrincipalDifference q branch w a i t =
        reducedCoefficient (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t*principalAmplitude q i+
        physicalAngularGap q r i*(horizonCoordinate t:ℂ)*continuedPrincipalDifference q branch w a i t := by
  have he := continuedPrincipalDifference_equation q branch w a hwi (by linarith) i
    (connection_ne_zero (principalChamber_of_three_halves q w hd i)) t ht
  rw [continuedPrincipalDifference_secondDerivative q branch w a hwi (by linarith) i t ht] at he
  dsimp only [physicalAngularGap]
  linear_combination he

/-- All four original source channels survive the finite resolvent identity, without a noncollision premise. -/
theorem clearedPhysicalGreen_equation (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (t : ℝ) (ht : t < 0) :
    w^(2 : ℕ)*clearedPhysicalGreen q r branch w a t-clearedPhysicalGreenSecond q r branch w a t+
      (horizonCoordinate t:ℂ)*(1/4+physicalRadialFrequency r^(2 : ℕ))*clearedPhysicalGreen q r branch w a t =
        physicalAngularGapProduct q r*continuedAngularSourceProjection q branch (physicalAngularParameter r) a w t := by
  have hM (J : ℂ) := continuedReducedGreen_equation w (physicalRadialFrequency r) (physicalRate q branch) a J
    hwi (by linarith) (connection_ne_zero (physicalRadialFrequency_chamber r w (by linarith))) t ht
  have hV (i : Fin 3) := continuedPrincipalDifference_physical_equation q r branch w a hd hwi i t ht
  have hgap (i : Fin 3) := physicalAngularGapCofactor_mul q r i
  rw [continuedAngularSourceProjection_eq]
  dsimp only [clearedPhysicalGreen,clearedPhysicalGreenSecond,physicalResolventAssembly,continuedCutoffRadialCoefficient]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
  linear_combination
    physicalAngularGapProduct q r*hM (scalarResidualPeriod q (physicalAngularParameter r))+
    (physicalAngularGapCofactor q r 0*scalarCutoffPeriod (physicalAngularParameter r) (principalExponent q 0))*
      (hV 0-hM (principalAmplitude q 0))+
    (physicalAngularGapCofactor q r 1*scalarCutoffPeriod (physicalAngularParameter r) (principalExponent q 1))*
      (hV 1-hM (principalAmplitude q 1))+
    (physicalAngularGapCofactor q r 2*scalarCutoffPeriod (physicalAngularParameter r) (principalExponent q 2))*
      (hV 2-hM (principalAmplitude q 2))+
    (scalarCutoffPeriod (physicalAngularParameter r) (principalExponent q 0)*(horizonCoordinate t:ℂ)*
      continuedPrincipalDifference q branch w a 0 t)*hgap 0+
    (scalarCutoffPeriod (physicalAngularParameter r) (principalExponent q 1)*(horizonCoordinate t:ℂ)*
      continuedPrincipalDifference q branch w a 1 t)*hgap 1+
    (scalarCutoffPeriod (physicalAngularParameter r) (principalExponent q 2)*(horizonCoordinate t:ℂ)*
      continuedPrincipalDifference q branch w a 2 t)*hgap 2

end
end RHTower.D4BMJointSource
