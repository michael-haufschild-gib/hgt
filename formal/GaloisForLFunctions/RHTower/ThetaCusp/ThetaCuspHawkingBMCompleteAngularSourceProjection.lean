import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMScalarSourcePairingAdmission
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceFullForcingContinuation

/-! The actual scalar-field integral of the complete continued source retains all four angular channels. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology MeasureTheory D4BMModularCore D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false

/-- The actual absolutely convergent scalar-field pairing of the native angular residual. -/
def scalarResidualPeriod (q : XiZeroCopy) (u : ℂ) : ℂ :=
  ∫ z : UpperHalfPlane, scalar u (coordinates z)*squareResidual q (coordinates z) ∂D4BMModularCore.measure

/-- The actual scalar-field pairing of a complete differential cutoff commutator. -/
def scalarCutoffPeriod (u k : ℂ) : ℂ :=
  ∫ z : UpperHalfPlane, scalar u (coordinates z)*cutoffCommutator k (coordinates z) ∂D4BMModularCore.measure

/-- The literal quotient integral of the entire continued cusp source at fixed radius. -/
def continuedAngularSourceProjection (q : XiZeroCopy) (branch : Bool) (u a w : ℂ) (t : ℝ) : ℂ :=
  ∫ z : UpperHalfPlane, scalar u (coordinates z)*continuedCuspResidualForcing q branch w a (t,z)
    ∂D4BMModularCore.measure

/-- All source channels have an absolutely convergent joint angular pairing at every frequency. -/
theorem continuedAngularSourceProjection_integrable (q : XiZeroCopy) (branch : Bool) (u a w : ℂ) (t : ℝ) :
    Integrable (fun z : UpperHalfPlane => scalar u (coordinates z)*continuedCuspResidualForcing q branch w a (t,z))
      D4BMModularCore.measure := by
  have hm := (scalar_squareResidual_integrable q u).const_mul
    (reducedCoefficient (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t)
  have hc := integrable_finsetSum Finset.univ (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    (scalar_cutoffCommutator_integrable u (principalExponent q i)).const_mul
      (continuedCutoffRadialCoefficient q branch w a i t))
  apply (hm.add hc).congr
  filter_upwards with z
  dsimp [continuedCuspResidualForcing]
  rw [mul_add,Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

/-- Exact integral decomposition; the full residual and every cutoff commutator remain present. -/
theorem continuedAngularSourceProjection_eq (q : XiZeroCopy) (branch : Bool) (u a w : ℂ) (t : ℝ) :
    continuedAngularSourceProjection q branch u a w t =
      reducedCoefficient (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t*
        scalarResidualPeriod q u+
      ∑ i : Fin 3, continuedCutoffRadialCoefficient q branch w a i t*scalarCutoffPeriod u (principalExponent q i) := by
  have hm := (scalar_squareResidual_integrable q u).const_mul
    (reducedCoefficient (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t)
  have hc (i : Fin 3) := (scalar_cutoffCommutator_integrable u (principalExponent q i)).const_mul
    (continuedCutoffRadialCoefficient q branch w a i t)
  have he : (fun z : UpperHalfPlane => scalar u (coordinates z)*continuedCuspResidualForcing q branch w a (t,z)) =
      (fun z => reducedCoefficient (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t*
        (scalar u (coordinates z)*squareResidual q (coordinates z))+
        ∑ i : Fin 3, continuedCutoffRadialCoefficient q branch w a i t*
          (scalar u (coordinates z)*cutoffCommutator (principalExponent q i) (coordinates z))) := by
    funext z
    dsimp [continuedCuspResidualForcing]
    rw [mul_add,Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  rw [continuedAngularSourceProjection,he,integral_add hm (integrable_finsetSum Finset.univ (fun i _ => hc i)),
    integral_finsetSum Finset.univ (fun i _ => hc i)]
  simp only [integral_const_mul,scalarResidualPeriod,scalarCutoffPeriod]

end
end RHTower.D4BMJointSource
