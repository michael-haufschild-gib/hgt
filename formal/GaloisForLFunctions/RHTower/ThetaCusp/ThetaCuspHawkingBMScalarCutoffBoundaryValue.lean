import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMScalarCutoffPeriodStrip

/-! The actual scalar cutoff integral has a derived all-parameter boundary value. -/
open Set Filter Topology MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMModularCore
noncomputable section

def cutoffPowerBoundaryValue (delta k : ℂ) : ℂ :=
  (k-delta)*(4:ℂ)^(delta+k-1)+(delta*(delta-1)-k*(k-1))*cutoffBulkMoment delta k

def scalarCutoffBoundaryValue (u k : ℂ) : ℂ :=
  d4BMCompletedEisensteinCuspConstantCoefficient u false*
      cutoffPowerBoundaryValue (d4BMCompletedEisensteinCuspWeylExponent u false) k+
    d4BMCompletedEisensteinCuspConstantCoefficient u true*
      cutoffPowerBoundaryValue (d4BMCompletedEisensteinCuspWeylExponent u true) k

/-- All complex parameters: the literal quotient integral equals its derived boundary/mismatch value. -/
theorem scalarCutoffPeriod_eq_boundary_value (u k : ℂ) :
    scalarCutoffPeriod u k = scalarCutoffBoundaryValue u k := by
  rw [scalarCutoffPeriod_eq_moments,cutoffPowerMoment_eq,cutoffPowerMoment_eq]
  rfl

private theorem moment_self (k : ℂ) : cutoffPowerMoment k k = 0 := by
  rw [cutoffPowerMoment_eq]
  simp

private theorem moment_complement (k : ℂ) : cutoffPowerMoment (1-k) k = 2*k-1 := by
  rw [cutoffPowerMoment_eq]
  rw [show 1-k+k-1=0 by ring,show (1-k)*(1-k-1)-k*(k-1)=0 by ring]
  simp only [Complex.cpow_zero,mul_one,zero_mul,add_zero]
  ring

/-- On either actual indicial root, the full cutoff period is the opposite Weyl coefficient
times the original boundary Wronskian. No eigenvalue-mismatch or boundary premise is supplied. -/
theorem scalarCutoffPeriod_weyl (u : ℂ) (branch : Bool) :
    scalarCutoffPeriod u (d4BMCompletedEisensteinCuspWeylExponent u branch) =
      (2*d4BMCompletedEisensteinCuspWeylExponent u branch-1)*
        d4BMCompletedEisensteinCuspConstantCoefficient u (!branch) := by
  have hm : d4BMCompletedEisensteinCuspWeylExponent u false =
      1-d4BMCompletedEisensteinCuspWeylExponent u true := by
    norm_num [d4BMCompletedEisensteinCuspWeylExponent,d4BMCuspSign]
    ring
  have hp : d4BMCompletedEisensteinCuspWeylExponent u true =
      1-d4BMCompletedEisensteinCuspWeylExponent u false := by rw [hm]; ring
  cases branch
  · rw [scalarCutoffPeriod_eq_moments,hp,moment_self,moment_complement]
    simp only [Bool.not_false,mul_zero,zero_add]
    ring
  · rw [scalarCutoffPeriod_eq_moments,hm,moment_self,moment_complement]
    simp only [Bool.not_true,mul_zero,add_zero]
    ring

/-- The complete continued source retains all three evaluated cutoff boundary/mismatch terms. -/
theorem continuedAngularSourceProjection_eq_cutoff_boundary (q : XiZeroCopy) (branch : Bool) (u a w : ℂ) (t : ℝ) :
    continuedAngularSourceProjection q branch u a w t =
      reducedCoefficient (physicalRate q branch) w a
        (continuedOnset (physicalRate q branch) w) t*scalarResidualPeriod q u+
      ∑ i : Fin 3, continuedCutoffRadialCoefficient q branch w a i t*
        scalarCutoffBoundaryValue u (principalExponent q i) := by
  rw [continuedAngularSourceProjection_eq]
  simp_rw [scalarCutoffPeriod_eq_boundary_value]

end
end RHTower.D4BMJointSource
