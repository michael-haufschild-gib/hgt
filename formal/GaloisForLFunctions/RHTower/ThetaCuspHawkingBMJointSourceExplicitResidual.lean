import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalEquation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceResidualAssembly

/-! Exact residual of the retained full-source lift and all three original principal Green responses. -/
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMModularCore D4BMGlobalAngularResponse D4BMHorizon D4BMAngularSeries
noncomputable section

/-- Actual independent-frequency field before the joint square-integrable correction. -/
def explicitField (q : XiZeroCopy) (branch : Bool) (w a T : ℂ) (t : ℝ) (z : Point) : ℂ :=
  radialLift (physicalRate q branch) w a T t*fullSquarePotential q z+
    ∑ i : Fin 3, principalDifference q branch w a T i t*cutoffPower (principalExponent q i) z

/-- Sum of actual separated wave expressions for the explicit field. -/
def explicitSeparatedWave (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (t : ℝ) (z : Point) : ℂ :=
  separatedScalarWave w (radialLift (physicalRate q branch) w a T) (fullSquarePotential q) t z+
    ∑ i : Fin 3, separatedScalarWave w (principalDifference q branch w a T i)
      (cutoffPower (principalExponent q i)) t z

/-- Every actual cutoff derivative appears with its original radial coefficient. -/
theorem cutoffPower_wave (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (hw : PrincipalChamber q w) (i : Fin 3) (t : ℝ) (ht : t < 0) (z : Point) (hz : 0 < z 1) :
    separatedScalarWave w (principalDifference q branch w a T i)
        (cutoffPower (principalExponent q i)) t z =
      reducedCoefficient (physicalRate q branch) w a T t*principalAmplitude q i*
        cutoff z*(z 1:ℂ)^(principalExponent q i)-
      cutoffRadialCoefficient q branch w a T i t*cutoffCommutator (principalExponent q i) z := by
  have he := principalDifference_equation q branch w a T hw i t ht
  unfold separatedScalarWave
  rw [scalarLaplacian_eq _ z hz]
  change (w^2*principalDifference q branch w a T i t-
    deriv (deriv (principalDifference q branch w a T i)) t)*cutoffPower (principalExponent q i) z-
    (1-(radialUnit t:ℂ)^2)*principalDifference q branch w a T i t*
      hyperbolicLaplacian (cutoffPower (principalExponent q i)) z = _
  dsimp only [cutoffPower,cutoffRadialCoefficient,cutoffCommutator]
  dsimp only [horizonCoordinate] at he ⊢
  push_cast at he ⊢
  linear_combination cutoff z*(z 1:ℂ)^(principalExponent q i)*he

/-- Exact source subtraction for the actual original forcing, with no omitted cusp term. -/
theorem originalForcing_explicitResidual (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (hw : PrincipalChamber q w) (t : ℝ) (ht : t < 0) (z : UpperHalfPlane) :
    originalForcing (physicalRate q branch) w a T (fullSquarePotential q (coordinates z))
        (fullGradientEnergy q (coordinates z)/2) t =
      explicitSeparatedWave q branch w a T t (coordinates z)+cuspResidualForcing q branch w a T (t,z) := by
  have hsum : (∑ i : Fin 3, separatedScalarWave w (principalDifference q branch w a T i)
      (cutoffPower (principalExponent q i)) t (coordinates z)) =
      reducedCoefficient (physicalRate q branch) w a T t*cutoff (coordinates z)*principalSquare q (coordinates z)-
      ∑ i : Fin 3, cutoffRadialCoefficient q branch w a T i t*
        cutoffCommutator (principalExponent q i) (coordinates z) := by
    simp_rw [cutoffPower_wave q branch w a T hw _ t ht (coordinates z) z.im_pos]
    rw [Finset.sum_sub_distrib,principalSquare_expansion q _ z.im_pos,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [scalar_gradient_absorption q branch w a T t _ z.im_pos]
  dsimp only [explicitSeparatedWave,cuspResidualForcing,squareResidual]
  rw [hsum]
  ring

end
end RHTower.D4BMJointSource
