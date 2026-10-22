import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticCurvature
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticControlDrift
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def negKineticSlopeControl (h v Z : ℝ) : ℕ → ℝ :=
  kineticControl 18 (fun j => -(j+1:ℝ)*reducedKineticCoefficient h v (j+1)*Z^j)

def negKineticSlopeControlDriftCell (h Z : ℝ) (i b : ℕ) : ℝ :=
  ∑ j ∈ Finset.range 19,-(j+1:ℝ)*
    (kineticDriftCell (h:ℂ) completeKineticSlope (j+1) (b+1)).re*Z^j*
      degreeElevationCoefficient 18 j i

theorem negKineticSlopeControl_drift_expansion (h v Z : ℝ) (i : ℕ) :
    negKineticSlopeControl h v Z i=
      ∑ b ∈ Finset.range 10,negKineticSlopeControlDriftCell h Z i b*v^b := by
  unfold negKineticSlopeControl kineticControl negKineticSlopeControlDriftCell
  simp_rw [reducedKineticCoefficient_drift_expansion]
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem negKineticSlopeControl_reconstruction (h v Z e : ℝ) :
    kineticBernstein 18 (negKineticSlopeControl h v Z) e=
      -reducedKineticSlopeValue h v (e*Z) := by
  rw [negKineticSlopeControl,kineticControl_reconstruction,reducedKineticSlopeValue,
    ←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_pow]
  ring

theorem negKineticSlopeControl_terminal (h v Z : ℝ) :
    negKineticSlopeControl h v Z 18 = -deriv (reducedKineticValue h v) Z := by
  rw [(reducedKineticValue_hasDerivAt h v Z).deriv]
  unfold negKineticSlopeControl kineticControl reducedKineticSlopeValue
  norm_num [Finset.sum_range_succ,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
  ring

end
end HTGeometry.ThetaRatioKineticContraction

