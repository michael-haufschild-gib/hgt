import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticCurvature
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def negKineticCurvatureControl (h v Z : ℝ) : ℕ → ℝ :=
  kineticControl 17 (fun j => -((j+1:ℝ)*(j+2:ℝ))*higherKineticCoefficient h v j*Z^j)

def negKineticCurvatureControlDriftCell (h Z : ℝ) (i b : ℕ) : ℝ :=
  ∑ j ∈ Finset.range 18,-((j+1:ℝ)*(j+2:ℝ))*
    (kineticDriftCell (h:ℂ) completeKineticSlope (j+2) (b+2)).re*Z^j*
      degreeElevationCoefficient 17 j i

theorem negKineticCurvatureControl_drift_expansion (h v Z : ℝ) (i : ℕ) :
    negKineticCurvatureControl h v Z i=
      ∑ b ∈ Finset.range 9,negKineticCurvatureControlDriftCell h Z i b*v^b := by
  unfold negKineticCurvatureControl kineticControl negKineticCurvatureControlDriftCell
  simp_rw [higherKineticCoefficient_expansion]
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem negKineticCurvatureControl_reconstruction (h v Z e : ℝ) :
    kineticBernstein 17 (negKineticCurvatureControl h v Z) e=
      -reducedKineticCurvatureCore h v (e*Z) := by
  rw [negKineticCurvatureControl,kineticControl_reconstruction,reducedKineticCurvatureCore,
    ←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_pow]
  ring

theorem negKineticCurvatureControl_terminal (h v Z : ℝ) :
    negKineticCurvatureControl h v Z 17 = -reducedKineticCurvatureCore h v Z := by
  unfold negKineticCurvatureControl kineticControl reducedKineticCurvatureCore
  norm_num [Finset.sum_range_succ, degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  ring

end
end HTGeometry.ThetaRatioKineticContraction
