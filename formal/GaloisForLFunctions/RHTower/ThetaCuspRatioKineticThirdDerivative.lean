import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticCurvature
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeControl
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def reducedKineticThirdValue (h v z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 17,
    (j+1:ℝ)*(j+2:ℝ)*(j+3:ℝ)*reducedKineticCoefficient h v (j+3)*z^j

def reducedKineticThirdCore (h v z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 17,
    (j+1:ℝ)*(j+2:ℝ)*(j+3:ℝ)*higherKineticCoefficient h v (j+1)*z^j

theorem reducedKineticCurvatureValue_hasDerivAt (h v z : ℝ) :
    HasDerivAt (reducedKineticCurvatureValue h v) (reducedKineticThirdValue h v z) z := by
  have hs := HasDerivAt.fun_sum (u := Finset.range 18) (fun j _ =>
    ((hasDerivAt_id z).pow j).const_mul
      ((j+1:ℝ)*(j+2:ℝ)*reducedKineticCoefficient h v (j+2)))
  apply hs.congr_deriv
  norm_num [reducedKineticThirdValue,Finset.sum_range_succ]
  ring

theorem reducedKineticThirdValue_drift_factor (h v z : ℝ) :
    reducedKineticThirdValue h v z=v*reducedKineticThirdCore h v z := by
  unfold reducedKineticThirdValue reducedKineticThirdCore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hc := higherKineticCoefficient_factor h v (j+1)
    (by have := Finset.mem_range.mp hj; omega)
  rw [show j+1+2=j+3 by omega] at hc
  rw [hc]
  ring

theorem reducedKineticValue_third_derivative (h v : ℝ) :
    deriv (deriv (deriv (reducedKineticValue h v)))=reducedKineticThirdValue h v := by
  have hd : deriv (reducedKineticValue h v)=reducedKineticSlopeValue h v := by
    funext z
    exact (reducedKineticValue_hasDerivAt h v z).deriv
  have hc : deriv (reducedKineticSlopeValue h v)=reducedKineticCurvatureValue h v := by
    funext z
    exact (reducedKineticSlopeValue_hasDerivAt h v z).deriv
  rw [hd,hc]
  funext z
  exact (reducedKineticCurvatureValue_hasDerivAt h v z).deriv

def kineticThirdControl (h v Z : ℝ) : ℕ → ℝ :=
  kineticControl 16 (fun j =>
    (j+1:ℝ)*(j+2:ℝ)*(j+3:ℝ)*higherKineticCoefficient h v (j+1)*Z^j)

def kineticThirdControlDriftCell (h Z : ℝ) (i b : ℕ) : ℝ :=
  ∑ j ∈ Finset.range 17,(j+1:ℝ)*(j+2:ℝ)*(j+3:ℝ)*
    (kineticDriftCell (h:ℂ) completeKineticSlope (j+3) (b+2)).re*Z^j*
      degreeElevationCoefficient 16 j i

theorem kineticThirdControl_drift_expansion (h v Z : ℝ) (i : ℕ) :
    kineticThirdControl h v Z i=
      ∑ b ∈ Finset.range 9,kineticThirdControlDriftCell h Z i b*v^b := by
  unfold kineticThirdControl kineticControl kineticThirdControlDriftCell
  simp_rw [higherKineticCoefficient_expansion]
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem kineticThirdControl_reconstruction (h v Z e : ℝ) :
    kineticBernstein 16 (kineticThirdControl h v Z) e=
      reducedKineticThirdCore h v (e*Z) := by
  rw [kineticThirdControl,kineticControl_reconstruction,reducedKineticThirdCore]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_pow]
  ring

theorem kineticThirdControl_initial (h v Z : ℝ) :
    kineticThirdControl h v Z 0=6*higherKineticCoefficient h v 1 := by
  norm_num [kineticThirdControl,kineticControl,Finset.sum_range_succ,
    degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,Nat.factorial]

theorem kineticThirdControl_terminal (h v Z : ℝ) :
    kineticThirdControl h v Z 16=reducedKineticThirdCore h v Z := by
  unfold kineticThirdControl kineticControl reducedKineticThirdCore
  norm_num [Finset.sum_range_succ,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
