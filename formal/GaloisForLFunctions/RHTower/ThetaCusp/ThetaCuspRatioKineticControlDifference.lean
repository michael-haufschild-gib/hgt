import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticEvaluation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticBernstein
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open Finset EvenCompactBernstein

def completeKineticCoefficient (h v : ℝ) (j : ℕ) : ℝ :=
  (eval (basePoint (h:ℂ) (v:ℂ) 0) (completeKineticSlope.coeff j)).re

def completeKineticValue (h v z : ℝ) : ℝ :=
  (eval (basePoint (h:ℂ) (v:ℂ) (z:ℂ)) clearSlope).re

theorem completeKineticValue_expansion (h v z : ℝ) :
    completeKineticValue h v z=
      ∑ j ∈ range 20, completeKineticCoefficient h v j*z^j := by
  have he := congrArg Complex.re (completeKineticSlope_evaluated_expansion (h:ℂ) (v:ℂ) (z:ℂ))
  simpa only [completeKineticValue,completeKineticCoefficient,Complex.re_sum,
    Complex.mul_re,←Complex.ofReal_pow,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero] using he

def kineticControl (n : ℕ) (a : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ range (n+1), a j*degreeElevationCoefficient n j i

theorem kineticControl_reconstruction (n : ℕ) (a : ℕ → ℝ) (e : ℝ) :
    kineticBernstein n (kineticControl n a) e=
      ∑ j ∈ range (n+1), a j*e^j := by
  unfold kineticBernstein kineticControl
  simp only [sum_mul,mul_assoc]
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [←mul_sum,monomial_bernstein_reconstruction n j (by have := mem_range.mp hj; omega)]

theorem kineticControl_last (n : ℕ) (a : ℕ → ℝ) :
    kineticControl n a n=∑ j ∈ range (n+1), a j := by
  unfold kineticControl
  apply sum_congr rfl
  intro j hj
  have hjn : j≤n := by have := mem_range.mp hj; omega
  simp [degreeElevationCoefficient,hjn]

def completeKineticControl (h v Z : ℝ) : ℕ → ℝ :=
  kineticControl 19 (fun j => completeKineticCoefficient h v j*Z^j)

theorem completeKineticControl_reconstruction (h v Z e : ℝ) :
    kineticBernstein 19 (completeKineticControl h v Z) e=
      completeKineticValue h v (e*Z) := by
  rw [completeKineticControl,kineticControl_reconstruction,completeKineticValue_expansion]
  apply sum_congr rfl
  intro j _
  rw [mul_pow]
  ring

theorem completeKineticControl_boundary (h v Z : ℝ) :
    completeKineticControl h v Z 19=completeKineticValue h v Z := by
  rw [completeKineticControl,kineticControl_last,completeKineticValue_expansion]

theorem complete_source_control_difference (h v Z e : ℝ) :
    completeKineticValue h v (e*Z)-completeKineticValue h v Z=
      (1-e)*kineticBernsteinDifference 19 (completeKineticControl h v Z) e := by
  rw [←completeKineticControl_reconstruction,←completeKineticControl_boundary,
    complete_bernstein_difference]

end
end HTGeometry.ThetaRatioKineticContraction
