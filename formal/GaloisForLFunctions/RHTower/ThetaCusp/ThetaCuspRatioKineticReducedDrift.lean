import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticControlSource
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticDriftReader
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity


def clockDriftZeroCoord : Coord → Poly
  | .U => X .U
  | .K => 0
  | .J => X .J

def clockDriftZero : Poly →+* Poly := eval₂Hom C clockDriftZeroCoord

@[simp] theorem clockDriftZero_C (c : ℂ) : clockDriftZero (C c)=C c := by
  simp [clockDriftZero]
@[simp] theorem clockDriftZero_X (i : Coord) : clockDriftZero (X i)=clockDriftZeroCoord i := by
  simp [clockDriftZero]

theorem clockDriftZero_eval (P : Poly) (h v z : ℂ) :
    eval (basePoint h v z) (clockDriftZero P)=eval (basePoint h 0 z) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => cases i <;> simp [hp,clockDriftZeroCoord,basePoint]

theorem clearSlope_driftZero : clockDriftZero clearSlope=0 := by
  apply polynomial_ext_clock_nonzero
  intro h v z hh
  rw [clockDriftZero_eval,clearSlope_eval h 0 z hh,slope_seam_factor]
  simp only [map_mul,eval_X,basePoint,zero_mul,mul_zero,map_zero]

theorem clearSlope_zero_drift (h z : ℂ) : eval (basePoint h 0 z) clearSlope=0 := by
  rw [←clockDriftZero_eval clearSlope h 0 z,clearSlope_driftZero,map_zero]

theorem completeKineticSlope_zero_drift (h : ℂ) :
    completeKineticSlope.map (eval (basePoint h 0 0))=0 := by
  apply Polynomial.funext
  intro z
  rw [Polynomial.eval_map,Polynomial.eval_zero]
  change kineticEvaluate h 0 z completeKineticSlope=0
  rw [completeKineticSlope_evaluate,clearSlope_zero_drift]

theorem completeKineticSlope_drift_constant (h : ℂ) (j : ℕ) :
    (driftReader h (completeKineticSlope.coeff j)).coeff 0=0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero,driftReader_eval]
  have he := congrArg (fun P : Polynomial ℂ => P.coeff j) (completeKineticSlope_zero_drift h)
  simpa only [Polynomial.coeff_map,Polynomial.coeff_zero] using he

def reducedKineticDriftCoefficient (h : ℂ) (j : ℕ) : Polynomial ℂ :=
  (driftReader h (completeKineticSlope.coeff j)).divX

theorem completeKineticSlope_drift_factor (h : ℂ) (j : ℕ) :
    driftReader h (completeKineticSlope.coeff j)=
      Polynomial.X*reducedKineticDriftCoefficient h j := by
  have he := Polynomial.X_mul_divX_add (driftReader h (completeKineticSlope.coeff j))
  rw [completeKineticSlope_drift_constant,Polynomial.C_0,add_zero] at he
  exact he.symm

theorem reducedKineticDriftCoefficient_coeff (h : ℂ) (j b : ℕ) :
    (reducedKineticDriftCoefficient h j).coeff b=
      (driftReader h (completeKineticSlope.coeff j)).coeff (b+1) :=
  Polynomial.coeff_divX

theorem completeKineticSlope_reduced_coefficient (h v : ℂ) (j : ℕ) :
    eval (basePoint h v 0) (completeKineticSlope.coeff j)=
      v*(reducedKineticDriftCoefficient h j).eval v := by
  rw [←driftReader_eval,completeKineticSlope_drift_factor]
  simp only [Polynomial.eval_mul,Polynomial.eval_X]

theorem completeKineticSlope_reduced_expansion (h v z : ℂ) :
    eval (basePoint h v z) clearSlope=
      v*∑ j ∈ Finset.range 20,(reducedKineticDriftCoefficient h j).eval v*z^j := by
  rw [completeKineticSlope_evaluated_expansion,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [completeKineticSlope_reduced_coefficient,mul_assoc]

def reducedKineticCoefficient (h v : ℝ) (j : ℕ) : ℝ :=
  ((reducedKineticDriftCoefficient (h:ℂ) j).eval (v:ℂ)).re

def reducedKineticValue (h v z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 20,reducedKineticCoefficient h v j*z^j

def reducedKineticControl (h v Z : ℝ) : ℕ → ℝ :=
  kineticControl 19 (fun j => reducedKineticCoefficient h v j*Z^j)

theorem completeKineticCoefficient_reduced (h v : ℝ) (j : ℕ) :
    completeKineticCoefficient h v j=v*reducedKineticCoefficient h v j := by
  have he := congrArg Complex.re (completeKineticSlope_reduced_coefficient (h:ℂ) (v:ℂ) j)
  simpa only [completeKineticCoefficient,reducedKineticCoefficient,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using he

theorem completeKineticValue_reduced (h v z : ℝ) :
    completeKineticValue h v z=v*reducedKineticValue h v z := by
  rw [completeKineticValue_expansion,reducedKineticValue,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [completeKineticCoefficient_reduced,mul_assoc]

theorem completeKineticControl_reduced (h v Z : ℝ) (i : ℕ) :
    completeKineticControl h v Z i=v*reducedKineticControl h v Z i := by
  simp only [completeKineticControl,reducedKineticControl,kineticControl,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [completeKineticCoefficient_reduced]
  ring

theorem reducedKineticControl_reconstruction (h v Z e : ℝ) :
    kineticBernstein 19 (reducedKineticControl h v Z) e=
      reducedKineticValue h v (e*Z) := by
  rw [reducedKineticControl,kineticControl_reconstruction,reducedKineticValue]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_pow]
  ring

theorem reducedKineticControl_boundary (h v Z : ℝ) :
    reducedKineticControl h v Z 19=reducedKineticValue h v Z := by
  rw [reducedKineticControl,kineticControl_last,reducedKineticValue]

theorem reduced_source_control_difference (h v Z e : ℝ) :
    reducedKineticValue h v (e*Z)-reducedKineticValue h v Z=
      (1-e)*kineticBernsteinDifference 19 (reducedKineticControl h v Z) e := by
  rw [←reducedKineticControl_reconstruction,←reducedKineticControl_boundary,
    complete_bernstein_difference]

end
end HTGeometry.ThetaRatioKineticContraction
