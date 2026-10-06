import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceRow2
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceRow3
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceRow4
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceRow5
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceRow6
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceRow7
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceRow8
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceRow9
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceRow10
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceRow11
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceRow12
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceRow13
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceRow14
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceRow15
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceRow16
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceRow17
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceRow18
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceRow19
import Mathlib.Analysis.Convex.Deriv
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

theorem higherKineticDriftConstant_zero (h : ℂ) (j : ℕ) (hj0 : 2 ≤ j) (hj1 : j < 20) :
    (reducedKineticDriftCoefficient h j).coeff 0=0 := by
  rw [reducedKineticDriftCoefficient_coeff]
  change kineticDriftCell h completeKineticSlope j 1=0
  interval_cases j
  · exact kineticSourceCoeff2Row1_zero h
  · exact kineticSourceCoeff3Row1_zero h
  · exact kineticSourceCoeff4Row1_zero h
  · exact kineticSourceCoeff5Row1_zero h
  · exact kineticSourceCoeff6Row1_zero h
  · exact kineticSourceCoeff7Row1_zero h
  · exact kineticSourceCoeff8Row1_zero h
  · exact kineticSourceCoeff9Row1_zero h
  · exact kineticSourceCoeff10Row1_zero h
  · exact kineticSourceCoeff11Row1_zero h
  · exact kineticSourceCoeff12Row1_zero h
  · exact kineticSourceCoeff13Row1_zero h
  · exact kineticSourceCoeff14Row1_zero h
  · exact kineticSourceCoeff15Row1_zero h
  · exact kineticSourceCoeff16Row1_zero h
  · exact kineticSourceCoeff17Row1_zero h
  · exact kineticSourceCoeff18Row1_zero h
  · exact kineticSourceCoeff19Row1_zero h

def higherKineticCoefficient (h v : ℝ) (j : ℕ) : ℝ :=
  (((reducedKineticDriftCoefficient (h:ℂ) (j+2)).divX).eval (v:ℂ)).re

theorem higherKineticCoefficient_expansion (h v : ℝ) (j : ℕ) :
    higherKineticCoefficient h v j=
      ∑ b ∈ Finset.range 9,
        (kineticDriftCell (h:ℂ) completeKineticSlope (j+2) (b+2)).re*v^b := by
  have hc (b : ℕ) : ((reducedKineticDriftCoefficient (h:ℂ) (j+2)).divX).coeff b=
      kineticDriftCell (h:ℂ) completeKineticSlope (j+2) (b+2) := by
    rw [Polynomial.coeff_divX,reducedKineticDriftCoefficient_coeff]
    rfl
  have hd : ((reducedKineticDriftCoefficient (h:ℂ) (j+2)).divX).natDegree≤8 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro b hb
    rw [hc]
    exact completeKineticSlope_drift_bound (h:ℂ) (j+2) (b+2) (by omega)
  have he : ((reducedKineticDriftCoefficient (h:ℂ) (j+2)).divX).eval (v:ℂ)=
      ∑ b ∈ Finset.range 9,
        kineticDriftCell (h:ℂ) completeKineticSlope (j+2) (b+2)*(v:ℂ)^b := by
    rw [Polynomial.eval_eq_sum_range' (show
      ((reducedKineticDriftCoefficient (h:ℂ) (j+2)).divX).natDegree<9 by omega)]
    simp only [hc]
  have hr := congrArg Complex.re he
  simpa only [higherKineticCoefficient,Complex.re_sum,Complex.mul_re,
    ←Complex.ofReal_pow,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] using hr

theorem higherKineticCoefficient_factor (h v : ℝ) (j : ℕ) (hj : j < 18) :
    reducedKineticCoefficient h v (j+2)=v*higherKineticCoefficient h v j := by
  have he := Polynomial.X_mul_divX_add (reducedKineticDriftCoefficient (h:ℂ) (j+2))
  rw [higherKineticDriftConstant_zero _ _ (by omega) (by omega),Polynomial.C_0,add_zero] at he
  have hr := congrArg (fun P : Polynomial ℂ => (P.eval (v:ℂ)).re) he
  simpa only [Polynomial.eval_mul,Polynomial.eval_X,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,reducedKineticCoefficient,higherKineticCoefficient] using hr.symm

def higherKineticValue (h v z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 18,higherKineticCoefficient h v j*z^j

theorem reducedKineticValue_affine_drift_split (h v z : ℝ) :
    reducedKineticValue h v z=reducedKineticCoefficient h v 0+
      reducedKineticCoefficient h v 1*z+v*z^2*higherKineticValue h v z := by
  unfold reducedKineticValue higherKineticValue
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  rw [higherKineticCoefficient_factor h v 0 (by omega),higherKineticCoefficient_factor h v 1 (by omega),higherKineticCoefficient_factor h v 2 (by omega),higherKineticCoefficient_factor h v 3 (by omega),higherKineticCoefficient_factor h v 4 (by omega),higherKineticCoefficient_factor h v 5 (by omega),higherKineticCoefficient_factor h v 6 (by omega),higherKineticCoefficient_factor h v 7 (by omega),higherKineticCoefficient_factor h v 8 (by omega),higherKineticCoefficient_factor h v 9 (by omega),higherKineticCoefficient_factor h v 10 (by omega),higherKineticCoefficient_factor h v 11 (by omega),higherKineticCoefficient_factor h v 12 (by omega),higherKineticCoefficient_factor h v 13 (by omega),higherKineticCoefficient_factor h v 14 (by omega),higherKineticCoefficient_factor h v 15 (by omega),higherKineticCoefficient_factor h v 16 (by omega),higherKineticCoefficient_factor h v 17 (by omega)]
  ring

def reducedKineticSlopeValue (h v z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 19,(j+1:ℝ)*reducedKineticCoefficient h v (j+1)*z^j

def reducedKineticCurvatureValue (h v z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 18,(j+1:ℝ)*(j+2:ℝ)*reducedKineticCoefficient h v (j+2)*z^j

def reducedKineticCurvatureCore (h v z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 18,(j+1:ℝ)*(j+2:ℝ)*higherKineticCoefficient h v j*z^j

theorem reducedKineticCurvatureCore_drift_tensor (h v z : ℝ) :
    reducedKineticCurvatureCore h v z=
      ∑ j ∈ Finset.range 18,(j+1:ℝ)*(j+2:ℝ)*
        (∑ b ∈ Finset.range 9,
          (kineticDriftCell (h:ℂ) completeKineticSlope (j+2) (b+2)).re*v^b)*z^j := by
  simp only [reducedKineticCurvatureCore,higherKineticCoefficient_expansion]

theorem reducedKineticCurvatureValue_drift_factor (h v z : ℝ) :
    reducedKineticCurvatureValue h v z=v*reducedKineticCurvatureCore h v z := by
  unfold reducedKineticCurvatureValue reducedKineticCurvatureCore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [higherKineticCoefficient_factor h v j (Finset.mem_range.mp hj)]
  ring

theorem reducedKineticValue_hasDerivAt (h v z : ℝ) :
    HasDerivAt (reducedKineticValue h v) (reducedKineticSlopeValue h v z) z := by
  have hs := HasDerivAt.fun_sum (u := Finset.range 20) (fun j _ =>
    ((hasDerivAt_id z).pow j).const_mul (reducedKineticCoefficient h v j))
  apply hs.congr_deriv
  norm_num [reducedKineticSlopeValue,Finset.sum_range_succ]
  ring

theorem reducedKineticSlopeValue_hasDerivAt (h v z : ℝ) :
    HasDerivAt (reducedKineticSlopeValue h v) (reducedKineticCurvatureValue h v z) z := by
  have hs := HasDerivAt.fun_sum (u := Finset.range 19) (fun j _ =>
    ((hasDerivAt_id z).pow j).const_mul ((j+1:ℝ)*reducedKineticCoefficient h v (j+1)))
  apply hs.congr_deriv
  norm_num [reducedKineticCurvatureValue,Finset.sum_range_succ]
  ring

theorem reducedKineticValue_second_derivative (h v : ℝ) :
    deriv (deriv (reducedKineticValue h v))=fun z => v*reducedKineticCurvatureCore h v z := by
  have hd : deriv (reducedKineticValue h v)=reducedKineticSlopeValue h v := by
    funext z
    exact (reducedKineticValue_hasDerivAt h v z).deriv
  rw [hd]
  funext z
  rw [(reducedKineticSlopeValue_hasDerivAt h v z).deriv,reducedKineticCurvatureValue_drift_factor]

end
end HTGeometry.ThetaRatioKineticContraction
