import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedQuadratic
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioQuadraticSlope
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioActualSlopeTail
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspModularCompensationDeterminant

namespace RHTower.ThetaRatioSourceIncidence
noncomputable section
set_option autoImplicit false
open MvPolynomial HTGeometry.ThetaRatioSource HTGeometry.ThetaRatioSquare
open HTGeometry.ThetaRatioQuadraticSource HTGeometry.ThetaRatioWeightedSquare
open HTGeometry.ThetaRatioInfinity ThetaCuspModularRatio ThetaCuspOddDirectionTransport

theorem actual_weighted_quadratic (c eta : ℝ) {x : ℝ} (hx : 0 < x) :
    eval (actualSquarePoint x) (weightedSourceQuadratic (c:ℂ) ((x/u x:ℝ):ℂ) (eta:ℂ))=
      (6:ℂ)^30*(u x:ℂ)^25*eval (state x) (sourceQuadratic (c:ℂ) (x:ℂ) (eta:ℂ)) := by
  let v : Coord → ℂ := fun i => match i with
    | .U => u x
    | .K => k x
    | .J => (J x:ℂ)/(u x:ℂ)
  have hu : (u x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)))
  have hsh : (eval v ∘ shearCoord)=state x := by
    funext i
    cases i <;> simp [shearCoord,state,v]
    field_simp [hu]
  have hsq : (eval v ∘ squareCoord)=actualSquarePoint x := by
    funext i
    cases i <;> simp [squareCoord,actualSquarePoint,v]
  have h1 (P : Poly) : eval v (shear P)=eval (state x) P := by
    simpa only [shear,coe_eval₂Hom,hsh] using (eval_assoc shearCoord v P).symm
  have h2 (P : Poly) : eval v (square P)=eval (actualSquarePoint x) P := by
    simpa only [square,coe_eval₂Hom,hsq] using (eval_assoc squareCoord v P).symm
  have he := congrArg (eval v) (weightedSourceQuadratic_eq (c:ℂ) ((x/u x:ℝ):ℂ) (eta:ℂ))
  rw [h2] at he
  simp only [map_add,map_mul,map_pow,map_ofNat,eval_C,eval_X,h1,v] at he
  rw [he]
  simp only [sourceQuadratic,map_add,map_mul,eval_C,map_ofNat]
  push_cast
  field_simp [hu]

theorem actual_weighted_quadratic_real (c eta : ℝ) {x : ℝ} (hx : 0 < x) :
    (eval (actualSquarePoint x)
      (weightedSourceQuadratic (c:ℂ) ((x/u x:ℝ):ℂ) (eta:ℂ))).re=
      (6:ℝ)^30*(u x)^25*(k x-1/6)^7*
        (deriv (normalizedBase c) x+2*deriv normalizedB x*eta+deriv normalizedD x*eta^2) := by
  rw [actual_weighted_quadratic c eta hx,normalized_source_quadratic c eta hx]
  have hp : eval (state x) (sourceJet 0)=((k x-1/6:ℝ):ℂ) := by
    rw [sourceJet_zero_eval]
    change (k x:ℂ)-1/6=((k x-1/6:ℝ):ℂ)
    push_cast
    rfl
  have hn : k x-1/6≠0 := by linarith [k_gt hx.le]
  have hden : (eval (state x) (sourceJet 0))^7=(((k x-1/6)^7:ℝ):ℂ) := by
    rw [hp,Complex.ofReal_pow]
  rw [hden,Complex.div_ofReal_re]
  have h6 : (6:ℂ)^30=(((6:ℝ)^30:ℝ):ℂ) := by norm_cast
  have hu25 : (u x:ℂ)^25=(((u x)^25:ℝ):ℂ) := by norm_cast
  rw [h6,hu25,←Complex.ofReal_mul,Complex.re_ofReal_mul]
  rw [mul_assoc ((6:ℝ)^30*(u x)^25) ((k x-1/6)^7),
    mul_comm ((k x-1/6)^7) (_ / _),div_mul_cancel₀ _ (pow_ne_zero 7 hn)]

def actualCenterUpper (x : ℝ) : ℝ := (k x-2/3-J x/u x)/4

theorem actual_center_ratio_bounds {x : ℝ} (hx : 0 < x) :
    0 < x/u x ∧ x/u x ≤ actualCenterUpper x := by
  have hu : 0 < u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
  refine ⟨div_pos hx hu,?_⟩
  have hh := center_le_retained_ratio hx.le
  unfold actualCenterUpper
  apply (div_le_iff₀ hu).mpr
  have he : (k x-2/3-J x/u x)/4*u x=(u x*(k x-2/3)-J x)/4 := by
    field_simp [hu.ne']
  rw [he]
  linarith only [hh]

end
end RHTower.ThetaRatioSourceIncidence
