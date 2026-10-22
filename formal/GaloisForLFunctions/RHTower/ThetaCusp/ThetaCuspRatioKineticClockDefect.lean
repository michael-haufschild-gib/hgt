import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticClockAlgebra
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioScaledDriftFactor
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def defectCoord : Coord → Poly
  | .U => X .U
  | .K => 9-X .K*(X .U)^2
  | .J => X .J

def defectLift : Poly →+* Poly := eval₂Hom C defectCoord

@[simp] theorem defectLift_C (c : ℂ) : defectLift (C c)=C c := by simp [defectLift]
@[simp] theorem defectLift_X (i : Coord) : defectLift (X i)=defectCoord i := by simp [defectLift]

theorem defectLift_eval (P : Poly) (h r z : ℂ) :
    eval (basePoint h r z) (defectLift P)=eval (basePoint h (9-r*h^2) z) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => cases i <;> simp [hp,defectCoord,basePoint]

def defectField : Coord → Poly
  | .U => -(X .U)^2*(12+4*X .U)*(9-X .K*(X .U)^2)*X .J
  | .K => -12*X .K*(9-X .K*(X .U)^2)+
      2*X .K*X .U*(12+4*X .U)*(9-X .K*(X .U)^2)*X .J
  | .J => -36+12*(9-X .K*(X .U)^2)*X .J+
      X .U*(6*X .K-24+8*(9-X .K*(X .U)^2)*X .J)-6*X .K*(X .U)^2*X .J

def defectLie (P : Poly) : Poly := flow defectField P

theorem defectField_incidence (i : Coord) :
    X Coord.U*defectLie (defectCoord i)=defectLift (clockField i) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  cases i <;> unfold defectLie <;> rw [flow_expand]
  all_goals apply MvPolynomial.funext
  all_goals intro v
  all_goals norm_num [defectCoord,defectField,clockField,pderiv_X,Pi.single_apply,map_ofNat,
    hUK,hUJ,hKJ,hKU,hJU,hJK]
  all_goals ring

theorem defectLie_lift (P : Poly) :
    X Coord.U*defectLie (defectLift P)=defectLift (clockLie P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [defectLie,clockLie,flow_C]
  | add p q hp hq =>
    simp only [map_add,defectLie,clockLie,flow_add] at *
    rw [mul_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,defectLie,clockLie,flow_mul,flow_X,map_add,defectLift_X] at *
    calc
      _ = (X Coord.U*flow defectField (defectLift p))*defectCoord i+
          defectLift p*(X Coord.U*flow defectField (defectCoord i)) := by ring
      _ = _ := by rw [hp,←defectLie,defectField_incidence]

theorem defectField_zero (r z : ℂ) :
    eval (basePoint 0 r z) (defectField .U)=0 ∧
    eval (basePoint 0 r z) (defectField .K)= -108*r ∧
    eval (basePoint 0 r z) (defectField .J)=36*(3*z-1) := by
  refine ⟨?_,?_,?_⟩ <;> norm_num [defectField,basePoint] <;> ring

theorem defect_zero_invariant (r z : ℂ) :
    eval (basePoint 0 r z) (defectLie (X Coord.K*(3*X Coord.J-1)))=0 := by
  unfold defectLie
  rw [flow_expand]
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  norm_num [defectField,basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  ring

theorem defectLift_pderiv (P : Poly) :
    pderiv Coord.U (defectLift P)=defectLift (pderiv Coord.U P)-
      2*X Coord.K*X Coord.U*defectLift (pderiv Coord.K P) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add,hp,hq]; ring
  | mul_X p i hp =>
    simp only [map_mul,pderiv_mul,map_add,defectLift_X,hp]
    cases i <;> norm_num [defectCoord,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU]
    all_goals ring

theorem defectLift_pderiv_zero (P : Poly) (r z : ℂ) :
    eval (basePoint 0 r z) (pderiv Coord.U (defectLift P))=
      eval (basePoint 0 9 z) (pderiv Coord.U P) := by
  rw [defectLift_pderiv]
  simp only [map_sub,map_mul,map_ofNat,eval_X,basePoint,defectLift_eval]
  norm_num

theorem clock_factor_of_zero (P : Poly)
    (hP : ∀ r z : ℂ, eval (basePoint 0 r z) P=0) :
    ∃ Q : Poly, P=X Coord.U*Q := by
  obtain ⟨Q,hQ⟩ := seamReset_division P
  have hz : seamReset P=0 := by
    apply MvPolynomial.funext
    intro v
    rw [seamReset_eval]
    have hb : (fun i => if i=Coord.U then 0 else v i)=basePoint 0 (v .K) (v .J) := by
      funext i
      cases i <;> rfl
    rw [hb,hP]
    simp
  exact ⟨Q,by simpa only [hz,add_zero] using hQ⟩

theorem clock_factor_first (P Q : Poly) (hPQ : P=X Coord.U*Q) (r z : ℂ) :
    eval (basePoint 0 r z) Q=eval (basePoint 0 r z) (pderiv Coord.U P) := by
  rw [hPQ]
  simp [pderiv_X,Pi.single_eq_same,basePoint]

end
end HTGeometry.ThetaRatioKineticContraction
