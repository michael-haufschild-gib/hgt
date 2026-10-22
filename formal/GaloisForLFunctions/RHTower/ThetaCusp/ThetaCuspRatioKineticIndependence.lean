import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticModel
import GaloisForLFunctions.HTGeometry.MvPolynomialSmooth
import Mathlib.Analysis.Calculus.MeanValue
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

theorem kinetic_partial (P : Poly) (h v z : ℂ) :
    HasDerivAt (fun t => eval (basePoint h v t) P)
      (eval (basePoint h v z) (pderiv Coord.J P)) z := by
  have hd : HasDerivAt (fun t => basePoint h v t)
      (fun i => if i=Coord.J then (1:ℂ) else 0) z := by
    apply hasDerivAt_pi.mpr
    intro i
    cases i with
    | U => simpa [basePoint] using hasDerivAt_const z h
    | K => simpa [basePoint] using hasDerivAt_const z v
    | J =>
      convert hasDerivAt_id z using 1 <;> rfl
  have he := GaloisForLFunctions.HTGeometry.hasDerivAt_mvPolynomial_eval_comp P hd
  simpa [Finset.sum_ite_eq'] using he

theorem kinetic_independent (P : Poly) (hP : pderiv Coord.J P=0) (h v z w : ℂ) :
    eval (basePoint h v z) P=eval (basePoint h v w) P := by
  have he (t : ℂ) : HasDerivAt (fun u => eval (basePoint h v u) P) 0 t := by
    simpa only [hP,map_zero] using kinetic_partial P h v t
  exact is_const_of_deriv_eq_zero (fun t => (he t).differentiableAt)
    (fun t => (he t).deriv) z w

theorem kinetic_mixed_partial (P : Poly) (i j : Coord) :
    pderiv i (pderiv j P)=pderiv j (pderiv i P) := by
  have hX (a b k : Coord) : pderiv a (pderiv b (X k : Poly))=0 := by
    simp only [pderiv_X,Pi.single_apply]
    split_ifs <;> simp
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p k hp =>
    simp only [pderiv_mul,map_add,hp,hX,mul_zero,add_zero]
    ring

theorem kineticUp_noJ (d : ℕ) (c : Poly) (hc : pderiv Coord.J c=0) :
    pderiv Coord.J (kineticUp d c)=0 := by
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have hu : pderiv Coord.J (pderiv Coord.U c)=0 := by rw [kinetic_mixed_partial,hc,map_zero]
  norm_num [kineticUp,pderiv_X,Pi.single_apply,hJU,hJK,hc,hu]

theorem kineticStay_noJ (j : ℕ) (c : Poly) (hc : pderiv Coord.J c=0) :
    pderiv Coord.J (kineticStay j c)=0 := by
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have hk : pderiv Coord.J (pderiv Coord.K c)=0 := by rw [kinetic_mixed_partial,hc,map_zero]
  norm_num [kineticStay,pderiv_X,Pi.single_apply,hJU,hJK,hc,hk]

theorem kineticDown_noJ (j : ℕ) (c : Poly) (hc : pderiv Coord.J c=0) :
    pderiv Coord.J (kineticDown j c)=0 := by
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [kineticDown,pderiv_X,Pi.single_apply,hJU,hJK,hc]

theorem kineticSlopeUp_noJ (d : ℕ) (c : Poly) (hc : pderiv Coord.J c=0) :
    pderiv Coord.J (kineticSlopeUp d c)=0 := by
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [kineticSlopeUp,pderiv_X,Pi.single_apply,hJU,hJK,hc,kineticUp_noJ d c hc]

end
end HTGeometry.ThetaRatioKineticContraction
