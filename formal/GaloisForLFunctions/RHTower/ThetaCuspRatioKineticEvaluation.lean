import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticIndependence
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDegree
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def kineticEvaluate (h v z : ℂ) : KineticPolynomial →+* ℂ :=
  Polynomial.eval₂RingHom (eval (basePoint h v 0)) z

@[simp] theorem kineticEvaluate_C (h v z : ℂ) (c : Poly) :
    kineticEvaluate h v z (Polynomial.C c)=eval (basePoint h v 0) c := by
  simp [kineticEvaluate]

@[simp] theorem kineticEvaluate_X (h v z : ℂ) :
    kineticEvaluate h v z Polynomial.X=z := by simp [kineticEvaluate]

theorem kineticBlockTerm_evaluate (d j : ℕ) (c : Poly) (hc : pderiv Coord.J c=0)
    (h v z : ℂ) :
    kineticEvaluate h v z (kineticBlockTerm d j c)=
      eval (basePoint h v z) (kineticRead (kineticBlockTerm d j c)) := by
  simp only [kineticBlockTerm,map_add,map_mul,map_pow,kineticEvaluate_C,kineticEvaluate_X,
    kineticRead_C,kineticRead_X,map_sub,map_ofNat,eval_X,basePoint]
  rw [kinetic_independent _ (kineticSlopeUp_noJ d c hc) h v 0 z,
    kinetic_independent _ (kineticStay_noJ j c hc) h v 0 z,
    kinetic_independent _ (kineticDown_noJ j c hc) h v 0 z]

theorem kineticMoment2_evaluate (h v z : ℂ) :
    kineticEvaluate h v z kineticMoment2=eval (basePoint h v z) clearMoment2 := by
  rw [←kineticMoment2_read]
  simp only [kineticMoment2,map_add,map_mul,map_pow,kineticEvaluate_C,kineticEvaluate_X,
    kineticRead_C,kineticRead_X,eval_X,basePoint]
  rw [kinetic_independent _ clearMoment2KineticCoeff0_noJ h v 0 z,kinetic_independent _ clearMoment2KineticCoeff1_noJ h v 0 z,kinetic_independent _ clearMoment2KineticCoeff2_noJ h v 0 z]

theorem kineticBlock2_evaluate (h v z : ℂ) :
    kineticEvaluate h v z kineticBlock2=
      eval (basePoint h v z) (clockSlopeBlock 3 clearMoment2) := by
  rw [←kineticBlock2_read]
  simp only [kineticBlock2,map_add]
  rw [kineticBlockTerm_evaluate 3 0 clearMoment2KineticCoeff0 clearMoment2KineticCoeff0_noJ,kineticBlockTerm_evaluate 3 1 clearMoment2KineticCoeff1 clearMoment2KineticCoeff1_noJ,kineticBlockTerm_evaluate 3 2 clearMoment2KineticCoeff2 clearMoment2KineticCoeff2_noJ]

theorem kineticMoment4_evaluate (h v z : ℂ) :
    kineticEvaluate h v z kineticMoment4=eval (basePoint h v z) clearMoment4 := by
  rw [←kineticMoment4_read]
  simp only [kineticMoment4,map_add,map_mul,map_pow,kineticEvaluate_C,kineticEvaluate_X,
    kineticRead_C,kineticRead_X,eval_X,basePoint]
  rw [kinetic_independent _ clearMoment4KineticCoeff0_noJ h v 0 z,kinetic_independent _ clearMoment4KineticCoeff1_noJ h v 0 z,kinetic_independent _ clearMoment4KineticCoeff2_noJ h v 0 z,kinetic_independent _ clearMoment4KineticCoeff3_noJ h v 0 z,kinetic_independent _ clearMoment4KineticCoeff4_noJ h v 0 z]

theorem kineticBlock4_evaluate (h v z : ℂ) :
    kineticEvaluate h v z kineticBlock4=
      eval (basePoint h v z) (clockSlopeBlock 5 clearMoment4) := by
  rw [←kineticBlock4_read]
  simp only [kineticBlock4,map_add]
  rw [kineticBlockTerm_evaluate 5 0 clearMoment4KineticCoeff0 clearMoment4KineticCoeff0_noJ,kineticBlockTerm_evaluate 5 1 clearMoment4KineticCoeff1 clearMoment4KineticCoeff1_noJ,kineticBlockTerm_evaluate 5 2 clearMoment4KineticCoeff2 clearMoment4KineticCoeff2_noJ,kineticBlockTerm_evaluate 5 3 clearMoment4KineticCoeff3 clearMoment4KineticCoeff3_noJ,kineticBlockTerm_evaluate 5 4 clearMoment4KineticCoeff4 clearMoment4KineticCoeff4_noJ]

theorem kineticMoment6_evaluate (h v z : ℂ) :
    kineticEvaluate h v z kineticMoment6=eval (basePoint h v z) clearMoment6 := by
  rw [←kineticMoment6_read]
  simp only [kineticMoment6,map_add,map_mul,map_pow,kineticEvaluate_C,kineticEvaluate_X,
    kineticRead_C,kineticRead_X,eval_X,basePoint]
  rw [kinetic_independent _ clearMoment6KineticCoeff0_noJ h v 0 z,kinetic_independent _ clearMoment6KineticCoeff1_noJ h v 0 z,kinetic_independent _ clearMoment6KineticCoeff2_noJ h v 0 z,kinetic_independent _ clearMoment6KineticCoeff3_noJ h v 0 z,kinetic_independent _ clearMoment6KineticCoeff4_noJ h v 0 z,kinetic_independent _ clearMoment6KineticCoeff5_noJ h v 0 z,kinetic_independent _ clearMoment6KineticCoeff6_noJ h v 0 z]

theorem kineticBlock6_evaluate (h v z : ℂ) :
    kineticEvaluate h v z kineticBlock6=
      eval (basePoint h v z) (clockSlopeBlock 7 clearMoment6) := by
  rw [←kineticBlock6_read]
  simp only [kineticBlock6,map_add]
  rw [kineticBlockTerm_evaluate 7 0 clearMoment6KineticCoeff0 clearMoment6KineticCoeff0_noJ,kineticBlockTerm_evaluate 7 1 clearMoment6KineticCoeff1 clearMoment6KineticCoeff1_noJ,kineticBlockTerm_evaluate 7 2 clearMoment6KineticCoeff2 clearMoment6KineticCoeff2_noJ,kineticBlockTerm_evaluate 7 3 clearMoment6KineticCoeff3 clearMoment6KineticCoeff3_noJ,kineticBlockTerm_evaluate 7 4 clearMoment6KineticCoeff4 clearMoment6KineticCoeff4_noJ,kineticBlockTerm_evaluate 7 5 clearMoment6KineticCoeff5 clearMoment6KineticCoeff5_noJ,kineticBlockTerm_evaluate 7 6 clearMoment6KineticCoeff6 clearMoment6KineticCoeff6_noJ]

theorem kineticMoment8_evaluate (h v z : ℂ) :
    kineticEvaluate h v z kineticMoment8=eval (basePoint h v z) clearMoment8 := by
  rw [←kineticMoment8_read]
  simp only [kineticMoment8,map_add,map_mul,map_pow,kineticEvaluate_C,kineticEvaluate_X,
    kineticRead_C,kineticRead_X,eval_X,basePoint]
  rw [kinetic_independent _ clearMoment8KineticCoeff0_noJ h v 0 z,kinetic_independent _ clearMoment8KineticCoeff1_noJ h v 0 z,kinetic_independent _ clearMoment8KineticCoeff2_noJ h v 0 z,kinetic_independent _ clearMoment8KineticCoeff3_noJ h v 0 z,kinetic_independent _ clearMoment8KineticCoeff4_noJ h v 0 z,kinetic_independent _ clearMoment8KineticCoeff5_noJ h v 0 z,kinetic_independent _ clearMoment8KineticCoeff6_noJ h v 0 z,kinetic_independent _ clearMoment8KineticCoeff7_noJ h v 0 z,kinetic_independent _ clearMoment8KineticCoeff8_noJ h v 0 z]

theorem kineticBlock8_evaluate (h v z : ℂ) :
    kineticEvaluate h v z kineticBlock8=
      eval (basePoint h v z) (clockSlopeBlock 9 clearMoment8) := by
  rw [←kineticBlock8_read]
  simp only [kineticBlock8,map_add]
  rw [kineticBlockTerm_evaluate 9 0 clearMoment8KineticCoeff0 clearMoment8KineticCoeff0_noJ,kineticBlockTerm_evaluate 9 1 clearMoment8KineticCoeff1 clearMoment8KineticCoeff1_noJ,kineticBlockTerm_evaluate 9 2 clearMoment8KineticCoeff2 clearMoment8KineticCoeff2_noJ,kineticBlockTerm_evaluate 9 3 clearMoment8KineticCoeff3 clearMoment8KineticCoeff3_noJ,kineticBlockTerm_evaluate 9 4 clearMoment8KineticCoeff4 clearMoment8KineticCoeff4_noJ,kineticBlockTerm_evaluate 9 5 clearMoment8KineticCoeff5 clearMoment8KineticCoeff5_noJ,kineticBlockTerm_evaluate 9 6 clearMoment8KineticCoeff6 clearMoment8KineticCoeff6_noJ,kineticBlockTerm_evaluate 9 7 clearMoment8KineticCoeff7 clearMoment8KineticCoeff7_noJ,kineticBlockTerm_evaluate 9 8 clearMoment8KineticCoeff8 clearMoment8KineticCoeff8_noJ]

theorem kineticMoment10_evaluate (h v z : ℂ) :
    kineticEvaluate h v z kineticMoment10=eval (basePoint h v z) clearMoment10 := by
  rw [←kineticMoment10_read]
  simp only [kineticMoment10,map_add,map_mul,map_pow,kineticEvaluate_C,kineticEvaluate_X,
    kineticRead_C,kineticRead_X,eval_X,basePoint]
  rw [kinetic_independent _ clearMoment10KineticCoeff0_noJ h v 0 z,kinetic_independent _ clearMoment10KineticCoeff1_noJ h v 0 z,kinetic_independent _ clearMoment10KineticCoeff2_noJ h v 0 z,kinetic_independent _ clearMoment10KineticCoeff3_noJ h v 0 z,kinetic_independent _ clearMoment10KineticCoeff4_noJ h v 0 z,kinetic_independent _ clearMoment10KineticCoeff5_noJ h v 0 z,kinetic_independent _ clearMoment10KineticCoeff6_noJ h v 0 z,kinetic_independent _ clearMoment10KineticCoeff7_noJ h v 0 z,kinetic_independent _ clearMoment10KineticCoeff8_noJ h v 0 z,kinetic_independent _ clearMoment10KineticCoeff9_noJ h v 0 z,kinetic_independent _ clearMoment10KineticCoeff10_noJ h v 0 z]

theorem kineticBlock10_evaluate (h v z : ℂ) :
    kineticEvaluate h v z kineticBlock10=
      eval (basePoint h v z) (clockSlopeBlock 11 clearMoment10) := by
  rw [←kineticBlock10_read]
  simp only [kineticBlock10,map_add]
  rw [kineticBlockTerm_evaluate 11 0 clearMoment10KineticCoeff0 clearMoment10KineticCoeff0_noJ,kineticBlockTerm_evaluate 11 1 clearMoment10KineticCoeff1 clearMoment10KineticCoeff1_noJ,kineticBlockTerm_evaluate 11 2 clearMoment10KineticCoeff2 clearMoment10KineticCoeff2_noJ,kineticBlockTerm_evaluate 11 3 clearMoment10KineticCoeff3 clearMoment10KineticCoeff3_noJ,kineticBlockTerm_evaluate 11 4 clearMoment10KineticCoeff4 clearMoment10KineticCoeff4_noJ,kineticBlockTerm_evaluate 11 5 clearMoment10KineticCoeff5 clearMoment10KineticCoeff5_noJ,kineticBlockTerm_evaluate 11 6 clearMoment10KineticCoeff6 clearMoment10KineticCoeff6_noJ,kineticBlockTerm_evaluate 11 7 clearMoment10KineticCoeff7 clearMoment10KineticCoeff7_noJ,kineticBlockTerm_evaluate 11 8 clearMoment10KineticCoeff8 clearMoment10KineticCoeff8_noJ,kineticBlockTerm_evaluate 11 9 clearMoment10KineticCoeff9 clearMoment10KineticCoeff9_noJ,kineticBlockTerm_evaluate 11 10 clearMoment10KineticCoeff10 clearMoment10KineticCoeff10_noJ]

theorem completeKineticSlope_evaluate (h v z : ℂ) :
    kineticEvaluate h v z completeKineticSlope=eval (basePoint h v z) clearSlope := by
  rw [clearSlope_cofactors]
  simp only [completeKineticSlope,cof2_75,cof4_75,cof6_75,cof8_75,cof10_75,
    map_add,map_sub,map_mul,map_neg,map_pow,map_ofNat,
    kineticMoment2_evaluate,kineticMoment4_evaluate,kineticMoment6_evaluate,
    kineticMoment8_evaluate,kineticMoment10_evaluate,
    kineticBlock2_evaluate,kineticBlock4_evaluate,kineticBlock6_evaluate,
    kineticBlock8_evaluate,kineticBlock10_evaluate]

theorem completeKineticSlope_evaluated_expansion (h v z : ℂ) :
    eval (basePoint h v z) clearSlope=
      ∑ j ∈ Finset.range 20, eval (basePoint h v 0) (completeKineticSlope.coeff j)*z^j := by
  rw [←completeKineticSlope_evaluate]
  change completeKineticSlope.eval₂ (eval (basePoint h v 0)) z=_
  exact Polynomial.eval₂_eq_sum_range' _ (by have := completeKineticSlope_degree; omega) _

end
end HTGeometry.ThetaRatioKineticContraction
