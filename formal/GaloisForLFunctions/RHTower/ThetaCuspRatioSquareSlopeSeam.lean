import GaloisForLFunctions.RHTower.ThetaCuspRatioSquareSlopeFactor
import GaloisForLFunctions.RHTower.ThetaCuspRatioInfinityFlow
import GaloisForLFunctions.RHTower.ThetaCuspRatioSlopeSeamSign
namespace HTGeometry.ThetaRatioSquare
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioInfinity Filter Topology


theorem shear_partial_U (P : Poly) :
    pderiv Coord.U (shear P)=shear (pderiv Coord.U P)+X Coord.J*shear (pderiv Coord.J P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add,hp,hq]; ring
  | mul_X p i hp =>
    simp only [map_mul,pderiv_mul,map_add,shear_X,hp]
    cases i <;> simp [shearCoord,pderiv_X] <;> ring

theorem shear_eval_seam (P : Poly) (k z : ℂ) :
    eval (basePoint 0 k z) (shear P)=eval (seamPoint k) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => cases i <;> simp [hp,shearCoord,basePoint,seamPoint]

theorem integerSlope_shear_factor :
    shear integerThirdSlope=X Coord.U*square reducedSlope := by
  apply mul_left_cancel₀ (MvPolynomial.X_ne_zero Coord.U)
  calc
    X Coord.U*shear integerThirdSlope=square slope := slope_eq
    _ = X Coord.U*(X Coord.U*square reducedSlope) := by
      rw [slope_seam_factor]
      simp only [map_mul,square_X,squareCoord]
      ring

theorem reducedSlope_seam_eq (k z : ℂ) :
    eval (basePoint 0 k z) reducedSlope=seamSlopeAlpha k+z*seamSlopeBeta k := by
  have he := congrArg (fun P : Poly => eval (basePoint 0 k z) (pderiv Coord.U P)) integerSlope_shear_factor
  rw [shear_partial_U] at he
  simp only [map_add,map_mul,eval_X,basePoint,shear_eval_seam,seamSlopeAlpha_eq,seamSlopeBeta_eq] at he
  simp only [pderiv_mul,pderiv_X,Pi.single_eq_same,map_add,map_mul,eval_X,basePoint,
    one_mul,zero_mul,add_zero] at he
  rw [square_eval_seam reducedSlope (basePoint 0 k z) rfl] at he
  exact he.symm

theorem reducedSlope_seam_pos {k z : ℝ} (hk0 : 5/4≤k) (hk1 : k≤19/15)
    (hz0 : 0≤z) (hz1 : z≤1/3) :
    0<(eval (basePoint 0 (k:ℂ) (z:ℂ)) reducedSlope).re := by
  rw [reducedSlope_seam_eq,←alphaReal_eq,←betaReal_eq]
  simpa using seam_tangent_cone_pos hk0 hk1 hz0 hz1

end
end HTGeometry.ThetaRatioSquare
