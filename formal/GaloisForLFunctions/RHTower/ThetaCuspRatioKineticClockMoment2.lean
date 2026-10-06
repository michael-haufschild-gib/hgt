import GaloisForLFunctions.RHTower.ThetaCuspRatioSquareSlope
import GaloisForLFunctions.RHTower.ThetaCuspRatioInfinityFlow
/-! Exact inverse-clock values and source derivatives for the second moment. -/

namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def clockField : Coord → Poly
  | .U => -(X .U)^3*(12+4*X .U)*X .K*X .J
  | .K => 12*X .U*X .K*(9-X .K)
  | .J => 6*(9-X .K)-36*X .U-24*(X .U)^2+
      (12*X .U+8*(X .U)^2)*X .K*X .J-6*X .U*X .J*(9-X .K)

def clockLie (P : Poly) : Poly := flow clockField P

def clockFlow (d : ℕ) (P : Poly) : Poly :=
  clockLie P+C (d:ℂ)*(X Coord.U)^2*(12+4*X .U)*X .K*X .J*P

private theorem univ_coord : (Finset.univ : Finset Coord)={.U,.K,.J} := by
  ext i
  cases i <;> simp

theorem flow_expand (f : Coord → Poly) (P : Poly) :
    flow f P=pderiv Coord.U P*f .U+pderiv Coord.K P*f .K+pderiv Coord.J P*f .J := by
  simp [flow,univ_coord,Finset.sum_insert,Finset.sum_singleton,add_assoc]

theorem clockField_incidence (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockField .U)=
      -h^4*eval (basePoint v h⁻¹ z) (squareField .K) ∧
    eval (basePoint h v z) (clockField .K)=
      h^2*eval (basePoint v h⁻¹ z) (squareField .U) ∧
    eval (basePoint h v z) (clockField .J)=
      h^2*eval (basePoint v h⁻¹ z) (squareField .J) := by
  simp only [clockField,squareField,map_add,map_sub,map_neg,map_mul,map_pow,
    map_ofNat,eval_X,basePoint]
  constructor
  · field_simp [hh]
  constructor
  · field_simp [hh]
  · field_simp [hh]

def clearMoment2Part0 : Poly := (((((X Coord.U : Poly)^(3-0)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(1152)) + (((X Coord.U : Poly)^(3-1)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-1620)) + ((X Coord.U : Poly)^(3-1)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(1440)))) + (((X Coord.U : Poly)^(3-1)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-12)) + (((X Coord.U : Poly)^(3-1)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-5184)) + ((X Coord.U : Poly)^(3-2)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-31104))))) + ((((X Coord.U : Poly)^(3-2)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(8640)) + (((X Coord.U : Poly)^(3-2)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(576)) + ((X Coord.U : Poly)^(3-3)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-3888)))) + (((X Coord.U : Poly)^(3-3)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-3024)) + (((X Coord.U : Poly)^(3-0)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-480)) + ((X Coord.U : Poly)^(3-0)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-1728))))))

theorem clearMoment2Part0_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment2Part0=h^3*eval (basePoint v h⁻¹ z) moment2Part0 := by
  norm_num [clearMoment2Part0,moment2Part0,basePoint]
  field_simp [hh]

theorem clearMoment2Part0_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 3 clearMoment2Part0)=
      h^5*eval (basePoint v h⁻¹ z) (squareLie moment2Part0) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment2Part0,moment2Part0,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment2Part1 : Poly := ((X Coord.U : Poly)^(3-0)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(0))

theorem clearMoment2Part1_eval (h v z : ℂ) (_hh : h≠0) :
    eval (basePoint h v z) clearMoment2Part1=h^3*eval (basePoint v h⁻¹ z) moment2Part1 := by
  norm_num [clearMoment2Part1,moment2Part1,basePoint]

theorem clearMoment2Part1_flow (h v z : ℂ) (_hh : h≠0) :
    eval (basePoint h v z) (clockFlow 3 clearMoment2Part1)=
      h^5*eval (basePoint v h⁻¹ z) (squareLie moment2Part1) := by
  norm_num [clockFlow,clockLie,flow,clockField,clearMoment2Part1,moment2Part1,squareField,
    univ_coord,basePoint,pderiv_X,Pi.single_apply]

end
end HTGeometry.ThetaRatioKineticContraction
