import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticClockMoment2
/-! Exact inverse-clock values and full Lie derivatives of the fourth moment. -/

namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def clearMoment4Part0 : Poly := (((((X Coord.U : Poly)^(5-0)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(819072)) + (((X Coord.U : Poly)^(5-1)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(20481984)) + ((X Coord.U : Poly)^(5-1)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-6697728)))) + (((X Coord.U : Poly)^(5-1)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(158976)) + (((X Coord.U : Poly)^(5-1)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(11524032)) + ((X Coord.U : Poly)^(5-1)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(502848))))) + ((((X Coord.U : Poly)^(5-1)*(X Coord.K : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(-373248)) + (((X Coord.U : Poly)^(5-1)*(X Coord.K : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(-746496)) + ((X Coord.U : Poly)^(5-1)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-312768)))) + (((X Coord.U : Poly)^(5-2)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(70368912)) + (((X Coord.U : Poly)^(5-2)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-24603264)) + ((X Coord.U : Poly)^(5-2)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(10368))))))

theorem clearMoment4Part0_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment4Part0=h^5*eval (basePoint v h⁻¹ z) moment4Part0 := by
  norm_num [clearMoment4Part0,moment4Part0,basePoint]
  field_simp [hh]

theorem clearMoment4Part0_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 5 clearMoment4Part0)=
      h^7*eval (basePoint v h⁻¹ z) (squareLie moment4Part0) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment4Part0,moment4Part0,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment4Part1 : Poly := (((((X Coord.U : Poly)^(5-2)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(559872)) + (((X Coord.U : Poly)^(5-2)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(2177280)) + ((X Coord.U : Poly)^(5-2)*(X Coord.K : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(2239488)))) + (((X Coord.U : Poly)^(5-2)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-609120)) + (((X Coord.U : Poly)^(5-2)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(23760)) + ((X Coord.U : Poly)^(5-3)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(25894080))))) + ((((X Coord.U : Poly)^(5-3)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-4478976)) + (((X Coord.U : Poly)^(5-3)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-1866240)) + ((X Coord.U : Poly)^(5-3)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(1679616)))) + (((X Coord.U : Poly)^(5-3)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-2426112)) + (((X Coord.U : Poly)^(5-3)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(10435392)) + ((X Coord.U : Poly)^(5-3)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-165888))))))

theorem clearMoment4Part1_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment4Part1=h^5*eval (basePoint v h⁻¹ z) moment4Part1 := by
  norm_num [clearMoment4Part1,moment4Part1,basePoint]
  field_simp [hh]

theorem clearMoment4Part1_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 5 clearMoment4Part1)=
      h^7*eval (basePoint v h⁻¹ z) (squareLie moment4Part1) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment4Part1,moment4Part1,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment4Part2 : Poly := (((((X Coord.U : Poly)^(5-4)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(11337408)) + (((X Coord.U : Poly)^(5-4)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-3359232)) + ((X Coord.U : Poly)^(5-4)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(1119744)))) + (((X Coord.U : Poly)^(5-4)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(1399680)) + (((X Coord.U : Poly)^(5-4)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(451008)) + ((X Coord.U : Poly)^(5-5)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(1679616))))) + ((((X Coord.U : Poly)^(5-5)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-186624)) + (((X Coord.U : Poly)^(5-0)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(376704)) + ((X Coord.U : Poly)^(5-0)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-31104)))) + (((X Coord.U : Poly)^(5-0)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(3841344)) + (((X Coord.U : Poly)^(5-0)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-164160)) + ((X Coord.U : Poly)^(5-0)*(X Coord.K : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(-373248))))))

theorem clearMoment4Part2_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment4Part2=h^5*eval (basePoint v h⁻¹ z) moment4Part2 := by
  norm_num [clearMoment4Part2,moment4Part2,basePoint]
  field_simp [hh]

theorem clearMoment4Part2_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 5 clearMoment4Part2)=
      h^7*eval (basePoint v h⁻¹ z) (squareLie moment4Part2) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment4Part2,moment4Part2,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment4Part3 : Poly := (((X Coord.U : Poly)^(5-0)*(X Coord.K : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(-248832)) + (((X Coord.U : Poly)^(5-0)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(93312)) + ((X Coord.U : Poly)^(5-0)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(0))))

theorem clearMoment4Part3_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment4Part3=h^5*eval (basePoint v h⁻¹ z) moment4Part3 := by
  norm_num [clearMoment4Part3,moment4Part3,basePoint]
  field_simp [hh]

theorem clearMoment4Part3_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 5 clearMoment4Part3)=
      h^7*eval (basePoint v h⁻¹ z) (squareLie moment4Part3) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment4Part3,moment4Part3,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

end
end HTGeometry.ThetaRatioKineticContraction
