import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticClockMoment2
/-! Exact inverse-clock values and full source derivatives, retaining every moment term. -/

namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def clearMoment6Part0 : Poly := (((((X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-8338360320)) + (((X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-90870584832)) + ((X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(31536096768)))) + (((X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-934861824)) + (((X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(21026304)) + ((X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-32045393664))))) + ((((X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-4303176192)) + (((X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(149154048)) + ((X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(3321160704)))) + (((X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(377478144)) + (((X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(4911197184)) + ((X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(-127650816))))))

theorem clearMoment6Part0_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment6Part0=h^7*eval (basePoint v h⁻¹ z) moment6Part0 := by
  norm_num [clearMoment6Part0,moment6Part0,basePoint]
  field_simp [hh]

theorem clearMoment6Part0_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 7 clearMoment6Part0)=
      h^9*eval (basePoint v h⁻¹ z) (squareLie moment6Part0) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment6Part0,moment6Part0,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment6Part1 : Poly := (((((X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(-232906752)) + (((X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((0+6)/2)*(X Coord.J : Poly)^6*(-107495424)) + ((X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(1239681024)))) + (((X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-54120960)) + (((X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-262125911808)) + ((X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(98870035968))))) + ((((X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(1579585536)) + (((X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-73446912)) + ((X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-6505152768)))) + (((X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-17677398528)) + (((X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-85536000)) + ((X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(-11663253504))))))

theorem clearMoment6Part1_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment6Part1=h^7*eval (basePoint v h⁻¹ z) moment6Part1 := by
  norm_num [clearMoment6Part1,moment6Part1,basePoint]
  field_simp [hh]

theorem clearMoment6Part1_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 7 clearMoment6Part1)=
      h^9*eval (basePoint v h⁻¹ z) (squareLie moment6Part1) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment6Part1,moment6Part1,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment6Part2 : Poly := (((((X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(1206337536)) + (((X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(886837248)) + ((X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(1155575808)))) + (((X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(537477120)) + (((X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-5641643520)) + ((X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(110419200))))) + ((((X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(1492992)) + (((X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-203900763456)) + ((X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(50993141760)))) + (((X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(15311379456)) + (((X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-151041024)) + ((X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-16144468992))))))

theorem clearMoment6Part2_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment6Part2=h^7*eval (basePoint v h⁻¹ z) moment6Part2 := by
  norm_num [clearMoment6Part2,moment6Part2,basePoint]
  field_simp [hh]

theorem clearMoment6Part2_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 7 clearMoment6Part2)=
      h^9*eval (basePoint v h⁻¹ z) (squareLie moment6Part2) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment6Part2,moment6Part2,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment6Part3 : Poly := (((((X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(7874039808)) + (((X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-1541514240)) + ((X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(-1370566656)))) + (((X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(-1818464256)) + (((X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(241864704)) + ((X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(-1101828096))))) + ((((X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-47910346560)) + (((X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(1067535936)) + ((X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-18035136)))) + (((X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-122353307136)) + (((X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(39484412928)) + ((X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-2002102272))))))

theorem clearMoment6Part3_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment6Part3=h^7*eval (basePoint v h⁻¹ z) moment6Part3 := by
  norm_num [clearMoment6Part3,moment6Part3,basePoint]
  field_simp [hh]

theorem clearMoment6Part3_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 7 clearMoment6Part3)=
      h^9*eval (basePoint v h⁻¹ z) (squareLie moment6Part3) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment6Part3,moment6Part3,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment6Part4 : Poly := (((((X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(750228480)) + (((X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-3083774976)) + ((X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-524040192)))) + (((X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(1350411264)) + (((X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(-967458816)) + ((X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(1182449664))))) + ((((X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-15444069120)) + (((X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-4425228288)) + ((X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(93747456)))) + (((X Coord.U : Poly)^(7-5)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(952342272)) + (((X Coord.U : Poly)^(7-5)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(6167549952)) + ((X Coord.U : Poly)^(7-5)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(1612431360))))))

theorem clearMoment6Part4_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment6Part4=h^7*eval (basePoint v h⁻¹ z) moment6Part4 := by
  norm_num [clearMoment6Part4,moment6Part4,basePoint]
  field_simp [hh]

theorem clearMoment6Part4_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 7 clearMoment6Part4)=
      h^9*eval (basePoint v h⁻¹ z) (squareLie moment6Part4) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment6Part4,moment6Part4,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment6Part5 : Poly := (((((X Coord.U : Poly)^(7-5)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-488208384)) + (((X Coord.U : Poly)^(7-5)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(1451188224)) + ((X Coord.U : Poly)^(7-5)*(X Coord.K : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-698720256)))) + (((X Coord.U : Poly)^(7-5)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-23657391360)) + (((X Coord.U : Poly)^(7-5)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(915390720)) + ((X Coord.U : Poly)^(7-5)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-151352064))))) + ((((X Coord.U : Poly)^(7-6)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-967458816)) + (((X Coord.U : Poly)^(7-6)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(214990848)) + ((X Coord.U : Poly)^(7-6)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-3083774976)))) + (((X Coord.U : Poly)^(7-6)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-604661760)) + (((X Coord.U : Poly)^(7-6)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(69424128)) + ((X Coord.U : Poly)^(7-7)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(241864704))))))

theorem clearMoment6Part5_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment6Part5=h^7*eval (basePoint v h⁻¹ z) moment6Part5 := by
  norm_num [clearMoment6Part5,moment6Part5,basePoint]
  field_simp [hh]

theorem clearMoment6Part5_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 7 clearMoment6Part5)=
      h^9*eval (basePoint v h⁻¹ z) (squareLie moment6Part5) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment6Part5,moment6Part5,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment6Part6 : Poly := (((((X Coord.U : Poly)^(7-7)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-26873856)) + (((X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(953026560)) + ((X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(112637952)))) + (((X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-1990656)) + (((X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-10518875136)) + ((X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(833836032))))) + ((((X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-17418240)) + (((X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(2364152832)) + ((X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(-90160128)))) + (((X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(1547486208)) + (((X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(-211756032)) + ((X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(-137355264))))))

theorem clearMoment6Part6_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment6Part6=h^7*eval (basePoint v h⁻¹ z) moment6Part6 := by
  norm_num [clearMoment6Part6,moment6Part6,basePoint]
  field_simp [hh]

theorem clearMoment6Part6_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 7 clearMoment6Part6)=
      h^9*eval (basePoint v h⁻¹ z) (squareLie moment6Part6) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment6Part6,moment6Part6,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment6Part7 : Poly := ((((X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((0+6)/2)*(X Coord.J : Poly)^6*(-35831808)) + ((X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-167712768))) + (((X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(5971968)) + ((X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(0))))

theorem clearMoment6Part7_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment6Part7=h^7*eval (basePoint v h⁻¹ z) moment6Part7 := by
  norm_num [clearMoment6Part7,moment6Part7,basePoint]
  field_simp [hh]

theorem clearMoment6Part7_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 7 clearMoment6Part7)=
      h^9*eval (basePoint v h⁻¹ z) (squareLie moment6Part7) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment6Part7,moment6Part7,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

end
end HTGeometry.ThetaRatioKineticContraction
