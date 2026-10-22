import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticClockMoment2
/-! Exact inverse-clock values and full source derivatives, retaining every moment term. -/

namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def clearMoment10Part0 : Poly := (((((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-312165555505201152)) + (((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-2936102282906370048)) + ((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(1818995586674982912)))) + (((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-56594005935390720)) + (((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(1534590913609728)) + ((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(-43083242274816))))) + ((((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((9+1)/2)*(X Coord.J : Poly)^1*(266524950528)) + (((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-367565196123832320)) + ((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-460966580336590848)))) + (((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(24334188461752320)) + (((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(-708382995775488)) + ((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((8+2)/2)*(X Coord.J : Poly)^2*(4615386365952))))))

theorem clearMoment10Part0_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10Part0=h^11*eval (basePoint v h⁻¹ z) moment10Part0 := by
  norm_num [clearMoment10Part0,moment10Part0,basePoint]
  field_simp [hh]

theorem clearMoment10Part0_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10Part0)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10Part0) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment10Part0,moment10Part0,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment10Part1 : Poly := (((((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(260607039842746368)) + (((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(60342327082156032)) + ((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(-4217261764313088)))) + (((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((7+3)/2)*(X Coord.J : Poly)^3*(74382549516288)) + (((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(207945326055112704)) + ((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(-57642006020308992))))) + ((((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(-5306918690930688)) + (((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((6+4)/2)*(X Coord.J : Poly)^4*(266907136573440)) + ((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(-54580396493242368)))) + (((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(3929776432349184)) + (((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((5+5)/2)*(X Coord.J : Poly)^5*(281445092425728)) + ((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((0+6)/2)*(X Coord.J : Poly)^6*(-17956085932818432))))))

theorem clearMoment10Part1_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10Part1=h^11*eval (basePoint v h⁻¹ z) moment10Part1 := by
  norm_num [clearMoment10Part1,moment10Part1,basePoint]
  field_simp [hh]

theorem clearMoment10Part1_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10Part1)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10Part1) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment10Part1,moment10Part1,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment10Part2 : Poly := (((((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((2+6)/2)*(X Coord.J : Poly)^6*(4715990223814656)) + (((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((4+6)/2)*(X Coord.J : Poly)^6*(12592873930752)) + ((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((1+7)/2)*(X Coord.J : Poly)^7*(2225170756141056)))) + (((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((3+7)/2)*(X Coord.J : Poly)^7*(-94841922650112)) + (((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((0+8)/2)*(X Coord.J : Poly)^8*(386039286595584)) + ((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((2+8)/2)*(X Coord.J : Poly)^8*(-73851936178176))))) + ((((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((1+9)/2)*(X Coord.J : Poly)^9*(-21175738564608)) + (((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((0+10)/2)*(X Coord.J : Poly)^10*(-2229025112064)) + ((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(61684770355347456)))) + (((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-197242493534208)) + (((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(80341172158464)) + ((X Coord.U : Poly)^(11-1)*(X Coord.K : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(-762883080192))))))

theorem clearMoment10Part2_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10Part2=h^11*eval (basePoint v h⁻¹ z) moment10Part2 := by
  norm_num [clearMoment10Part2,moment10Part2,basePoint]
  field_simp [hh]

theorem clearMoment10Part2_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10Part2)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10Part2) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment10Part2,moment10Part2,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment10Part3 : Poly := (((((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-9455534033560731648)) + (((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(6034557931751079936)) + ((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(77107829817212928)))) + (((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-7239659433099264)) + (((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(247320885067776)) + ((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((9+1)/2)*(X Coord.J : Poly)^1*(-3329120010240))))) + ((((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(283490304519241728)) + (((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-1830188307339214848)) + ((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(25356104889532416)))) + (((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(1132149688565760)) + (((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((8+2)/2)*(X Coord.J : Poly)^2*(-27635385434112)) + ((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(-183915869383655424))))))

theorem clearMoment10Part3_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10Part3=h^11*eval (basePoint v h⁻¹ z) moment10Part3 := by
  norm_num [clearMoment10Part3,moment10Part3,basePoint]
  field_simp [hh]

theorem clearMoment10Part3_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10Part3)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10Part3) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment10Part3,moment10Part3,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment10Part4 : Poly := (((((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(299556403542392832)) + (((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(-5141271574904832)) + ((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((7+3)/2)*(X Coord.J : Poly)^3*(-100206207074304)))) + (((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(29860612486004736)) + (((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(145249023007457280)) + ((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(-30422992425910272))))) + ((((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((6+4)/2)*(X Coord.J : Poly)^4*(244872425963520)) + (((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(32470139150401536)) + ((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(-20769282027159552)))) + (((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((5+5)/2)*(X Coord.J : Poly)^5*(1027096417271808)) + (((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((0+6)/2)*(X Coord.J : Poly)^6*(-8705631717752832)) + ((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((2+6)/2)*(X Coord.J : Poly)^6*(-10727531636981760))))))

theorem clearMoment10Part4_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10Part4=h^11*eval (basePoint v h⁻¹ z) moment10Part4 := by
  norm_num [clearMoment10Part4,moment10Part4,basePoint]
  field_simp [hh]

theorem clearMoment10Part4_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10Part4)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10Part4) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment10Part4,moment10Part4,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment10Part5 : Poly := (((((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((4+6)/2)*(X Coord.J : Poly)^6*(1085108257751040)) + (((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((1+7)/2)*(X Coord.J : Poly)^7*(-1743654893912064)) + ((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((3+7)/2)*(X Coord.J : Poly)^7*(661215532548096)))) + (((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((0+8)/2)*(X Coord.J : Poly)^8*(91947285872640)) + (((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((2+8)/2)*(X Coord.J : Poly)^8*(185194836393984)) + ((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((1+9)/2)*(X Coord.J : Poly)^9*(20061226008576))))) + ((((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-412258829129220096)) + (((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(19009199682551808)) + ((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-403853428260864)))) + (((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(7818213851136)) + (((X Coord.U : Poly)^(11-2)*(X Coord.K : Poly)^((10+0)/2)*(X Coord.J : Poly)^0*(6115295232)) + ((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-13150464920064589824))))))

theorem clearMoment10Part5_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10Part5=h^11*eval (basePoint v h⁻¹ z) moment10Part5 := by
  norm_num [clearMoment10Part5,moment10Part5,basePoint]
  field_simp [hh]

theorem clearMoment10Part5_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10Part5)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10Part5) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment10Part5,moment10Part5,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment10Part6 : Poly := (((((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(7490578609634623488)) + (((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(1074125894882033664)) + ((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-15869968032301056)))) + (((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(-691019570479104)) + (((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((9+1)/2)*(X Coord.J : Poly)^1*(19221849980928)) + ((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(93245636404076544))))) + ((((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-1594312423014629376)) + (((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-240029402699907072)) + ((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(4743924629667840)))) + (((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((8+2)/2)*(X Coord.J : Poly)^2*(67437439377408)) + (((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(79758889488580608)) + ((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(6742504921595904))))))

theorem clearMoment10Part6_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10Part6=h^11*eval (basePoint v h⁻¹ z) moment10Part6 := by
  norm_num [clearMoment10Part6,moment10Part6,basePoint]
  field_simp [hh]

theorem clearMoment10Part6_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10Part6)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10Part6) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment10Part6,moment10Part6,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment10Part7 : Poly := (((((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(35264505271320576)) + (((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((7+3)/2)*(X Coord.J : Poly)^3*(-339866777124864)) + ((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(-162275805732519936)))) + (((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(37155767614193664)) + (((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(20442577957208064)) + ((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((6+4)/2)*(X Coord.J : Poly)^4*(-1788924764307456))))) + ((((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(21372728658886656)) + (((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(21837248204636160)) + ((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((5+5)/2)*(X Coord.J : Poly)^5*(-2644485466226688)))) + (((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((0+6)/2)*(X Coord.J : Poly)^6*(-2526460650455040)) + (((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((2+6)/2)*(X Coord.J : Poly)^6*(3281403593097216)) + ((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((4+6)/2)*(X Coord.J : Poly)^6*(-1958740337885184))))))

theorem clearMoment10Part7_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10Part7=h^11*eval (basePoint v h⁻¹ z) moment10Part7 := by
  norm_num [clearMoment10Part7,moment10Part7,basePoint]
  field_simp [hh]

theorem clearMoment10Part7_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10Part7)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10Part7) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment10Part7,moment10Part7,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment10Part8 : Poly := (((((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((1+7)/2)*(X Coord.J : Poly)^7*(-573416710078464)) + (((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((3+7)/2)*(X Coord.J : Poly)^7*(-648089051332608)) + ((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((0+8)/2)*(X Coord.J : Poly)^8*(5015306502144)))) + (((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((2+8)/2)*(X Coord.J : Poly)^8*(-80802160312320)) + (((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-2447771852650954752)) + ((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(20716788679262208))))) + ((((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(1256456716075008)) + (((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(-27614129209344)) + ((X Coord.U : Poly)^(11-3)*(X Coord.K : Poly)^((10+0)/2)*(X Coord.J : Poly)^0*(-209066655744)))) + (((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-8554127497378209792)) + (((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(4188357258535084032)) + ((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(1578703866224246784))))))

theorem clearMoment10Part8_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10Part8=h^11*eval (basePoint v h⁻¹ z) moment10Part8 := by
  norm_num [clearMoment10Part8,moment10Part8,basePoint]
  field_simp [hh]

theorem clearMoment10Part8_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10Part8)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10Part8) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment10Part8,moment10Part8,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment10Part9 : Poly := (((((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(54261410809724928)) + (((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(-266793322807296)) + ((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((9+1)/2)*(X Coord.J : Poly)^1*(-44450211815424)))) + (((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-518080260483588096)) + (((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-801251635915653120)) + ((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-151499636071022592))))) + ((((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(-14721930448404480)) + (((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((8+2)/2)*(X Coord.J : Poly)^2*(-7410716614656)) + ((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(468204878877622272)))) + (((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(-66591881423290368)) + (((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(-4292773429837824)) + ((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((7+3)/2)*(X Coord.J : Poly)^3*(1325204017053696))))))

theorem clearMoment10Part9_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10Part9=h^11*eval (basePoint v h⁻¹ z) moment10Part9 := by
  norm_num [clearMoment10Part9,moment10Part9,basePoint]
  field_simp [hh]

theorem clearMoment10Part9_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10Part9)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10Part9) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment10Part9,moment10Part9,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment10Part10 : Poly := (((((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(-158036696275746816)) + (((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(49152197917605888)) + ((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(-34257886947311616)))) + (((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((6+4)/2)*(X Coord.J : Poly)^4*(3518770258575360)) + (((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(10641226570924032)) + ((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(-3685971650936832))))) + ((((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((5+5)/2)*(X Coord.J : Poly)^5*(3117090387787776)) + (((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((0+6)/2)*(X Coord.J : Poly)^6*(-229450272473088)) + ((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((2+6)/2)*(X Coord.J : Poly)^6*(1490381915553792)))) + (((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((4+6)/2)*(X Coord.J : Poly)^6*(1283129018155008)) + (((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((1+7)/2)*(X Coord.J : Poly)^7*(-40122452017152)) + ((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((3+7)/2)*(X Coord.J : Poly)^7*(191696159637504))))))

theorem clearMoment10Part10_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10Part10=h^11*eval (basePoint v h⁻¹ z) moment10Part10 := by
  norm_num [clearMoment10Part10,moment10Part10,basePoint]
  field_simp [hh]

theorem clearMoment10Part10_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10Part10)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10Part10) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment10Part10,moment10Part10,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment10Part11 : Poly := (((((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-3961660559120695296)) + (((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-173128209213800448)) + ((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(5898464181780480)))) + (((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(-87926724108288)) + (((X Coord.U : Poly)^(11-4)*(X Coord.K : Poly)^((10+0)/2)*(X Coord.J : Poly)^0*(2911629017088)) + ((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(677116232091085824))))) + ((((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(632117280995205120)) + (((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(1344442243046768640)) + ((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(1706936929468416)))) + (((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(7781627281932288)) + (((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((9+1)/2)*(X Coord.J : Poly)^1*(-69760642424832)) + ((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-1228382486731505664))))))

theorem clearMoment10Part11_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10Part11=h^11*eval (basePoint v h⁻¹ z) moment10Part11 := by
  norm_num [clearMoment10Part11,moment10Part11,basePoint]
  field_simp [hh]

theorem clearMoment10Part11_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10Part11)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10Part11) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment10Part11,moment10Part11,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment10Part12 : Poly := (((((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-54432845479378944)) + (((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-113036754199707648)) + ((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(8431935683788800)))) + (((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((8+2)/2)*(X Coord.J : Poly)^2*(-896245999976448)) + (((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(633002521774915584)) + ((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(-236508689461542912))))) + ((((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(48716063613517824)) + (((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((7+3)/2)*(X Coord.J : Poly)^3*(-3315615516721152)) + ((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(32705127157137408)))) + (((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(-26210932150173696)) + (((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(4425276589277184)) + ((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((6+4)/2)*(X Coord.J : Poly)^4*(-3051879793754112))))))

theorem clearMoment10Part12_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10Part12=h^11*eval (basePoint v h⁻¹ z) moment10Part12 := by
  norm_num [clearMoment10Part12,moment10Part12,basePoint]
  field_simp [hh]

theorem clearMoment10Part12_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10Part12)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10Part12) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment10Part12,moment10Part12,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment10Part13 : Poly := (((((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(1376701634838528)) + (((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(-2049588590542848)) + ((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((5+5)/2)*(X Coord.J : Poly)^5*(-1604433700454400)))) + (((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((2+6)/2)*(X Coord.J : Poly)^6*(140428582060032)) + (((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((4+6)/2)*(X Coord.J : Poly)^6*(-296460339904512)) + ((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-4382336574963588096))))) + ((((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-28115931239221248)) + (((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-30272545686878208)) + ((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(1220349372668928)))) + (((X Coord.U : Poly)^(11-5)*(X Coord.K : Poly)^((10+0)/2)*(X Coord.J : Poly)^0*(-21649604520960)) + (((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(328311602422530048)) + ((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(2303805099558223872))))))

theorem clearMoment10Part13_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10Part13=h^11*eval (basePoint v h⁻¹ z) moment10Part13 := by
  norm_num [clearMoment10Part13,moment10Part13,basePoint]
  field_simp [hh]

theorem clearMoment10Part13_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10Part13)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10Part13) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment10Part13,moment10Part13,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment10Part14 : Poly := (((((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-578663556564123648)) + (((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(211281541027430400)) + ((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(-15769153018920960)))) + (((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((9+1)/2)*(X Coord.J : Poly)^1*(658392165236736)) + (((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(53484012180504576)) + ((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-974558059750490112))))) + ((((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(335431848736456704)) + (((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(-48404603792130048)) + ((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((8+2)/2)*(X Coord.J : Poly)^2*(2351529262153728)))) + (((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(-130820508628549632)) + (((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(48960675900555264)) + ((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(-7059740472115200))))))

theorem clearMoment10Part14_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10Part14=h^11*eval (basePoint v h⁻¹ z) moment10Part14 := by
  norm_num [clearMoment10Part14,moment10Part14,basePoint]
  field_simp [hh]

theorem clearMoment10Part14_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10Part14)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10Part14) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment10Part14,moment10Part14,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment10Part15 : Poly := (((((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((7+3)/2)*(X Coord.J : Poly)^3*(1984745630859264)) + (((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(-3441754087096320)) + ((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(1525489061068800)))) + (((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((6+4)/2)*(X Coord.J : Poly)^4*(1318886295994368)) + (((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(-280857164120064)) + ((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((5+5)/2)*(X Coord.J : Poly)^5*(312063515688960))))) + ((((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-294241410708922368)) + (((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-613251565613383680)) + ((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(53149080840781824)))) + (((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(-4460464678846464)) + (((X Coord.U : Poly)^(11-6)*(X Coord.K : Poly)^((10+0)/2)*(X Coord.J : Poly)^0*(91471564873728)) + ((X Coord.U : Poly)^(11-7)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(383949003059269632))))))

theorem clearMoment10Part15_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10Part15=h^11*eval (basePoint v h⁻¹ z) moment10Part15 := by
  norm_num [clearMoment10Part15,moment10Part15,basePoint]
  field_simp [hh]

theorem clearMoment10Part15_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10Part15)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10Part15) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment10Part15,moment10Part15,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment10Part16 : Poly := (((((X Coord.U : Poly)^(11-7)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-106968024361009152)) + (((X Coord.U : Poly)^(11-7)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(682255339279220736)) + ((X Coord.U : Poly)^(11-7)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-212576273746624512)))) + (((X Coord.U : Poly)^(11-7)*(X Coord.K : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(26346124845121536)) + (((X Coord.U : Poly)^(11-7)*(X Coord.K : Poly)^((9+1)/2)*(X Coord.J : Poly)^1*(-1070124255608832)) + ((X Coord.U : Poly)^(11-7)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(196230762942824448))))) + ((((X Coord.U : Poly)^(11-7)*(X Coord.K : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-58131790753038336)) + (((X Coord.U : Poly)^(11-7)*(X Coord.K : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(8073877241069568)) + ((X Coord.U : Poly)^(11-7)*(X Coord.K : Poly)^((8+2)/2)*(X Coord.J : Poly)^2*(-916075143364608)))) + (((X Coord.U : Poly)^(11-7)*(X Coord.K : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(4589005449461760)) + (((X Coord.U : Poly)^(11-7)*(X Coord.K : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(-493171806044160)) + ((X Coord.U : Poly)^(11-7)*(X Coord.K : Poly)^((7+3)/2)*(X Coord.J : Poly)^3*(-713659540045824))))))

theorem clearMoment10Part16_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10Part16=h^11*eval (basePoint v h⁻¹ z) moment10Part16 := by
  norm_num [clearMoment10Part16,moment10Part16,basePoint]
  field_simp [hh]

theorem clearMoment10Part16_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10Part16)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10Part16) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment10Part16,moment10Part16,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment10Part17 : Poly := (((((X Coord.U : Poly)^(11-7)*(X Coord.K : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(351071455150080)) + (((X Coord.U : Poly)^(11-7)*(X Coord.K : Poly)^((6+4)/2)*(X Coord.J : Poly)^4*(-226246048874496)) + ((X Coord.U : Poly)^(11-7)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-1288727614526312448)))) + (((X Coord.U : Poly)^(11-7)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(374568440387198976)) + (((X Coord.U : Poly)^(11-7)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-88589516401631232)) + ((X Coord.U : Poly)^(11-7)*(X Coord.K : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(6618583363719168))))) + ((((X Coord.U : Poly)^(11-7)*(X Coord.K : Poly)^((10+0)/2)*(X Coord.J : Poly)^0*(-213164635115520)) + (((X Coord.U : Poly)^(11-8)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-130820508628549632)) + ((X Coord.U : Poly)^(11-8)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(36177913453215744)))) + (((X Coord.U : Poly)^(11-8)*(X Coord.K : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(-4810932762181632)) + (((X Coord.U : Poly)^(11-8)*(X Coord.K : Poly)^((9+1)/2)*(X Coord.J : Poly)^1*(298317860831232)) + ((X Coord.U : Poly)^(11-8)*(X Coord.K : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-3441754087096320))))))

theorem clearMoment10Part17_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10Part17=h^11*eval (basePoint v h⁻¹ z) moment10Part17 := by
  norm_num [clearMoment10Part17,moment10Part17,basePoint]
  field_simp [hh]

theorem clearMoment10Part17_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10Part17)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10Part17) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment10Part17,moment10Part17,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment10Part18 : Poly := (((((X Coord.U : Poly)^(11-8)*(X Coord.K : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(-66034868944896)) + (((X Coord.U : Poly)^(11-8)*(X Coord.K : Poly)^((8+2)/2)*(X Coord.J : Poly)^2*(245239200350208)) + ((X Coord.U : Poly)^(11-8)*(X Coord.K : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(-280857164120064)))) + (((X Coord.U : Poly)^(11-8)*(X Coord.K : Poly)^((7+3)/2)*(X Coord.J : Poly)^3*(111451255603200)) + (((X Coord.U : Poly)^(11-8)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(53484012180504576)) + ((X Coord.U : Poly)^(11-8)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-182663105027899392))))) + ((((X Coord.U : Poly)^(11-8)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(51833819612971008)) + (((X Coord.U : Poly)^(11-8)*(X Coord.K : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(-5853234192187392)) + ((X Coord.U : Poly)^(11-8)*(X Coord.K : Poly)^((10+0)/2)*(X Coord.J : Poly)^0*(217846571433984)))) + (((X Coord.U : Poly)^(11-9)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(1376701634838528)) + (((X Coord.U : Poly)^(11-9)*(X Coord.K : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(93619054706688)) + ((X Coord.U : Poly)^(11-9)*(X Coord.K : Poly)^((9+1)/2)*(X Coord.J : Poly)^1*(-48574172233728))))))

theorem clearMoment10Part18_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10Part18=h^11*eval (basePoint v h⁻¹ z) moment10Part18 := by
  norm_num [clearMoment10Part18,moment10Part18,basePoint]
  field_simp [hh]

theorem clearMoment10Part18_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10Part18)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10Part18) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment10Part18,moment10Part18,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment10Part19 : Poly := (((((X Coord.U : Poly)^(11-9)*(X Coord.K : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(140428582060032)) + (((X Coord.U : Poly)^(11-9)*(X Coord.K : Poly)^((8+2)/2)*(X Coord.J : Poly)^2*(-35664401793024)) + ((X Coord.U : Poly)^(11-9)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(32705127157137408)))) + (((X Coord.U : Poly)^(11-9)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-8910632371027968)) + (((X Coord.U : Poly)^(11-9)*(X Coord.K : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(1133703069106176)) + ((X Coord.U : Poly)^(11-9)*(X Coord.K : Poly)^((10+0)/2)*(X Coord.J : Poly)^0*(-51534596210688))))) + ((((X Coord.U : Poly)^(11-10)*(X Coord.K : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(-40122452017152)) + (((X Coord.U : Poly)^(11-10)*(X Coord.K : Poly)^((9+1)/2)*(X Coord.J : Poly)^1*(6687075336192)) + ((X Coord.U : Poly)^(11-10)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-229450272473088)))) + (((X Coord.U : Poly)^(11-10)*(X Coord.K : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(-19225341591552)) + (((X Coord.U : Poly)^(11-10)*(X Coord.K : Poly)^((10+0)/2)*(X Coord.J : Poly)^0*(4225860108288)) + ((X Coord.U : Poly)^(11-11)*(X Coord.K : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(5015306502144))))))

theorem clearMoment10Part19_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10Part19=h^11*eval (basePoint v h⁻¹ z) moment10Part19 := by
  norm_num [clearMoment10Part19,moment10Part19,basePoint]
  field_simp [hh]

theorem clearMoment10Part19_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10Part19)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10Part19) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment10Part19,moment10Part19,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment10Part20 : Poly := (((((X Coord.U : Poly)^(11-11)*(X Coord.K : Poly)^((10+0)/2)*(X Coord.J : Poly)^0*(-557256278016)) + (((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(160938316815925248)) + ((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-481576059666432)))) + (((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-327177085648896)) + (((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(2299011268608)) + ((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((9+1)/2)*(X Coord.J : Poly)^1*(-8153726976))))) + ((((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-149299498311745536)) + (((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(1744681690202112)) + ((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-2676914685739008)))) + (((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(100337980538880)) + (((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((8+2)/2)*(X Coord.J : Poly)^2*(-173776306176)) + ((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(107262236326625280))))))

theorem clearMoment10Part20_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10Part20=h^11*eval (basePoint v h⁻¹ z) moment10Part20 := by
  norm_num [clearMoment10Part20,moment10Part20,basePoint]
  field_simp [hh]

theorem clearMoment10Part20_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10Part20)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10Part20) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment10Part20,moment10Part20,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment10Part21 : Poly := (((((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(-13136441311494144)) + (((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(734567543341056)) + ((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((7+3)/2)*(X Coord.J : Poly)^3*(-9730368995328)))) + (((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(62072707151167488)) + (((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(-34686602777198592)) + ((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(2807707951300608))))) + ((((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((6+4)/2)*(X Coord.J : Poly)^4*(-62408881078272)) + (((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(-21135383922475008)) + ((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(4463867016511488)))) + (((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((5+5)/2)*(X Coord.J : Poly)^5*(-163763975356416)) + (((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((0+6)/2)*(X Coord.J : Poly)^6*(-5108809461792768)) + ((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((2+6)/2)*(X Coord.J : Poly)^6*(2867656286011392))))))

theorem clearMoment10Part21_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10Part21=h^11*eval (basePoint v h⁻¹ z) moment10Part21 := by
  norm_num [clearMoment10Part21,moment10Part21,basePoint]
  field_simp [hh]

theorem clearMoment10Part21_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10Part21)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10Part21) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment10Part21,moment10Part21,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment10Part22 : Poly := (((((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((4+6)/2)*(X Coord.J : Poly)^6*(-205976998379520)) + (((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((1+7)/2)*(X Coord.J : Poly)^7*(914720701022208)) + ((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((3+7)/2)*(X Coord.J : Poly)^7*(-131452284174336)))) + (((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((0+8)/2)*(X Coord.J : Poly)^8*(118649149194240)) + (((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((2+8)/2)*(X Coord.J : Poly)^8*(-48187188707328)) + ((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((1+9)/2)*(X Coord.J : Poly)^9*(-9287604633600))))) + ((((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((0+10)/2)*(X Coord.J : Poly)^10*(-743008370688)) + (((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(10648022001647616)) + ((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(332976678764544)))) + (((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-5278009393152)) + (((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(24461180928)) + ((X Coord.U : Poly)^(11-0)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(0))))))

theorem clearMoment10Part22_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10Part22=h^11*eval (basePoint v h⁻¹ z) moment10Part22 := by
  norm_num [clearMoment10Part22,moment10Part22,basePoint]
  field_simp [hh]

theorem clearMoment10Part22_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10Part22)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10Part22) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment10Part22,moment10Part22,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

end
end HTGeometry.ThetaRatioKineticContraction
