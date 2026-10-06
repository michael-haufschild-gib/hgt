import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticClockMoment2
/-! Exact inverse-clock values and full source derivatives, retaining every moment term. -/

namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def clearMoment8Part0 : Poly := (((((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(48721763450880)) + (((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(465200636755968)) + ((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-208222828609536)))) + (((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(4892833382400)) + (((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-196203036672)) + ((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(2516189184))))) + ((((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(106607673040896)) + (((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(39495108722688)) + ((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-1766119956480)))) + (((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(28747726848)) + (((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(-30631036059648)) + ((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(-4672396099584))))))

theorem clearMoment8Part0_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment8Part0=h^9*eval (basePoint v h⁻¹ z) moment8Part0 := by
  norm_num [clearMoment8Part0,moment8Part0,basePoint]
  field_simp [hh]

theorem clearMoment8Part0_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 9 clearMoment8Part0)=
      h^11*eval (basePoint v h⁻¹ z) (squareLie moment8Part0) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment8Part0,moment8Part0,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment8Part1 : Poly := (((((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(175615672320)) + (((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(-32021435621376)) + ((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(3499943510016)))) + (((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(277618876416)) + (((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(3851131060224)) + ((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(-19707494400))))) + ((((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((0+6)/2)*(X Coord.J : Poly)^6*(1500528623616)) + (((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((2+6)/2)*(X Coord.J : Poly)^6*(-133186830336)) + ((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((1+7)/2)*(X Coord.J : Poly)^7*(-79976595456)))) + (((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((0+8)/2)*(X Coord.J : Poly)^8*(-15479341056)) + (((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-5043506135040)) + ((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(280455561216))))))

theorem clearMoment8Part1_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment8Part1=h^9*eval (basePoint v h⁻¹ z) moment8Part1 := by
  norm_num [clearMoment8Part1,moment8Part1,basePoint]
  field_simp [hh]

theorem clearMoment8Part1_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 9 clearMoment8Part1)=
      h^11*eval (basePoint v h⁻¹ z) (squareLie moment8Part1) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment8Part1,moment8Part1,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment8Part2 : Poly := (((((X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-6975258624)) + (((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(1390654809612288)) + ((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-653518510829568)))) + (((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-15706344517632)) + (((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(943376855040)) + ((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(-18251993088))))) + ((((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(9961318766592)) + (((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(161480364963840)) + ((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(290179418112)))) + (((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(-114128787456)) + (((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(44438285795328)) + ((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(-18974447271936))))))

theorem clearMoment8Part2_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment8Part2=h^9*eval (basePoint v h⁻¹ z) moment8Part2 := by
  norm_num [clearMoment8Part2,moment8Part2,basePoint]
  field_simp [hh]

theorem clearMoment8Part2_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 9 clearMoment8Part2)=
      h^11*eval (basePoint v h⁻¹ z) (squareLie moment8Part2) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment8Part2,moment8Part2,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment8Part3 : Poly := (((((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(-51729186816)) + (((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(-13697040052224)) + ((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(-13151151415296)))) + (((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(909402329088)) + (((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(-5423574122496)) + ((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(976703422464))))) + ((((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((0+6)/2)*(X Coord.J : Poly)^6*(336675667968)) + (((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((2+6)/2)*(X Coord.J : Poly)^6*(545646772224)) + ((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((1+7)/2)*(X Coord.J : Poly)^7*(108355387392)))) + (((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(60218694660096)) + (((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-1816099356672)) + ((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(37381533696))))))

theorem clearMoment8Part3_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment8Part3=h^9*eval (basePoint v h⁻¹ z) moment8Part3 := by
  norm_num [clearMoment8Part3,moment8Part3,basePoint]
  field_simp [hh]

theorem clearMoment8Part3_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 9 clearMoment8Part3)=
      h^11*eval (basePoint v h⁻¹ z) (squareLie moment8Part3) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment8Part3,moment8Part3,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment8Part4 : Poly := (((((X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(95551488)) + (((X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(1594560904169472)) + ((X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-616167263969280)))) + (((X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-114204482150400)) + (((X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(992594829312)) + ((X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(39070605312))))) + ((((X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(43236339148800)) + (((X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(62404116940800)) + ((X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(19329491220480)))) + (((X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(-81859258368)) + (((X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(5636415062016)) + ((X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(14700214222848))))))

theorem clearMoment8Part4_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment8Part4=h^9*eval (basePoint v h⁻¹ z) moment8Part4 := by
  norm_num [clearMoment8Part4,moment8Part4,basePoint]
  field_simp [hh]

theorem clearMoment8Part4_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 9 clearMoment8Part4)=
      h^11*eval (basePoint v h⁻¹ z) (squareLie moment8Part4) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment8Part4,moment8Part4,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment8Part5 : Poly := (((((X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(-1588280721408)) + (((X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(-6765439500288)) + ((X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(9166672281600)))) + (((X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(-1954051817472)) + (((X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(-1369921683456)) + ((X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(-1377661353984))))) + ((((X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((0+6)/2)*(X Coord.J : Poly)^6*(34828517376)) + (((X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((2+6)/2)*(X Coord.J : Poly)^6*(-328935997440)) + ((X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(304304294430720)))) + (((X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-3709196789760)) + (((X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(12712826880)) + ((X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(-2030469120))))))

theorem clearMoment8Part5_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment8Part5=h^9*eval (basePoint v h⁻¹ z) moment8Part5 := by
  norm_num [clearMoment8Part5,moment8Part5,basePoint]
  field_simp [hh]

theorem clearMoment8Part5_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 9 clearMoment8Part5)=
      h^11*eval (basePoint v h⁻¹ z) (squareLie moment8Part5) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment8Part5,moment8Part5,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment8Part6 : Poly := (((((X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(1043671487738112)) + (((X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-374639477501952)) + ((X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-62359251038208)))) + (((X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-9293006278656)) + (((X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(118839177216)) + ((X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-901187887104))))) + ((((X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(65431174643712)) + (((X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-10667684634624)) + ((X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(1263071232000)))) + (((X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(16143017803776)) + (((X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(-10015133663232)) + ((X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(1932552732672))))))

theorem clearMoment8Part6_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment8Part6=h^9*eval (basePoint v h⁻¹ z) moment8Part6 := by
  norm_num [clearMoment8Part6,moment8Part6,basePoint]
  field_simp [hh]

theorem clearMoment8Part6_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 9 clearMoment8Part6)=
      h^11*eval (basePoint v h⁻¹ z) (squareLie moment8Part6) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment8Part6,moment8Part6,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment8Part7 : Poly := (((((X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(-914248581120)) + (((X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(2002639749120)) + ((X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(1852683632640)))) + (((X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(-208971104256)) + (((X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(564995948544)) + ((X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(267216539010048))))) + ((((X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(30406152273408)) + (((X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-1095470189568)) + ((X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(17800632576)))) + (((X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(1258724385792)) + (((X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-8567815274496)) + ((X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-89526703915008))))))

theorem clearMoment8Part7_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment8Part7=h^9*eval (basePoint v h⁻¹ z) moment8Part7 := by
  norm_num [clearMoment8Part7,moment8Part7,basePoint]
  field_simp [hh]

theorem clearMoment8Part7_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 9 clearMoment8Part7)=
      h^11*eval (basePoint v h⁻¹ z) (squareLie moment8Part7) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment8Part7,moment8Part7,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment8Part8 : Poly := (((((X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(7415249338368)) + (((X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(-582911852544)) + ((X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(33892500971520)))) + (((X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-19133916733440)) + (((X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(8028456984576)) + ((X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(-1076405428224))))) + ((((X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(3656994324480)) + (((X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(-1044855521280)) + ((X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(-1458927894528)))) + (((X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(522427760640)) + (((X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(-599824465920)) + ((X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(320229714622464))))))

theorem clearMoment8Part8_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment8Part8=h^9*eval (basePoint v h⁻¹ z) moment8Part8 := by
  norm_num [clearMoment8Part8,moment8Part8,basePoint]
  field_simp [hh]

theorem clearMoment8Part8_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 9 clearMoment8Part8)=
      h^11*eval (basePoint v h⁻¹ z) (squareLie moment8Part8) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment8Part8,moment8Part8,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment8Part9 : Poly := (((((X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-8830480343040)) + (((X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(3199829723136)) + ((X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(-75026580480)))) + (((X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(25140203394048)) + (((X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-67785001943040)) + ((X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(16900538056704))))) + ((((X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-4563503235072)) + (((X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(357852266496)) + ((X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-5485491486720)))) + (((X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-232190115840)) + (((X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(676576198656)) + ((X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(-696570347520))))))

theorem clearMoment8Part9_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment8Part9=h^9*eval (basePoint v h⁻¹ z) moment8Part9 := by
  norm_num [clearMoment8Part9,moment8Part9,basePoint]
  field_simp [hh]

theorem clearMoment8Part9_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 9 clearMoment8Part9)=
      h^11*eval (basePoint v h⁻¹ z) (squareLie moment8Part9) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment8Part9,moment8Part9,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment8Part10 : Poly := (((((X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(402462867456)) + (((X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-1704420569088)) + ((X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(34018391549952)))) + (((X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-2749759819776)) + (((X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(139464115200)) + ((X Coord.U : Poly)^(9-7)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(3656994324480))))) + ((((X Coord.U : Poly)^(9-7)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(417942208512)) + (((X Coord.U : Poly)^(9-7)*(X Coord.K : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(-171562696704)) + ((X Coord.U : Poly)^(9-7)*(X Coord.K : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(522427760640)))) + (((X Coord.U : Poly)^(9-7)*(X Coord.K : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(-166402916352)) + (((X Coord.U : Poly)^(9-7)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(33892500971520)) + ((X Coord.U : Poly)^(9-7)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-7144199626752))))))

theorem clearMoment8Part10_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment8Part10=h^9*eval (basePoint v h⁻¹ z) moment8Part10 := by
  norm_num [clearMoment8Part10,moment8Part10,basePoint]
  field_simp [hh]

theorem clearMoment8Part10_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 9 clearMoment8Part10)=
      h^11*eval (basePoint v h⁻¹ z) (squareLie moment8Part10) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment8Part10,moment8Part10,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment8Part11 : Poly := (((((X Coord.U : Poly)^(9-7)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(1306553131008)) + (((X Coord.U : Poly)^(9-7)*(X Coord.K : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(-64765992960)) + ((X Coord.U : Poly)^(9-8)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-208971104256)))) + (((X Coord.U : Poly)^(9-8)*(X Coord.K : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(38698352640)) + (((X Coord.U : Poly)^(9-8)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-914248581120)) + ((X Coord.U : Poly)^(9-8)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-110290305024))))) + ((((X Coord.U : Poly)^(9-8)*(X Coord.K : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(18381717504)) + (((X Coord.U : Poly)^(9-9)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(34828517376)) + ((X Coord.U : Poly)^(9-9)*(X Coord.K : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(-3869835264)))) + (((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-14932547665920)) + (((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-473768165376)) + ((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(18268913664))))))

theorem clearMoment8Part11_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment8Part11=h^9*eval (basePoint v h⁻¹ z) moment8Part11 := by
  norm_num [clearMoment8Part11,moment8Part11,basePoint]
  field_simp [hh]

theorem clearMoment8Part11_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 9 clearMoment8Part11)=
      h^11*eval (basePoint v h⁻¹ z) (squareLie moment8Part11) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment8Part11,moment8Part11,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment8Part12 : Poly := (((((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(-127401984)) + (((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(36181024800768)) + ((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-3344970940416)))) + (((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(260254384128)) + (((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(-1795571712)) + ((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(-15123423707136))))) + ((((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(1215558254592)) + (((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(-24953536512)) + ((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(-9391203348480)))) + (((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(2944819224576)) + (((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(-106218418176)) + ((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(1838171750400))))))

theorem clearMoment8Part12_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment8Part12=h^9*eval (basePoint v h⁻¹ z) moment8Part12 := by
  norm_num [clearMoment8Part12,moment8Part12,basePoint]
  field_simp [hh]

theorem clearMoment8Part12_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 9 clearMoment8Part12)=
      h^11*eval (basePoint v h⁻¹ z) (squareLie moment8Part12) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment8Part12,moment8Part12,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

def clearMoment8Part13 : Poly := (((((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(-173091520512)) + ((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((0+6)/2)*(X Coord.J : Poly)^6*(464057745408))) + (((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((2+6)/2)*(X Coord.J : Poly)^6*(-117205843968)) + ((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((1+7)/2)*(X Coord.J : Poly)^7*(-38698352640)))) + ((((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((0+8)/2)*(X Coord.J : Poly)^8*(-5159780352)) + ((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-293964152832))) + (((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-37786632192)) + (((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(382205952)) + ((X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(0))))))

theorem clearMoment8Part13_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment8Part13=h^9*eval (basePoint v h⁻¹ z) moment8Part13 := by
  norm_num [clearMoment8Part13,moment8Part13,basePoint]
  field_simp [hh]

theorem clearMoment8Part13_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 9 clearMoment8Part13)=
      h^11*eval (basePoint v h⁻¹ z) (squareLie moment8Part13) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hJU : Coord.J ≠ Coord.U := Ne.symm hUJ
  have hJK : Coord.J ≠ Coord.K := Ne.symm hKJ
  unfold clockFlow clockLie squareLie
  rw [flow_expand,flow_expand]
  norm_num [clockField,clearMoment8Part13,moment8Part13,squareField,
    basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKJ,hKU,hJU,hJK]
  field_simp [hh]
  ring

end
end HTGeometry.ThetaRatioKineticContraction
