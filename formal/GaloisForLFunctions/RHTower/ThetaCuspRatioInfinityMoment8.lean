import GaloisForLFunctions.RHTower.ThetaCuspRatioInfinityFlow
/-! # Exact source-flow compactification and the third-slope expanding mode. -/

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def scaled8Part0Low : Poly := ((((if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(48721763450880) else 0) + ((if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(465200636755968) else 0) + (if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(-208222828609536) else 0))) + ((if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(4892833382400) else 0) + ((if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(-196203036672) else 0) + (if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((7+1)/2)*(C (1/3:ℂ)*deficit)^1*(2516189184) else 0)))) + (((if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(106607673040896) else 0) + ((if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(39495108722688) else 0) + (if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((4+2)/2)*(C (1/3:ℂ)*deficit)^2*(-1766119956480) else 0))) + ((if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((6+2)/2)*(C (1/3:ℂ)*deficit)^2*(28747726848) else 0) + ((if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((1+3)/2)*(C (1/3:ℂ)*deficit)^3*(-30631036059648) else 0) + (if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((3+3)/2)*(C (1/3:ℂ)*deficit)^3*(-4672396099584) else 0)))))
def scaled8Part0Mid : Poly := (0:Poly)
def scaled8Part0Upper : Poly := (0:Poly)

theorem scaled8Part0_clear (h r t : ℂ) (hh : h≠0) :
    h^(7+2)*eval (sourcePoint h r t) moment8Part0 =
      h^2*eval (basePoint h r t) scaled8Part0Low+
      h*eval (basePoint h r t) scaled8Part0Mid+eval (basePoint h r t) scaled8Part0Upper := by
  norm_num [moment8Part0,scaled8Part0Low,scaled8Part0Mid,scaled8Part0Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled8Part1Low : Poly := ((((if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((5+3)/2)*(C (1/3:ℂ)*deficit)^3*(175615672320) else 0) + ((if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((0+4)/2)*(C (1/3:ℂ)*deficit)^4*(-32021435621376) else 0) + (if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((2+4)/2)*(C (1/3:ℂ)*deficit)^4*(3499943510016) else 0))) + ((if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((4+4)/2)*(C (1/3:ℂ)*deficit)^4*(277618876416) else 0) + ((if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((1+5)/2)*(C (1/3:ℂ)*deficit)^5*(3851131060224) else 0) + (if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((3+5)/2)*(C (1/3:ℂ)*deficit)^5*(-19707494400) else 0)))) + (((if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((0+6)/2)*(C (1/3:ℂ)*deficit)^6*(1500528623616) else 0) + ((if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((2+6)/2)*(C (1/3:ℂ)*deficit)^6*(-133186830336) else 0) + (if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((1+7)/2)*(C (1/3:ℂ)*deficit)^7*(-79976595456) else 0))) + ((if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((0+8)/2)*(C (1/3:ℂ)*deficit)^8*(-15479341056) else 0) + ((if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(-5043506135040) else 0) + (if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(280455561216) else 0)))))
def scaled8Part1Mid : Poly := (0:Poly)
def scaled8Part1Upper : Poly := (0:Poly)

theorem scaled8Part1_clear (h r t : ℂ) (hh : h≠0) :
    h^(7+2)*eval (sourcePoint h r t) moment8Part1 =
      h^2*eval (basePoint h r t) scaled8Part1Low+
      h*eval (basePoint h r t) scaled8Part1Mid+eval (basePoint h r t) scaled8Part1Upper := by
  norm_num [moment8Part1,scaled8Part1Low,scaled8Part1Mid,scaled8Part1Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled8Part2Low : Poly := ((((if 1≤7 then (X Coord.U:Poly)^(7-1)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(-6975258624) else 0) + ((if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(1390654809612288) else 0) + (if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(-653518510829568) else 0))) + ((if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(-15706344517632) else 0) + ((if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(943376855040) else 0) + (if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((7+1)/2)*(C (1/3:ℂ)*deficit)^1*(-18251993088) else 0)))) + (((if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(9961318766592) else 0) + ((if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(161480364963840) else 0) + (if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((4+2)/2)*(C (1/3:ℂ)*deficit)^2*(290179418112) else 0))) + ((if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((6+2)/2)*(C (1/3:ℂ)*deficit)^2*(-114128787456) else 0) + ((if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((1+3)/2)*(C (1/3:ℂ)*deficit)^3*(44438285795328) else 0) + (if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((3+3)/2)*(C (1/3:ℂ)*deficit)^3*(-18974447271936) else 0)))))
def scaled8Part2Mid : Poly := (0:Poly)
def scaled8Part2Upper : Poly := (0:Poly)

theorem scaled8Part2_clear (h r t : ℂ) (hh : h≠0) :
    h^(7+2)*eval (sourcePoint h r t) moment8Part2 =
      h^2*eval (basePoint h r t) scaled8Part2Low+
      h*eval (basePoint h r t) scaled8Part2Mid+eval (basePoint h r t) scaled8Part2Upper := by
  norm_num [moment8Part2,scaled8Part2Low,scaled8Part2Mid,scaled8Part2Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled8Part3Low : Poly := ((((if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((5+3)/2)*(C (1/3:ℂ)*deficit)^3*(-51729186816) else 0) + ((if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((0+4)/2)*(C (1/3:ℂ)*deficit)^4*(-13697040052224) else 0) + (if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((2+4)/2)*(C (1/3:ℂ)*deficit)^4*(-13151151415296) else 0))) + ((if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((4+4)/2)*(C (1/3:ℂ)*deficit)^4*(909402329088) else 0) + ((if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((1+5)/2)*(C (1/3:ℂ)*deficit)^5*(-5423574122496) else 0) + (if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((3+5)/2)*(C (1/3:ℂ)*deficit)^5*(976703422464) else 0)))) + (((if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((0+6)/2)*(C (1/3:ℂ)*deficit)^6*(336675667968) else 0) + ((if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((2+6)/2)*(C (1/3:ℂ)*deficit)^6*(545646772224) else 0) + (if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((1+7)/2)*(C (1/3:ℂ)*deficit)^7*(108355387392) else 0))) + ((if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(60218694660096) else 0) + ((if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(-1816099356672) else 0) + (if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(37381533696) else 0)))))
def scaled8Part3Mid : Poly := (0:Poly)
def scaled8Part3Upper : Poly := (0:Poly)

theorem scaled8Part3_clear (h r t : ℂ) (hh : h≠0) :
    h^(7+2)*eval (sourcePoint h r t) moment8Part3 =
      h^2*eval (basePoint h r t) scaled8Part3Low+
      h*eval (basePoint h r t) scaled8Part3Mid+eval (basePoint h r t) scaled8Part3Upper := by
  norm_num [moment8Part3,scaled8Part3Low,scaled8Part3Mid,scaled8Part3Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled8Part4Low : Poly := ((((if 2≤7 then (X Coord.U:Poly)^(7-2)*driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(95551488) else 0) + ((if 3≤7 then (X Coord.U:Poly)^(7-3)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(1594560904169472) else 0) + (if 3≤7 then (X Coord.U:Poly)^(7-3)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(-616167263969280) else 0))) + ((if 3≤7 then (X Coord.U:Poly)^(7-3)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(-114204482150400) else 0) + ((if 3≤7 then (X Coord.U:Poly)^(7-3)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(992594829312) else 0) + (if 3≤7 then (X Coord.U:Poly)^(7-3)*driftSquare^((7+1)/2)*(C (1/3:ℂ)*deficit)^1*(39070605312) else 0)))) + (((if 3≤7 then (X Coord.U:Poly)^(7-3)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(43236339148800) else 0) + ((if 3≤7 then (X Coord.U:Poly)^(7-3)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(62404116940800) else 0) + (if 3≤7 then (X Coord.U:Poly)^(7-3)*driftSquare^((4+2)/2)*(C (1/3:ℂ)*deficit)^2*(19329491220480) else 0))) + ((if 3≤7 then (X Coord.U:Poly)^(7-3)*driftSquare^((6+2)/2)*(C (1/3:ℂ)*deficit)^2*(-81859258368) else 0) + ((if 3≤7 then (X Coord.U:Poly)^(7-3)*driftSquare^((1+3)/2)*(C (1/3:ℂ)*deficit)^3*(5636415062016) else 0) + (if 3≤7 then (X Coord.U:Poly)^(7-3)*driftSquare^((3+3)/2)*(C (1/3:ℂ)*deficit)^3*(14700214222848) else 0)))))
def scaled8Part4Mid : Poly := (0:Poly)
def scaled8Part4Upper : Poly := (0:Poly)

theorem scaled8Part4_clear (h r t : ℂ) (hh : h≠0) :
    h^(7+2)*eval (sourcePoint h r t) moment8Part4 =
      h^2*eval (basePoint h r t) scaled8Part4Low+
      h*eval (basePoint h r t) scaled8Part4Mid+eval (basePoint h r t) scaled8Part4Upper := by
  norm_num [moment8Part4,scaled8Part4Low,scaled8Part4Mid,scaled8Part4Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled8Part5Low : Poly := ((((if 3≤7 then (X Coord.U:Poly)^(7-3)*driftSquare^((5+3)/2)*(C (1/3:ℂ)*deficit)^3*(-1588280721408) else 0) + ((if 3≤7 then (X Coord.U:Poly)^(7-3)*driftSquare^((0+4)/2)*(C (1/3:ℂ)*deficit)^4*(-6765439500288) else 0) + (if 3≤7 then (X Coord.U:Poly)^(7-3)*driftSquare^((2+4)/2)*(C (1/3:ℂ)*deficit)^4*(9166672281600) else 0))) + ((if 3≤7 then (X Coord.U:Poly)^(7-3)*driftSquare^((4+4)/2)*(C (1/3:ℂ)*deficit)^4*(-1954051817472) else 0) + ((if 3≤7 then (X Coord.U:Poly)^(7-3)*driftSquare^((1+5)/2)*(C (1/3:ℂ)*deficit)^5*(-1369921683456) else 0) + (if 3≤7 then (X Coord.U:Poly)^(7-3)*driftSquare^((3+5)/2)*(C (1/3:ℂ)*deficit)^5*(-1377661353984) else 0)))) + (((if 3≤7 then (X Coord.U:Poly)^(7-3)*driftSquare^((0+6)/2)*(C (1/3:ℂ)*deficit)^6*(34828517376) else 0) + ((if 3≤7 then (X Coord.U:Poly)^(7-3)*driftSquare^((2+6)/2)*(C (1/3:ℂ)*deficit)^6*(-328935997440) else 0) + (if 3≤7 then (X Coord.U:Poly)^(7-3)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(304304294430720) else 0))) + ((if 3≤7 then (X Coord.U:Poly)^(7-3)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(-3709196789760) else 0) + ((if 3≤7 then (X Coord.U:Poly)^(7-3)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(12712826880) else 0) + (if 3≤7 then (X Coord.U:Poly)^(7-3)*driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(-2030469120) else 0)))))
def scaled8Part5Mid : Poly := (0:Poly)
def scaled8Part5Upper : Poly := (0:Poly)

theorem scaled8Part5_clear (h r t : ℂ) (hh : h≠0) :
    h^(7+2)*eval (sourcePoint h r t) moment8Part5 =
      h^2*eval (basePoint h r t) scaled8Part5Low+
      h*eval (basePoint h r t) scaled8Part5Mid+eval (basePoint h r t) scaled8Part5Upper := by
  norm_num [moment8Part5,scaled8Part5Low,scaled8Part5Mid,scaled8Part5Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled8Part6Low : Poly := ((((if 4≤7 then (X Coord.U:Poly)^(7-4)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(1043671487738112) else 0) + ((if 4≤7 then (X Coord.U:Poly)^(7-4)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(-374639477501952) else 0) + (if 4≤7 then (X Coord.U:Poly)^(7-4)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(-62359251038208) else 0))) + ((if 4≤7 then (X Coord.U:Poly)^(7-4)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(-9293006278656) else 0) + ((if 4≤7 then (X Coord.U:Poly)^(7-4)*driftSquare^((7+1)/2)*(C (1/3:ℂ)*deficit)^1*(118839177216) else 0) + (if 4≤7 then (X Coord.U:Poly)^(7-4)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(-901187887104) else 0)))) + (((if 4≤7 then (X Coord.U:Poly)^(7-4)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(65431174643712) else 0) + ((if 4≤7 then (X Coord.U:Poly)^(7-4)*driftSquare^((4+2)/2)*(C (1/3:ℂ)*deficit)^2*(-10667684634624) else 0) + (if 4≤7 then (X Coord.U:Poly)^(7-4)*driftSquare^((6+2)/2)*(C (1/3:ℂ)*deficit)^2*(1263071232000) else 0))) + ((if 4≤7 then (X Coord.U:Poly)^(7-4)*driftSquare^((1+3)/2)*(C (1/3:ℂ)*deficit)^3*(16143017803776) else 0) + ((if 4≤7 then (X Coord.U:Poly)^(7-4)*driftSquare^((3+3)/2)*(C (1/3:ℂ)*deficit)^3*(-10015133663232) else 0) + (if 4≤7 then (X Coord.U:Poly)^(7-4)*driftSquare^((5+3)/2)*(C (1/3:ℂ)*deficit)^3*(1932552732672) else 0)))))
def scaled8Part6Mid : Poly := (0:Poly)
def scaled8Part6Upper : Poly := (0:Poly)

theorem scaled8Part6_clear (h r t : ℂ) (hh : h≠0) :
    h^(7+2)*eval (sourcePoint h r t) moment8Part6 =
      h^2*eval (basePoint h r t) scaled8Part6Low+
      h*eval (basePoint h r t) scaled8Part6Mid+eval (basePoint h r t) scaled8Part6Upper := by
  norm_num [moment8Part6,scaled8Part6Low,scaled8Part6Mid,scaled8Part6Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled8Part7Low : Poly := ((((if 4≤7 then (X Coord.U:Poly)^(7-4)*driftSquare^((0+4)/2)*(C (1/3:ℂ)*deficit)^4*(-914248581120) else 0) + ((if 4≤7 then (X Coord.U:Poly)^(7-4)*driftSquare^((2+4)/2)*(C (1/3:ℂ)*deficit)^4*(2002639749120) else 0) + (if 4≤7 then (X Coord.U:Poly)^(7-4)*driftSquare^((4+4)/2)*(C (1/3:ℂ)*deficit)^4*(1852683632640) else 0))) + ((if 4≤7 then (X Coord.U:Poly)^(7-4)*driftSquare^((1+5)/2)*(C (1/3:ℂ)*deficit)^5*(-208971104256) else 0) + ((if 4≤7 then (X Coord.U:Poly)^(7-4)*driftSquare^((3+5)/2)*(C (1/3:ℂ)*deficit)^5*(564995948544) else 0) + (if 4≤7 then (X Coord.U:Poly)^(7-4)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(267216539010048) else 0)))) + (((if 4≤7 then (X Coord.U:Poly)^(7-4)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(30406152273408) else 0) + ((if 4≤7 then (X Coord.U:Poly)^(7-4)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(-1095470189568) else 0) + (if 4≤7 then (X Coord.U:Poly)^(7-4)*driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(17800632576) else 0))) + ((if 5≤7 then (X Coord.U:Poly)^(7-5)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(1258724385792) else 0) + ((if 5≤7 then (X Coord.U:Poly)^(7-5)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(-8567815274496) else 0) + (if 5≤7 then (X Coord.U:Poly)^(7-5)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(-89526703915008) else 0)))))
def scaled8Part7Mid : Poly := (0:Poly)
def scaled8Part7Upper : Poly := (0:Poly)

theorem scaled8Part7_clear (h r t : ℂ) (hh : h≠0) :
    h^(7+2)*eval (sourcePoint h r t) moment8Part7 =
      h^2*eval (basePoint h r t) scaled8Part7Low+
      h*eval (basePoint h r t) scaled8Part7Mid+eval (basePoint h r t) scaled8Part7Upper := by
  norm_num [moment8Part7,scaled8Part7Low,scaled8Part7Mid,scaled8Part7Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled8Part8Low : Poly := ((((if 5≤7 then (X Coord.U:Poly)^(7-5)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(7415249338368) else 0) + ((if 5≤7 then (X Coord.U:Poly)^(7-5)*driftSquare^((7+1)/2)*(C (1/3:ℂ)*deficit)^1*(-582911852544) else 0) + (if 5≤7 then (X Coord.U:Poly)^(7-5)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(33892500971520) else 0))) + ((if 5≤7 then (X Coord.U:Poly)^(7-5)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(-19133916733440) else 0) + ((if 5≤7 then (X Coord.U:Poly)^(7-5)*driftSquare^((4+2)/2)*(C (1/3:ℂ)*deficit)^2*(8028456984576) else 0) + (if 5≤7 then (X Coord.U:Poly)^(7-5)*driftSquare^((6+2)/2)*(C (1/3:ℂ)*deficit)^2*(-1076405428224) else 0)))) + (((if 5≤7 then (X Coord.U:Poly)^(7-5)*driftSquare^((1+3)/2)*(C (1/3:ℂ)*deficit)^3*(3656994324480) else 0) + ((if 5≤7 then (X Coord.U:Poly)^(7-5)*driftSquare^((3+3)/2)*(C (1/3:ℂ)*deficit)^3*(-1044855521280) else 0) + (if 5≤7 then (X Coord.U:Poly)^(7-5)*driftSquare^((5+3)/2)*(C (1/3:ℂ)*deficit)^3*(-1458927894528) else 0))) + ((if 5≤7 then (X Coord.U:Poly)^(7-5)*driftSquare^((2+4)/2)*(C (1/3:ℂ)*deficit)^4*(522427760640) else 0) + ((if 5≤7 then (X Coord.U:Poly)^(7-5)*driftSquare^((4+4)/2)*(C (1/3:ℂ)*deficit)^4*(-599824465920) else 0) + (if 5≤7 then (X Coord.U:Poly)^(7-5)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(320229714622464) else 0)))))
def scaled8Part8Mid : Poly := (0:Poly)
def scaled8Part8Upper : Poly := (0:Poly)

theorem scaled8Part8_clear (h r t : ℂ) (hh : h≠0) :
    h^(7+2)*eval (sourcePoint h r t) moment8Part8 =
      h^2*eval (basePoint h r t) scaled8Part8Low+
      h*eval (basePoint h r t) scaled8Part8Mid+eval (basePoint h r t) scaled8Part8Upper := by
  norm_num [moment8Part8,scaled8Part8Low,scaled8Part8Mid,scaled8Part8Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled8Part9Low : Poly := ((((if 5≤7 then (X Coord.U:Poly)^(7-5)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(-8830480343040) else 0) + ((if 5≤7 then (X Coord.U:Poly)^(7-5)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(3199829723136) else 0) + (if 5≤7 then (X Coord.U:Poly)^(7-5)*driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(-75026580480) else 0))) + ((if 6≤7 then (X Coord.U:Poly)^(7-6)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(25140203394048) else 0) + ((if 6≤7 then (X Coord.U:Poly)^(7-6)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(-67785001943040) else 0) + (if 6≤7 then (X Coord.U:Poly)^(7-6)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(16900538056704) else 0)))) + (((if 6≤7 then (X Coord.U:Poly)^(7-6)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(-4563503235072) else 0) + ((if 6≤7 then (X Coord.U:Poly)^(7-6)*driftSquare^((7+1)/2)*(C (1/3:ℂ)*deficit)^1*(357852266496) else 0) + (if 6≤7 then (X Coord.U:Poly)^(7-6)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(-5485491486720) else 0))) + ((if 6≤7 then (X Coord.U:Poly)^(7-6)*driftSquare^((4+2)/2)*(C (1/3:ℂ)*deficit)^2*(-232190115840) else 0) + ((if 6≤7 then (X Coord.U:Poly)^(7-6)*driftSquare^((6+2)/2)*(C (1/3:ℂ)*deficit)^2*(676576198656) else 0) + (if 6≤7 then (X Coord.U:Poly)^(7-6)*driftSquare^((3+3)/2)*(C (1/3:ℂ)*deficit)^3*(-696570347520) else 0)))))
def scaled8Part9Mid : Poly := (0:Poly)
def scaled8Part9Upper : Poly := (0:Poly)

theorem scaled8Part9_clear (h r t : ℂ) (hh : h≠0) :
    h^(7+2)*eval (sourcePoint h r t) moment8Part9 =
      h^2*eval (basePoint h r t) scaled8Part9Low+
      h*eval (basePoint h r t) scaled8Part9Mid+eval (basePoint h r t) scaled8Part9Upper := by
  norm_num [moment8Part9,scaled8Part9Low,scaled8Part9Mid,scaled8Part9Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled8Part10Low : Poly := ((((if 6≤7 then (X Coord.U:Poly)^(7-6)*driftSquare^((5+3)/2)*(C (1/3:ℂ)*deficit)^3*(402462867456) else 0) + ((if 6≤7 then (X Coord.U:Poly)^(7-6)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(-1704420569088) else 0) + (if 6≤7 then (X Coord.U:Poly)^(7-6)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(34018391549952) else 0))) + ((if 6≤7 then (X Coord.U:Poly)^(7-6)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(-2749759819776) else 0) + ((if 6≤7 then (X Coord.U:Poly)^(7-6)*driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(139464115200) else 0) + (if 7≤7 then (X Coord.U:Poly)^(7-7)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(3656994324480) else 0)))) + (((if 7≤7 then (X Coord.U:Poly)^(7-7)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(417942208512) else 0) + ((if 7≤7 then (X Coord.U:Poly)^(7-7)*driftSquare^((7+1)/2)*(C (1/3:ℂ)*deficit)^1*(-171562696704) else 0) + (if 7≤7 then (X Coord.U:Poly)^(7-7)*driftSquare^((4+2)/2)*(C (1/3:ℂ)*deficit)^2*(522427760640) else 0))) + ((if 7≤7 then (X Coord.U:Poly)^(7-7)*driftSquare^((6+2)/2)*(C (1/3:ℂ)*deficit)^2*(-166402916352) else 0) + ((if 7≤7 then (X Coord.U:Poly)^(7-7)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(33892500971520) else 0) + (if 7≤7 then (X Coord.U:Poly)^(7-7)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(-7144199626752) else 0)))))
def scaled8Part10Mid : Poly := (0:Poly)
def scaled8Part10Upper : Poly := (0:Poly)

theorem scaled8Part10_clear (h r t : ℂ) (hh : h≠0) :
    h^(7+2)*eval (sourcePoint h r t) moment8Part10 =
      h^2*eval (basePoint h r t) scaled8Part10Low+
      h*eval (basePoint h r t) scaled8Part10Mid+eval (basePoint h r t) scaled8Part10Upper := by
  norm_num [moment8Part10,scaled8Part10Low,scaled8Part10Mid,scaled8Part10Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled8Part11Low : Poly := ((((if 7≤7 then (X Coord.U:Poly)^(7-7)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(1306553131008) else 0) + ((if 7≤7 then (X Coord.U:Poly)^(7-7)*driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(-64765992960) else 0) + (if 8≤7 then (X Coord.U:Poly)^(7-8)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(-208971104256) else 0))) + ((if 8≤7 then (X Coord.U:Poly)^(7-8)*driftSquare^((7+1)/2)*(C (1/3:ℂ)*deficit)^1*(38698352640) else 0) + ((if 8≤7 then (X Coord.U:Poly)^(7-8)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(-914248581120) else 0) + (if 8≤7 then (X Coord.U:Poly)^(7-8)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(-110290305024) else 0)))) + (((if 8≤7 then (X Coord.U:Poly)^(7-8)*driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(18381717504) else 0) + ((if 9≤7 then (X Coord.U:Poly)^(7-9)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(34828517376) else 0) + (if 9≤7 then (X Coord.U:Poly)^(7-9)*driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(-3869835264) else 0))) + ((if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(-14932547665920) else 0) + ((if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(-473768165376) else 0) + (if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(18268913664) else 0)))))
def scaled8Part11Mid : Poly := (((driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(-208971104256)) + (driftSquare^((7+1)/2)*(C (1/3:ℂ)*deficit)^1*(38698352640))) + ((driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(-914248581120)) + ((driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(-110290305024)) + (driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(18381717504)))))
def scaled8Part11Upper : Poly := ((driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(34828517376)) + (driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(-3869835264)))

theorem scaled8Part11_clear (h r t : ℂ) (hh : h≠0) :
    h^(7+2)*eval (sourcePoint h r t) moment8Part11 =
      h^2*eval (basePoint h r t) scaled8Part11Low+
      h*eval (basePoint h r t) scaled8Part11Mid+eval (basePoint h r t) scaled8Part11Upper := by
  norm_num [moment8Part11,scaled8Part11Low,scaled8Part11Mid,scaled8Part11Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled8Part12Low : Poly := ((((if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((7+1)/2)*(C (1/3:ℂ)*deficit)^1*(-127401984) else 0) + ((if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(36181024800768) else 0) + (if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(-3344970940416) else 0))) + ((if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((4+2)/2)*(C (1/3:ℂ)*deficit)^2*(260254384128) else 0) + ((if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((6+2)/2)*(C (1/3:ℂ)*deficit)^2*(-1795571712) else 0) + (if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((1+3)/2)*(C (1/3:ℂ)*deficit)^3*(-15123423707136) else 0)))) + (((if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((3+3)/2)*(C (1/3:ℂ)*deficit)^3*(1215558254592) else 0) + ((if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((5+3)/2)*(C (1/3:ℂ)*deficit)^3*(-24953536512) else 0) + (if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((0+4)/2)*(C (1/3:ℂ)*deficit)^4*(-9391203348480) else 0))) + ((if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((2+4)/2)*(C (1/3:ℂ)*deficit)^4*(2944819224576) else 0) + ((if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((4+4)/2)*(C (1/3:ℂ)*deficit)^4*(-106218418176) else 0) + (if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((1+5)/2)*(C (1/3:ℂ)*deficit)^5*(1838171750400) else 0)))))
def scaled8Part12Mid : Poly := (0:Poly)
def scaled8Part12Upper : Poly := (0:Poly)

theorem scaled8Part12_clear (h r t : ℂ) (hh : h≠0) :
    h^(7+2)*eval (sourcePoint h r t) moment8Part12 =
      h^2*eval (basePoint h r t) scaled8Part12Low+
      h*eval (basePoint h r t) scaled8Part12Mid+eval (basePoint h r t) scaled8Part12Upper := by
  norm_num [moment8Part12,scaled8Part12Low,scaled8Part12Mid,scaled8Part12Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled8Part13Low : Poly := ((((if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((3+5)/2)*(C (1/3:ℂ)*deficit)^5*(-173091520512) else 0) + (if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((0+6)/2)*(C (1/3:ℂ)*deficit)^6*(464057745408) else 0)) + ((if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((2+6)/2)*(C (1/3:ℂ)*deficit)^6*(-117205843968) else 0) + (if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((1+7)/2)*(C (1/3:ℂ)*deficit)^7*(-38698352640) else 0))) + (((if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((0+8)/2)*(C (1/3:ℂ)*deficit)^8*(-5159780352) else 0) + (if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(-293964152832) else 0)) + ((if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(-37786632192) else 0) + ((if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(382205952) else 0) + (if 0≤7 then (X Coord.U:Poly)^(7-0)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(0) else 0)))))
def scaled8Part13Mid : Poly := (0:Poly)
def scaled8Part13Upper : Poly := (0:Poly)

theorem scaled8Part13_clear (h r t : ℂ) (hh : h≠0) :
    h^(7+2)*eval (sourcePoint h r t) moment8Part13 =
      h^2*eval (basePoint h r t) scaled8Part13Low+
      h*eval (basePoint h r t) scaled8Part13Mid+eval (basePoint h r t) scaled8Part13Upper := by
  norm_num [moment8Part13,scaled8Part13Low,scaled8Part13Mid,scaled8Part13Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def low8 : Poly := (((scaled8Part0Low + (scaled8Part1Low + scaled8Part2Low)) + ((scaled8Part3Low + scaled8Part4Low) + (scaled8Part5Low + scaled8Part6Low))) + ((scaled8Part7Low + (scaled8Part8Low + scaled8Part9Low)) + ((scaled8Part10Low + scaled8Part11Low) + (scaled8Part12Low + scaled8Part13Low))))
def mid8 : Poly := (((scaled8Part0Mid + (scaled8Part1Mid + scaled8Part2Mid)) + ((scaled8Part3Mid + scaled8Part4Mid) + (scaled8Part5Mid + scaled8Part6Mid))) + ((scaled8Part7Mid + (scaled8Part8Mid + scaled8Part9Mid)) + ((scaled8Part10Mid + scaled8Part11Mid) + (scaled8Part12Mid + scaled8Part13Mid))))
def upper8 : Poly := (((scaled8Part0Upper + (scaled8Part1Upper + scaled8Part2Upper)) + ((scaled8Part3Upper + scaled8Part4Upper) + (scaled8Part5Upper + scaled8Part6Upper))) + ((scaled8Part7Upper + (scaled8Part8Upper + scaled8Part9Upper)) + ((scaled8Part10Upper + scaled8Part11Upper) + (scaled8Part12Upper + scaled8Part13Upper))))

def midScaled8 : Poly := ((((-208971104256:Poly)*(-X Coord.K*X Coord.U*C ((1/3:ℂ)^1)*(∑ i ∈ Finset.range ((5+1)/2), driftSquare^i*(9:Poly)^(((5+1)/2)-1-i)) - X Coord.J*C (1/3:ℂ)*1*driftSquare^((5+1)/2))) + ((38698352640:Poly)*(-X Coord.K*X Coord.U*C ((1/3:ℂ)^1)*(∑ i ∈ Finset.range ((7+1)/2), driftSquare^i*(9:Poly)^(((7+1)/2)-1-i)) - X Coord.J*C (1/3:ℂ)*1*driftSquare^((7+1)/2)))) + (((-914248581120:Poly)*(-X Coord.K*X Coord.U*C ((1/3:ℂ)^0)*(∑ i ∈ Finset.range ((4+0)/2), driftSquare^i*(9:Poly)^(((4+0)/2)-1-i)) - X Coord.J*C (1/3:ℂ)*0*driftSquare^((4+0)/2))) + (((-110290305024:Poly)*(-X Coord.K*X Coord.U*C ((1/3:ℂ)^0)*(∑ i ∈ Finset.range ((6+0)/2), driftSquare^i*(9:Poly)^(((6+0)/2)-1-i)) - X Coord.J*C (1/3:ℂ)*0*driftSquare^((6+0)/2))) + ((18381717504:Poly)*(-X Coord.K*X Coord.U*C ((1/3:ℂ)^0)*(∑ i ∈ Finset.range ((8+0)/2), driftSquare^i*(9:Poly)^(((8+0)/2)-1-i)) - X Coord.J*C (1/3:ℂ)*0*driftSquare^((8+0)/2))))))
def upperScaled8 : Poly := (3869835264:Poly)*X Coord.K*driftSquare^3
def scaledMoment8 : Poly := low8+midScaled8+upperScaled8

theorem mid8_scaled : mid8=X Coord.U*midScaled8 := by
  apply MvPolynomial.funext
  intro v
  norm_num [mid8,midScaled8,scaled8Part0Mid,scaled8Part1Mid,scaled8Part2Mid,scaled8Part3Mid,scaled8Part4Mid,scaled8Part5Mid,scaled8Part6Mid,scaled8Part7Mid,scaled8Part8Mid,scaled8Part9Mid,scaled8Part10Mid,scaled8Part11Mid,scaled8Part12Mid,scaled8Part13Mid,driftSquare,deficit,Finset.sum_range_succ] <;> ring

theorem upper8_scaled : upper8=(X Coord.U)^2*upperScaled8 := by
  apply MvPolynomial.funext
  intro v
  norm_num [upper8,upperScaled8,scaled8Part0Upper,scaled8Part1Upper,scaled8Part2Upper,scaled8Part3Upper,scaled8Part4Upper,scaled8Part5Upper,scaled8Part6Upper,scaled8Part7Upper,scaled8Part8Upper,scaled8Part9Upper,scaled8Part10Upper,scaled8Part11Upper,scaled8Part12Upper,scaled8Part13Upper,driftSquare,deficit] <;> ring

theorem scaledMoment8_eq (h r t : ℂ) (hh : h≠0) :
    h^7*eval (sourcePoint h r t) moment8=eval (basePoint h r t) scaledMoment8 := by
  have he : h^(7+2)*eval (sourcePoint h r t) moment8=
      h^2*eval (basePoint h r t) low8+h*eval (basePoint h r t) mid8+
        eval (basePoint h r t) upper8 := by
    simp only [moment8,low8,mid8,upper8,map_add,mul_add]
    rw [scaled8Part0_clear h r t hh,scaled8Part1_clear h r t hh,scaled8Part2_clear h r t hh,scaled8Part3_clear h r t hh,scaled8Part4_clear h r t hh,scaled8Part5_clear h r t hh,scaled8Part6_clear h r t hh,scaled8Part7_clear h r t hh,scaled8Part8_clear h r t hh,scaled8Part9_clear h r t hh,scaled8Part10_clear h r t hh,scaled8Part11_clear h r t hh,scaled8Part12_clear h r t hh,scaled8Part13_clear h r t hh]
    ring
  rw [mid8_scaled,upper8_scaled] at he
  apply mul_left_cancel₀ (pow_ne_zero 2 hh)
  calc h^2*(h^7*eval (sourcePoint h r t) moment8)=
        h^(7+2)*eval (sourcePoint h r t) moment8 := by ring
       _ = h^2*eval (basePoint h r t) scaledMoment8 := by
         rw [he]
         simp only [scaledMoment8,map_add,map_mul,map_pow,eval_X,basePoint]
         ring

theorem scaledMoment8_zero (r t : ℂ) :
    eval (basePoint 0 r t) scaledMoment8=(6:ℂ)^10*46656*(r-12*t) := by
  norm_num [scaledMoment8,low8,midScaled8,upperScaled8,scaled8Part0Low,scaled8Part1Low,scaled8Part2Low,scaled8Part3Low,scaled8Part4Low,scaled8Part5Low,scaled8Part6Low,scaled8Part7Low,scaled8Part8Low,scaled8Part9Low,scaled8Part10Low,scaled8Part11Low,scaled8Part12Low,scaled8Part13Low,basePoint,driftSquare,deficit,Finset.sum_range_succ] <;> ring

end
end HTGeometry.ThetaRatioInfinity
