import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticClockMoments
/-! Complete kinetic coefficient decomposition; every literal source term is retained. -/
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def clearMoment8Part0KineticCoeff (d : ℕ) : Poly := (((((if 0=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((0+0)/2)*(48721763450880) else 0)) + (((if 0=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((0+0)/2)*(465200636755968) else 0)) + ((if 1=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((1+1)/2)*(-208222828609536) else 0)))) + (((if 1=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((3+1)/2)*(4892833382400) else 0)) + (((if 1=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((5+1)/2)*(-196203036672) else 0)) + ((if 1=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((7+1)/2)*(2516189184) else 0))))) + ((((if 2=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((0+2)/2)*(106607673040896) else 0)) + (((if 2=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((2+2)/2)*(39495108722688) else 0)) + ((if 2=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((4+2)/2)*(-1766119956480) else 0)))) + (((if 2=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((6+2)/2)*(28747726848) else 0)) + (((if 3=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((1+3)/2)*(-30631036059648) else 0)) + ((if 3=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((3+3)/2)*(-4672396099584) else 0))))))

theorem clearMoment8Part0_kinetic : clearMoment8Part0=
    ((((X Coord.J)^0*clearMoment8Part0KineticCoeff 0 + (X Coord.J)^1*clearMoment8Part0KineticCoeff 1) + ((X Coord.J)^2*clearMoment8Part0KineticCoeff 2 + (X Coord.J)^3*clearMoment8Part0KineticCoeff 3)) + (((X Coord.J)^4*clearMoment8Part0KineticCoeff 4 + (X Coord.J)^5*clearMoment8Part0KineticCoeff 5) + ((X Coord.J)^6*clearMoment8Part0KineticCoeff 6 + ((X Coord.J)^7*clearMoment8Part0KineticCoeff 7 + (X Coord.J)^8*clearMoment8Part0KineticCoeff 8)))) := by
  norm_num [clearMoment8Part0,clearMoment8Part0KineticCoeff]
  ring

def clearMoment8Part1KineticCoeff (d : ℕ) : Poly := (((((if 3=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((5+3)/2)*(175615672320) else 0)) + (((if 4=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((0+4)/2)*(-32021435621376) else 0)) + ((if 4=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((2+4)/2)*(3499943510016) else 0)))) + (((if 4=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((4+4)/2)*(277618876416) else 0)) + (((if 5=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((1+5)/2)*(3851131060224) else 0)) + ((if 5=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((3+5)/2)*(-19707494400) else 0))))) + ((((if 6=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((0+6)/2)*(1500528623616) else 0)) + (((if 6=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((2+6)/2)*(-133186830336) else 0)) + ((if 7=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((1+7)/2)*(-79976595456) else 0)))) + (((if 8=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((0+8)/2)*(-15479341056) else 0)) + (((if 0=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((2+0)/2)*(-5043506135040) else 0)) + ((if 0=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((4+0)/2)*(280455561216) else 0))))))

theorem clearMoment8Part1_kinetic : clearMoment8Part1=
    ((((X Coord.J)^0*clearMoment8Part1KineticCoeff 0 + (X Coord.J)^1*clearMoment8Part1KineticCoeff 1) + ((X Coord.J)^2*clearMoment8Part1KineticCoeff 2 + (X Coord.J)^3*clearMoment8Part1KineticCoeff 3)) + (((X Coord.J)^4*clearMoment8Part1KineticCoeff 4 + (X Coord.J)^5*clearMoment8Part1KineticCoeff 5) + ((X Coord.J)^6*clearMoment8Part1KineticCoeff 6 + ((X Coord.J)^7*clearMoment8Part1KineticCoeff 7 + (X Coord.J)^8*clearMoment8Part1KineticCoeff 8)))) := by
  norm_num [clearMoment8Part1,clearMoment8Part1KineticCoeff]
  ring

def clearMoment8Part2KineticCoeff (d : ℕ) : Poly := (((((if 0=d then (X Coord.U : Poly)^(9-1)*(X Coord.K : Poly)^((6+0)/2)*(-6975258624) else 0)) + (((if 0=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((0+0)/2)*(1390654809612288) else 0)) + ((if 1=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((1+1)/2)*(-653518510829568) else 0)))) + (((if 1=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((3+1)/2)*(-15706344517632) else 0)) + (((if 1=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((5+1)/2)*(943376855040) else 0)) + ((if 1=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((7+1)/2)*(-18251993088) else 0))))) + ((((if 2=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((0+2)/2)*(9961318766592) else 0)) + (((if 2=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((2+2)/2)*(161480364963840) else 0)) + ((if 2=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((4+2)/2)*(290179418112) else 0)))) + (((if 2=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((6+2)/2)*(-114128787456) else 0)) + (((if 3=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((1+3)/2)*(44438285795328) else 0)) + ((if 3=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((3+3)/2)*(-18974447271936) else 0))))))

theorem clearMoment8Part2_kinetic : clearMoment8Part2=
    ((((X Coord.J)^0*clearMoment8Part2KineticCoeff 0 + (X Coord.J)^1*clearMoment8Part2KineticCoeff 1) + ((X Coord.J)^2*clearMoment8Part2KineticCoeff 2 + (X Coord.J)^3*clearMoment8Part2KineticCoeff 3)) + (((X Coord.J)^4*clearMoment8Part2KineticCoeff 4 + (X Coord.J)^5*clearMoment8Part2KineticCoeff 5) + ((X Coord.J)^6*clearMoment8Part2KineticCoeff 6 + ((X Coord.J)^7*clearMoment8Part2KineticCoeff 7 + (X Coord.J)^8*clearMoment8Part2KineticCoeff 8)))) := by
  norm_num [clearMoment8Part2,clearMoment8Part2KineticCoeff]
  ring

def clearMoment8Part3KineticCoeff (d : ℕ) : Poly := (((((if 3=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((5+3)/2)*(-51729186816) else 0)) + (((if 4=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((0+4)/2)*(-13697040052224) else 0)) + ((if 4=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((2+4)/2)*(-13151151415296) else 0)))) + (((if 4=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((4+4)/2)*(909402329088) else 0)) + (((if 5=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((1+5)/2)*(-5423574122496) else 0)) + ((if 5=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((3+5)/2)*(976703422464) else 0))))) + ((((if 6=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((0+6)/2)*(336675667968) else 0)) + (((if 6=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((2+6)/2)*(545646772224) else 0)) + ((if 7=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((1+7)/2)*(108355387392) else 0)))) + (((if 0=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((2+0)/2)*(60218694660096) else 0)) + (((if 0=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((4+0)/2)*(-1816099356672) else 0)) + ((if 0=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((6+0)/2)*(37381533696) else 0))))))

theorem clearMoment8Part3_kinetic : clearMoment8Part3=
    ((((X Coord.J)^0*clearMoment8Part3KineticCoeff 0 + (X Coord.J)^1*clearMoment8Part3KineticCoeff 1) + ((X Coord.J)^2*clearMoment8Part3KineticCoeff 2 + (X Coord.J)^3*clearMoment8Part3KineticCoeff 3)) + (((X Coord.J)^4*clearMoment8Part3KineticCoeff 4 + (X Coord.J)^5*clearMoment8Part3KineticCoeff 5) + ((X Coord.J)^6*clearMoment8Part3KineticCoeff 6 + ((X Coord.J)^7*clearMoment8Part3KineticCoeff 7 + (X Coord.J)^8*clearMoment8Part3KineticCoeff 8)))) := by
  norm_num [clearMoment8Part3,clearMoment8Part3KineticCoeff]
  ring

def clearMoment8Part4KineticCoeff (d : ℕ) : Poly := (((((if 0=d then (X Coord.U : Poly)^(9-2)*(X Coord.K : Poly)^((8+0)/2)*(95551488) else 0)) + (((if 0=d then (X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((0+0)/2)*(1594560904169472) else 0)) + ((if 1=d then (X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((1+1)/2)*(-616167263969280) else 0)))) + (((if 1=d then (X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((3+1)/2)*(-114204482150400) else 0)) + (((if 1=d then (X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((5+1)/2)*(992594829312) else 0)) + ((if 1=d then (X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((7+1)/2)*(39070605312) else 0))))) + ((((if 2=d then (X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((0+2)/2)*(43236339148800) else 0)) + (((if 2=d then (X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((2+2)/2)*(62404116940800) else 0)) + ((if 2=d then (X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((4+2)/2)*(19329491220480) else 0)))) + (((if 2=d then (X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((6+2)/2)*(-81859258368) else 0)) + (((if 3=d then (X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((1+3)/2)*(5636415062016) else 0)) + ((if 3=d then (X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((3+3)/2)*(14700214222848) else 0))))))

theorem clearMoment8Part4_kinetic : clearMoment8Part4=
    ((((X Coord.J)^0*clearMoment8Part4KineticCoeff 0 + (X Coord.J)^1*clearMoment8Part4KineticCoeff 1) + ((X Coord.J)^2*clearMoment8Part4KineticCoeff 2 + (X Coord.J)^3*clearMoment8Part4KineticCoeff 3)) + (((X Coord.J)^4*clearMoment8Part4KineticCoeff 4 + (X Coord.J)^5*clearMoment8Part4KineticCoeff 5) + ((X Coord.J)^6*clearMoment8Part4KineticCoeff 6 + ((X Coord.J)^7*clearMoment8Part4KineticCoeff 7 + (X Coord.J)^8*clearMoment8Part4KineticCoeff 8)))) := by
  norm_num [clearMoment8Part4,clearMoment8Part4KineticCoeff]
  ring

def clearMoment8Part5KineticCoeff (d : ℕ) : Poly := (((((if 3=d then (X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((5+3)/2)*(-1588280721408) else 0)) + (((if 4=d then (X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((0+4)/2)*(-6765439500288) else 0)) + ((if 4=d then (X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((2+4)/2)*(9166672281600) else 0)))) + (((if 4=d then (X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((4+4)/2)*(-1954051817472) else 0)) + (((if 5=d then (X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((1+5)/2)*(-1369921683456) else 0)) + ((if 5=d then (X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((3+5)/2)*(-1377661353984) else 0))))) + ((((if 6=d then (X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((0+6)/2)*(34828517376) else 0)) + (((if 6=d then (X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((2+6)/2)*(-328935997440) else 0)) + ((if 0=d then (X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((2+0)/2)*(304304294430720) else 0)))) + (((if 0=d then (X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((4+0)/2)*(-3709196789760) else 0)) + (((if 0=d then (X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((6+0)/2)*(12712826880) else 0)) + ((if 0=d then (X Coord.U : Poly)^(9-3)*(X Coord.K : Poly)^((8+0)/2)*(-2030469120) else 0))))))

theorem clearMoment8Part5_kinetic : clearMoment8Part5=
    ((((X Coord.J)^0*clearMoment8Part5KineticCoeff 0 + (X Coord.J)^1*clearMoment8Part5KineticCoeff 1) + ((X Coord.J)^2*clearMoment8Part5KineticCoeff 2 + (X Coord.J)^3*clearMoment8Part5KineticCoeff 3)) + (((X Coord.J)^4*clearMoment8Part5KineticCoeff 4 + (X Coord.J)^5*clearMoment8Part5KineticCoeff 5) + ((X Coord.J)^6*clearMoment8Part5KineticCoeff 6 + ((X Coord.J)^7*clearMoment8Part5KineticCoeff 7 + (X Coord.J)^8*clearMoment8Part5KineticCoeff 8)))) := by
  norm_num [clearMoment8Part5,clearMoment8Part5KineticCoeff]
  ring

def clearMoment8Part6KineticCoeff (d : ℕ) : Poly := (((((if 0=d then (X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((0+0)/2)*(1043671487738112) else 0)) + (((if 1=d then (X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((1+1)/2)*(-374639477501952) else 0)) + ((if 1=d then (X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((3+1)/2)*(-62359251038208) else 0)))) + (((if 1=d then (X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((5+1)/2)*(-9293006278656) else 0)) + (((if 1=d then (X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((7+1)/2)*(118839177216) else 0)) + ((if 2=d then (X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((0+2)/2)*(-901187887104) else 0))))) + ((((if 2=d then (X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((2+2)/2)*(65431174643712) else 0)) + (((if 2=d then (X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((4+2)/2)*(-10667684634624) else 0)) + ((if 2=d then (X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((6+2)/2)*(1263071232000) else 0)))) + (((if 3=d then (X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((1+3)/2)*(16143017803776) else 0)) + (((if 3=d then (X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((3+3)/2)*(-10015133663232) else 0)) + ((if 3=d then (X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((5+3)/2)*(1932552732672) else 0))))))

theorem clearMoment8Part6_kinetic : clearMoment8Part6=
    ((((X Coord.J)^0*clearMoment8Part6KineticCoeff 0 + (X Coord.J)^1*clearMoment8Part6KineticCoeff 1) + ((X Coord.J)^2*clearMoment8Part6KineticCoeff 2 + (X Coord.J)^3*clearMoment8Part6KineticCoeff 3)) + (((X Coord.J)^4*clearMoment8Part6KineticCoeff 4 + (X Coord.J)^5*clearMoment8Part6KineticCoeff 5) + ((X Coord.J)^6*clearMoment8Part6KineticCoeff 6 + ((X Coord.J)^7*clearMoment8Part6KineticCoeff 7 + (X Coord.J)^8*clearMoment8Part6KineticCoeff 8)))) := by
  norm_num [clearMoment8Part6,clearMoment8Part6KineticCoeff]
  ring

def clearMoment8Part7KineticCoeff (d : ℕ) : Poly := (((((if 4=d then (X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((0+4)/2)*(-914248581120) else 0)) + (((if 4=d then (X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((2+4)/2)*(2002639749120) else 0)) + ((if 4=d then (X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((4+4)/2)*(1852683632640) else 0)))) + (((if 5=d then (X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((1+5)/2)*(-208971104256) else 0)) + (((if 5=d then (X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((3+5)/2)*(564995948544) else 0)) + ((if 0=d then (X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((2+0)/2)*(267216539010048) else 0))))) + ((((if 0=d then (X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((4+0)/2)*(30406152273408) else 0)) + (((if 0=d then (X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((6+0)/2)*(-1095470189568) else 0)) + ((if 0=d then (X Coord.U : Poly)^(9-4)*(X Coord.K : Poly)^((8+0)/2)*(17800632576) else 0)))) + (((if 0=d then (X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((0+0)/2)*(1258724385792) else 0)) + (((if 1=d then (X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((1+1)/2)*(-8567815274496) else 0)) + ((if 1=d then (X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((3+1)/2)*(-89526703915008) else 0))))))

theorem clearMoment8Part7_kinetic : clearMoment8Part7=
    ((((X Coord.J)^0*clearMoment8Part7KineticCoeff 0 + (X Coord.J)^1*clearMoment8Part7KineticCoeff 1) + ((X Coord.J)^2*clearMoment8Part7KineticCoeff 2 + (X Coord.J)^3*clearMoment8Part7KineticCoeff 3)) + (((X Coord.J)^4*clearMoment8Part7KineticCoeff 4 + (X Coord.J)^5*clearMoment8Part7KineticCoeff 5) + ((X Coord.J)^6*clearMoment8Part7KineticCoeff 6 + ((X Coord.J)^7*clearMoment8Part7KineticCoeff 7 + (X Coord.J)^8*clearMoment8Part7KineticCoeff 8)))) := by
  norm_num [clearMoment8Part7,clearMoment8Part7KineticCoeff]
  ring

def clearMoment8Part8KineticCoeff (d : ℕ) : Poly := (((((if 1=d then (X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((5+1)/2)*(7415249338368) else 0)) + (((if 1=d then (X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((7+1)/2)*(-582911852544) else 0)) + ((if 2=d then (X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((0+2)/2)*(33892500971520) else 0)))) + (((if 2=d then (X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((2+2)/2)*(-19133916733440) else 0)) + (((if 2=d then (X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((4+2)/2)*(8028456984576) else 0)) + ((if 2=d then (X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((6+2)/2)*(-1076405428224) else 0))))) + ((((if 3=d then (X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((1+3)/2)*(3656994324480) else 0)) + (((if 3=d then (X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((3+3)/2)*(-1044855521280) else 0)) + ((if 3=d then (X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((5+3)/2)*(-1458927894528) else 0)))) + (((if 4=d then (X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((2+4)/2)*(522427760640) else 0)) + (((if 4=d then (X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((4+4)/2)*(-599824465920) else 0)) + ((if 0=d then (X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((2+0)/2)*(320229714622464) else 0))))))

theorem clearMoment8Part8_kinetic : clearMoment8Part8=
    ((((X Coord.J)^0*clearMoment8Part8KineticCoeff 0 + (X Coord.J)^1*clearMoment8Part8KineticCoeff 1) + ((X Coord.J)^2*clearMoment8Part8KineticCoeff 2 + (X Coord.J)^3*clearMoment8Part8KineticCoeff 3)) + (((X Coord.J)^4*clearMoment8Part8KineticCoeff 4 + (X Coord.J)^5*clearMoment8Part8KineticCoeff 5) + ((X Coord.J)^6*clearMoment8Part8KineticCoeff 6 + ((X Coord.J)^7*clearMoment8Part8KineticCoeff 7 + (X Coord.J)^8*clearMoment8Part8KineticCoeff 8)))) := by
  norm_num [clearMoment8Part8,clearMoment8Part8KineticCoeff]
  ring

def clearMoment8Part9KineticCoeff (d : ℕ) : Poly := (((((if 0=d then (X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((4+0)/2)*(-8830480343040) else 0)) + (((if 0=d then (X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((6+0)/2)*(3199829723136) else 0)) + ((if 0=d then (X Coord.U : Poly)^(9-5)*(X Coord.K : Poly)^((8+0)/2)*(-75026580480) else 0)))) + (((if 0=d then (X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((0+0)/2)*(25140203394048) else 0)) + (((if 1=d then (X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((1+1)/2)*(-67785001943040) else 0)) + ((if 1=d then (X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((3+1)/2)*(16900538056704) else 0))))) + ((((if 1=d then (X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((5+1)/2)*(-4563503235072) else 0)) + (((if 1=d then (X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((7+1)/2)*(357852266496) else 0)) + ((if 2=d then (X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((2+2)/2)*(-5485491486720) else 0)))) + (((if 2=d then (X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((4+2)/2)*(-232190115840) else 0)) + (((if 2=d then (X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((6+2)/2)*(676576198656) else 0)) + ((if 3=d then (X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((3+3)/2)*(-696570347520) else 0))))))

theorem clearMoment8Part9_kinetic : clearMoment8Part9=
    ((((X Coord.J)^0*clearMoment8Part9KineticCoeff 0 + (X Coord.J)^1*clearMoment8Part9KineticCoeff 1) + ((X Coord.J)^2*clearMoment8Part9KineticCoeff 2 + (X Coord.J)^3*clearMoment8Part9KineticCoeff 3)) + (((X Coord.J)^4*clearMoment8Part9KineticCoeff 4 + (X Coord.J)^5*clearMoment8Part9KineticCoeff 5) + ((X Coord.J)^6*clearMoment8Part9KineticCoeff 6 + ((X Coord.J)^7*clearMoment8Part9KineticCoeff 7 + (X Coord.J)^8*clearMoment8Part9KineticCoeff 8)))) := by
  norm_num [clearMoment8Part9,clearMoment8Part9KineticCoeff]
  ring

def clearMoment8Part10KineticCoeff (d : ℕ) : Poly := (((((if 3=d then (X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((5+3)/2)*(402462867456) else 0)) + (((if 0=d then (X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((2+0)/2)*(-1704420569088) else 0)) + ((if 0=d then (X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((4+0)/2)*(34018391549952) else 0)))) + (((if 0=d then (X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((6+0)/2)*(-2749759819776) else 0)) + (((if 0=d then (X Coord.U : Poly)^(9-6)*(X Coord.K : Poly)^((8+0)/2)*(139464115200) else 0)) + ((if 1=d then (X Coord.U : Poly)^(9-7)*(X Coord.K : Poly)^((3+1)/2)*(3656994324480) else 0))))) + ((((if 1=d then (X Coord.U : Poly)^(9-7)*(X Coord.K : Poly)^((5+1)/2)*(417942208512) else 0)) + (((if 1=d then (X Coord.U : Poly)^(9-7)*(X Coord.K : Poly)^((7+1)/2)*(-171562696704) else 0)) + ((if 2=d then (X Coord.U : Poly)^(9-7)*(X Coord.K : Poly)^((4+2)/2)*(522427760640) else 0)))) + (((if 2=d then (X Coord.U : Poly)^(9-7)*(X Coord.K : Poly)^((6+2)/2)*(-166402916352) else 0)) + (((if 0=d then (X Coord.U : Poly)^(9-7)*(X Coord.K : Poly)^((2+0)/2)*(33892500971520) else 0)) + ((if 0=d then (X Coord.U : Poly)^(9-7)*(X Coord.K : Poly)^((4+0)/2)*(-7144199626752) else 0))))))

theorem clearMoment8Part10_kinetic : clearMoment8Part10=
    ((((X Coord.J)^0*clearMoment8Part10KineticCoeff 0 + (X Coord.J)^1*clearMoment8Part10KineticCoeff 1) + ((X Coord.J)^2*clearMoment8Part10KineticCoeff 2 + (X Coord.J)^3*clearMoment8Part10KineticCoeff 3)) + (((X Coord.J)^4*clearMoment8Part10KineticCoeff 4 + (X Coord.J)^5*clearMoment8Part10KineticCoeff 5) + ((X Coord.J)^6*clearMoment8Part10KineticCoeff 6 + ((X Coord.J)^7*clearMoment8Part10KineticCoeff 7 + (X Coord.J)^8*clearMoment8Part10KineticCoeff 8)))) := by
  norm_num [clearMoment8Part10,clearMoment8Part10KineticCoeff]
  ring

def clearMoment8Part11KineticCoeff (d : ℕ) : Poly := (((((if 0=d then (X Coord.U : Poly)^(9-7)*(X Coord.K : Poly)^((6+0)/2)*(1306553131008) else 0)) + (((if 0=d then (X Coord.U : Poly)^(9-7)*(X Coord.K : Poly)^((8+0)/2)*(-64765992960) else 0)) + ((if 1=d then (X Coord.U : Poly)^(9-8)*(X Coord.K : Poly)^((5+1)/2)*(-208971104256) else 0)))) + (((if 1=d then (X Coord.U : Poly)^(9-8)*(X Coord.K : Poly)^((7+1)/2)*(38698352640) else 0)) + (((if 0=d then (X Coord.U : Poly)^(9-8)*(X Coord.K : Poly)^((4+0)/2)*(-914248581120) else 0)) + ((if 0=d then (X Coord.U : Poly)^(9-8)*(X Coord.K : Poly)^((6+0)/2)*(-110290305024) else 0))))) + ((((if 0=d then (X Coord.U : Poly)^(9-8)*(X Coord.K : Poly)^((8+0)/2)*(18381717504) else 0)) + (((if 0=d then (X Coord.U : Poly)^(9-9)*(X Coord.K : Poly)^((6+0)/2)*(34828517376) else 0)) + ((if 0=d then (X Coord.U : Poly)^(9-9)*(X Coord.K : Poly)^((8+0)/2)*(-3869835264) else 0)))) + (((if 1=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((1+1)/2)*(-14932547665920) else 0)) + (((if 1=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((3+1)/2)*(-473768165376) else 0)) + ((if 1=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((5+1)/2)*(18268913664) else 0))))))

theorem clearMoment8Part11_kinetic : clearMoment8Part11=
    ((((X Coord.J)^0*clearMoment8Part11KineticCoeff 0 + (X Coord.J)^1*clearMoment8Part11KineticCoeff 1) + ((X Coord.J)^2*clearMoment8Part11KineticCoeff 2 + (X Coord.J)^3*clearMoment8Part11KineticCoeff 3)) + (((X Coord.J)^4*clearMoment8Part11KineticCoeff 4 + (X Coord.J)^5*clearMoment8Part11KineticCoeff 5) + ((X Coord.J)^6*clearMoment8Part11KineticCoeff 6 + ((X Coord.J)^7*clearMoment8Part11KineticCoeff 7 + (X Coord.J)^8*clearMoment8Part11KineticCoeff 8)))) := by
  norm_num [clearMoment8Part11,clearMoment8Part11KineticCoeff]
  ring

def clearMoment8Part12KineticCoeff (d : ℕ) : Poly := (((((if 1=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((7+1)/2)*(-127401984) else 0)) + (((if 2=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((0+2)/2)*(36181024800768) else 0)) + ((if 2=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((2+2)/2)*(-3344970940416) else 0)))) + (((if 2=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((4+2)/2)*(260254384128) else 0)) + (((if 2=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((6+2)/2)*(-1795571712) else 0)) + ((if 3=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((1+3)/2)*(-15123423707136) else 0))))) + ((((if 3=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((3+3)/2)*(1215558254592) else 0)) + (((if 3=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((5+3)/2)*(-24953536512) else 0)) + ((if 4=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((0+4)/2)*(-9391203348480) else 0)))) + (((if 4=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((2+4)/2)*(2944819224576) else 0)) + (((if 4=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((4+4)/2)*(-106218418176) else 0)) + ((if 5=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((1+5)/2)*(1838171750400) else 0))))))

theorem clearMoment8Part12_kinetic : clearMoment8Part12=
    ((((X Coord.J)^0*clearMoment8Part12KineticCoeff 0 + (X Coord.J)^1*clearMoment8Part12KineticCoeff 1) + ((X Coord.J)^2*clearMoment8Part12KineticCoeff 2 + (X Coord.J)^3*clearMoment8Part12KineticCoeff 3)) + (((X Coord.J)^4*clearMoment8Part12KineticCoeff 4 + (X Coord.J)^5*clearMoment8Part12KineticCoeff 5) + ((X Coord.J)^6*clearMoment8Part12KineticCoeff 6 + ((X Coord.J)^7*clearMoment8Part12KineticCoeff 7 + (X Coord.J)^8*clearMoment8Part12KineticCoeff 8)))) := by
  norm_num [clearMoment8Part12,clearMoment8Part12KineticCoeff]
  ring

def clearMoment8Part13KineticCoeff (d : ℕ) : Poly := (((((if 5=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((3+5)/2)*(-173091520512) else 0)) + ((if 6=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((0+6)/2)*(464057745408) else 0))) + (((if 6=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((2+6)/2)*(-117205843968) else 0)) + ((if 7=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((1+7)/2)*(-38698352640) else 0)))) + ((((if 8=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((0+8)/2)*(-5159780352) else 0)) + ((if 0=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((2+0)/2)*(-293964152832) else 0))) + (((if 0=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((4+0)/2)*(-37786632192) else 0)) + (((if 0=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((6+0)/2)*(382205952) else 0)) + ((if 0=d then (X Coord.U : Poly)^(9-0)*(X Coord.K : Poly)^((0+0)/2)*(0) else 0))))))

theorem clearMoment8Part13_kinetic : clearMoment8Part13=
    ((((X Coord.J)^0*clearMoment8Part13KineticCoeff 0 + (X Coord.J)^1*clearMoment8Part13KineticCoeff 1) + ((X Coord.J)^2*clearMoment8Part13KineticCoeff 2 + (X Coord.J)^3*clearMoment8Part13KineticCoeff 3)) + (((X Coord.J)^4*clearMoment8Part13KineticCoeff 4 + (X Coord.J)^5*clearMoment8Part13KineticCoeff 5) + ((X Coord.J)^6*clearMoment8Part13KineticCoeff 6 + ((X Coord.J)^7*clearMoment8Part13KineticCoeff 7 + (X Coord.J)^8*clearMoment8Part13KineticCoeff 8)))) := by
  norm_num [clearMoment8Part13,clearMoment8Part13KineticCoeff]
  ring

def clearMoment8KineticCoeff0 : Poly := ((((clearMoment8Part0KineticCoeff 0) + ((clearMoment8Part1KineticCoeff 0) + (clearMoment8Part2KineticCoeff 0))) + (((clearMoment8Part3KineticCoeff 0) + (clearMoment8Part4KineticCoeff 0)) + ((clearMoment8Part5KineticCoeff 0) + (clearMoment8Part6KineticCoeff 0)))) + (((clearMoment8Part7KineticCoeff 0) + ((clearMoment8Part8KineticCoeff 0) + (clearMoment8Part9KineticCoeff 0))) + (((clearMoment8Part10KineticCoeff 0) + (clearMoment8Part11KineticCoeff 0)) + ((clearMoment8Part12KineticCoeff 0) + (clearMoment8Part13KineticCoeff 0)))))

def clearMoment8KineticCoeff1 : Poly := ((((clearMoment8Part0KineticCoeff 1) + ((clearMoment8Part1KineticCoeff 1) + (clearMoment8Part2KineticCoeff 1))) + (((clearMoment8Part3KineticCoeff 1) + (clearMoment8Part4KineticCoeff 1)) + ((clearMoment8Part5KineticCoeff 1) + (clearMoment8Part6KineticCoeff 1)))) + (((clearMoment8Part7KineticCoeff 1) + ((clearMoment8Part8KineticCoeff 1) + (clearMoment8Part9KineticCoeff 1))) + (((clearMoment8Part10KineticCoeff 1) + (clearMoment8Part11KineticCoeff 1)) + ((clearMoment8Part12KineticCoeff 1) + (clearMoment8Part13KineticCoeff 1)))))

def clearMoment8KineticCoeff2 : Poly := ((((clearMoment8Part0KineticCoeff 2) + ((clearMoment8Part1KineticCoeff 2) + (clearMoment8Part2KineticCoeff 2))) + (((clearMoment8Part3KineticCoeff 2) + (clearMoment8Part4KineticCoeff 2)) + ((clearMoment8Part5KineticCoeff 2) + (clearMoment8Part6KineticCoeff 2)))) + (((clearMoment8Part7KineticCoeff 2) + ((clearMoment8Part8KineticCoeff 2) + (clearMoment8Part9KineticCoeff 2))) + (((clearMoment8Part10KineticCoeff 2) + (clearMoment8Part11KineticCoeff 2)) + ((clearMoment8Part12KineticCoeff 2) + (clearMoment8Part13KineticCoeff 2)))))

def clearMoment8KineticCoeff3 : Poly := ((((clearMoment8Part0KineticCoeff 3) + ((clearMoment8Part1KineticCoeff 3) + (clearMoment8Part2KineticCoeff 3))) + (((clearMoment8Part3KineticCoeff 3) + (clearMoment8Part4KineticCoeff 3)) + ((clearMoment8Part5KineticCoeff 3) + (clearMoment8Part6KineticCoeff 3)))) + (((clearMoment8Part7KineticCoeff 3) + ((clearMoment8Part8KineticCoeff 3) + (clearMoment8Part9KineticCoeff 3))) + (((clearMoment8Part10KineticCoeff 3) + (clearMoment8Part11KineticCoeff 3)) + ((clearMoment8Part12KineticCoeff 3) + (clearMoment8Part13KineticCoeff 3)))))

def clearMoment8KineticCoeff4 : Poly := ((((clearMoment8Part0KineticCoeff 4) + ((clearMoment8Part1KineticCoeff 4) + (clearMoment8Part2KineticCoeff 4))) + (((clearMoment8Part3KineticCoeff 4) + (clearMoment8Part4KineticCoeff 4)) + ((clearMoment8Part5KineticCoeff 4) + (clearMoment8Part6KineticCoeff 4)))) + (((clearMoment8Part7KineticCoeff 4) + ((clearMoment8Part8KineticCoeff 4) + (clearMoment8Part9KineticCoeff 4))) + (((clearMoment8Part10KineticCoeff 4) + (clearMoment8Part11KineticCoeff 4)) + ((clearMoment8Part12KineticCoeff 4) + (clearMoment8Part13KineticCoeff 4)))))

def clearMoment8KineticCoeff5 : Poly := ((((clearMoment8Part0KineticCoeff 5) + ((clearMoment8Part1KineticCoeff 5) + (clearMoment8Part2KineticCoeff 5))) + (((clearMoment8Part3KineticCoeff 5) + (clearMoment8Part4KineticCoeff 5)) + ((clearMoment8Part5KineticCoeff 5) + (clearMoment8Part6KineticCoeff 5)))) + (((clearMoment8Part7KineticCoeff 5) + ((clearMoment8Part8KineticCoeff 5) + (clearMoment8Part9KineticCoeff 5))) + (((clearMoment8Part10KineticCoeff 5) + (clearMoment8Part11KineticCoeff 5)) + ((clearMoment8Part12KineticCoeff 5) + (clearMoment8Part13KineticCoeff 5)))))

def clearMoment8KineticCoeff6 : Poly := ((((clearMoment8Part0KineticCoeff 6) + ((clearMoment8Part1KineticCoeff 6) + (clearMoment8Part2KineticCoeff 6))) + (((clearMoment8Part3KineticCoeff 6) + (clearMoment8Part4KineticCoeff 6)) + ((clearMoment8Part5KineticCoeff 6) + (clearMoment8Part6KineticCoeff 6)))) + (((clearMoment8Part7KineticCoeff 6) + ((clearMoment8Part8KineticCoeff 6) + (clearMoment8Part9KineticCoeff 6))) + (((clearMoment8Part10KineticCoeff 6) + (clearMoment8Part11KineticCoeff 6)) + ((clearMoment8Part12KineticCoeff 6) + (clearMoment8Part13KineticCoeff 6)))))

def clearMoment8KineticCoeff7 : Poly := ((((clearMoment8Part0KineticCoeff 7) + ((clearMoment8Part1KineticCoeff 7) + (clearMoment8Part2KineticCoeff 7))) + (((clearMoment8Part3KineticCoeff 7) + (clearMoment8Part4KineticCoeff 7)) + ((clearMoment8Part5KineticCoeff 7) + (clearMoment8Part6KineticCoeff 7)))) + (((clearMoment8Part7KineticCoeff 7) + ((clearMoment8Part8KineticCoeff 7) + (clearMoment8Part9KineticCoeff 7))) + (((clearMoment8Part10KineticCoeff 7) + (clearMoment8Part11KineticCoeff 7)) + ((clearMoment8Part12KineticCoeff 7) + (clearMoment8Part13KineticCoeff 7)))))

def clearMoment8KineticCoeff8 : Poly := ((((clearMoment8Part0KineticCoeff 8) + ((clearMoment8Part1KineticCoeff 8) + (clearMoment8Part2KineticCoeff 8))) + (((clearMoment8Part3KineticCoeff 8) + (clearMoment8Part4KineticCoeff 8)) + ((clearMoment8Part5KineticCoeff 8) + (clearMoment8Part6KineticCoeff 8)))) + (((clearMoment8Part7KineticCoeff 8) + ((clearMoment8Part8KineticCoeff 8) + (clearMoment8Part9KineticCoeff 8))) + (((clearMoment8Part10KineticCoeff 8) + (clearMoment8Part11KineticCoeff 8)) + ((clearMoment8Part12KineticCoeff 8) + (clearMoment8Part13KineticCoeff 8)))))

theorem clearMoment8_kinetic : clearMoment8=
    ((((X Coord.J)^0*clearMoment8KineticCoeff0 + (X Coord.J)^1*clearMoment8KineticCoeff1) + ((X Coord.J)^2*clearMoment8KineticCoeff2 + (X Coord.J)^3*clearMoment8KineticCoeff3)) + (((X Coord.J)^4*clearMoment8KineticCoeff4 + (X Coord.J)^5*clearMoment8KineticCoeff5) + ((X Coord.J)^6*clearMoment8KineticCoeff6 + ((X Coord.J)^7*clearMoment8KineticCoeff7 + (X Coord.J)^8*clearMoment8KineticCoeff8)))) := by
  simp only [clearMoment8,clearMoment8KineticCoeff0,clearMoment8KineticCoeff1,clearMoment8KineticCoeff2,clearMoment8KineticCoeff3,clearMoment8KineticCoeff4,clearMoment8KineticCoeff5,clearMoment8KineticCoeff6,clearMoment8KineticCoeff7,clearMoment8KineticCoeff8,clearMoment8Part0_kinetic,clearMoment8Part1_kinetic,clearMoment8Part2_kinetic,clearMoment8Part3_kinetic,clearMoment8Part4_kinetic,clearMoment8Part5_kinetic,clearMoment8Part6_kinetic,clearMoment8Part7_kinetic,clearMoment8Part8_kinetic,clearMoment8Part9_kinetic,clearMoment8Part10_kinetic,clearMoment8Part11_kinetic,clearMoment8Part12_kinetic,clearMoment8Part13_kinetic]
  ring

def clearMoment8KineticCoeff0Norm : {P : Poly // clearMoment8KineticCoeff0=P} := by
  have he : clearMoment8KineticCoeff0=clearMoment8KineticCoeff0 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment8KineticCoeff0,clearMoment8Part0KineticCoeff,clearMoment8Part1KineticCoeff,clearMoment8Part2KineticCoeff,clearMoment8Part3KineticCoeff,clearMoment8Part4KineticCoeff,clearMoment8Part5KineticCoeff,clearMoment8Part6KineticCoeff,clearMoment8Part7KineticCoeff,clearMoment8Part8KineticCoeff,clearMoment8Part9KineticCoeff,clearMoment8Part10KineticCoeff,clearMoment8Part11KineticCoeff,clearMoment8Part12KineticCoeff,clearMoment8Part13KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment8KineticCoeff1Norm : {P : Poly // clearMoment8KineticCoeff1=P} := by
  have he : clearMoment8KineticCoeff1=clearMoment8KineticCoeff1 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment8KineticCoeff1,clearMoment8Part0KineticCoeff,clearMoment8Part1KineticCoeff,clearMoment8Part2KineticCoeff,clearMoment8Part3KineticCoeff,clearMoment8Part4KineticCoeff,clearMoment8Part5KineticCoeff,clearMoment8Part6KineticCoeff,clearMoment8Part7KineticCoeff,clearMoment8Part8KineticCoeff,clearMoment8Part9KineticCoeff,clearMoment8Part10KineticCoeff,clearMoment8Part11KineticCoeff,clearMoment8Part12KineticCoeff,clearMoment8Part13KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment8KineticCoeff2Norm : {P : Poly // clearMoment8KineticCoeff2=P} := by
  have he : clearMoment8KineticCoeff2=clearMoment8KineticCoeff2 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment8KineticCoeff2,clearMoment8Part0KineticCoeff,clearMoment8Part1KineticCoeff,clearMoment8Part2KineticCoeff,clearMoment8Part3KineticCoeff,clearMoment8Part4KineticCoeff,clearMoment8Part5KineticCoeff,clearMoment8Part6KineticCoeff,clearMoment8Part7KineticCoeff,clearMoment8Part8KineticCoeff,clearMoment8Part9KineticCoeff,clearMoment8Part10KineticCoeff,clearMoment8Part11KineticCoeff,clearMoment8Part12KineticCoeff,clearMoment8Part13KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment8KineticCoeff3Norm : {P : Poly // clearMoment8KineticCoeff3=P} := by
  have he : clearMoment8KineticCoeff3=clearMoment8KineticCoeff3 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment8KineticCoeff3,clearMoment8Part0KineticCoeff,clearMoment8Part1KineticCoeff,clearMoment8Part2KineticCoeff,clearMoment8Part3KineticCoeff,clearMoment8Part4KineticCoeff,clearMoment8Part5KineticCoeff,clearMoment8Part6KineticCoeff,clearMoment8Part7KineticCoeff,clearMoment8Part8KineticCoeff,clearMoment8Part9KineticCoeff,clearMoment8Part10KineticCoeff,clearMoment8Part11KineticCoeff,clearMoment8Part12KineticCoeff,clearMoment8Part13KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment8KineticCoeff4Norm : {P : Poly // clearMoment8KineticCoeff4=P} := by
  have he : clearMoment8KineticCoeff4=clearMoment8KineticCoeff4 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment8KineticCoeff4,clearMoment8Part0KineticCoeff,clearMoment8Part1KineticCoeff,clearMoment8Part2KineticCoeff,clearMoment8Part3KineticCoeff,clearMoment8Part4KineticCoeff,clearMoment8Part5KineticCoeff,clearMoment8Part6KineticCoeff,clearMoment8Part7KineticCoeff,clearMoment8Part8KineticCoeff,clearMoment8Part9KineticCoeff,clearMoment8Part10KineticCoeff,clearMoment8Part11KineticCoeff,clearMoment8Part12KineticCoeff,clearMoment8Part13KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment8KineticCoeff5Norm : {P : Poly // clearMoment8KineticCoeff5=P} := by
  have he : clearMoment8KineticCoeff5=clearMoment8KineticCoeff5 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment8KineticCoeff5,clearMoment8Part0KineticCoeff,clearMoment8Part1KineticCoeff,clearMoment8Part2KineticCoeff,clearMoment8Part3KineticCoeff,clearMoment8Part4KineticCoeff,clearMoment8Part5KineticCoeff,clearMoment8Part6KineticCoeff,clearMoment8Part7KineticCoeff,clearMoment8Part8KineticCoeff,clearMoment8Part9KineticCoeff,clearMoment8Part10KineticCoeff,clearMoment8Part11KineticCoeff,clearMoment8Part12KineticCoeff,clearMoment8Part13KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment8KineticCoeff6Norm : {P : Poly // clearMoment8KineticCoeff6=P} := by
  have he : clearMoment8KineticCoeff6=clearMoment8KineticCoeff6 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment8KineticCoeff6,clearMoment8Part0KineticCoeff,clearMoment8Part1KineticCoeff,clearMoment8Part2KineticCoeff,clearMoment8Part3KineticCoeff,clearMoment8Part4KineticCoeff,clearMoment8Part5KineticCoeff,clearMoment8Part6KineticCoeff,clearMoment8Part7KineticCoeff,clearMoment8Part8KineticCoeff,clearMoment8Part9KineticCoeff,clearMoment8Part10KineticCoeff,clearMoment8Part11KineticCoeff,clearMoment8Part12KineticCoeff,clearMoment8Part13KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment8KineticCoeff7Norm : {P : Poly // clearMoment8KineticCoeff7=P} := by
  have he : clearMoment8KineticCoeff7=clearMoment8KineticCoeff7 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment8KineticCoeff7,clearMoment8Part0KineticCoeff,clearMoment8Part1KineticCoeff,clearMoment8Part2KineticCoeff,clearMoment8Part3KineticCoeff,clearMoment8Part4KineticCoeff,clearMoment8Part5KineticCoeff,clearMoment8Part6KineticCoeff,clearMoment8Part7KineticCoeff,clearMoment8Part8KineticCoeff,clearMoment8Part9KineticCoeff,clearMoment8Part10KineticCoeff,clearMoment8Part11KineticCoeff,clearMoment8Part12KineticCoeff,clearMoment8Part13KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment8KineticCoeff8Norm : {P : Poly // clearMoment8KineticCoeff8=P} := by
  have he : clearMoment8KineticCoeff8=clearMoment8KineticCoeff8 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment8KineticCoeff8,clearMoment8Part0KineticCoeff,clearMoment8Part1KineticCoeff,clearMoment8Part2KineticCoeff,clearMoment8Part3KineticCoeff,clearMoment8Part4KineticCoeff,clearMoment8Part5KineticCoeff,clearMoment8Part6KineticCoeff,clearMoment8Part7KineticCoeff,clearMoment8Part8KineticCoeff,clearMoment8Part9KineticCoeff,clearMoment8Part10KineticCoeff,clearMoment8Part11KineticCoeff,clearMoment8Part12KineticCoeff,clearMoment8Part13KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem clearMoment8KineticCoeff0_noJ : pderiv Coord.J clearMoment8KineticCoeff0=0 := by
  rw [clearMoment8KineticCoeff0Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment8KineticCoeff0Norm,pderiv_X,Pi.single_apply,hJU,hJK]

theorem clearMoment8KineticCoeff1_noJ : pderiv Coord.J clearMoment8KineticCoeff1=0 := by
  rw [clearMoment8KineticCoeff1Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment8KineticCoeff1Norm,pderiv_X,Pi.single_apply,hJU,hJK]

theorem clearMoment8KineticCoeff2_noJ : pderiv Coord.J clearMoment8KineticCoeff2=0 := by
  rw [clearMoment8KineticCoeff2Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment8KineticCoeff2Norm,pderiv_X,Pi.single_apply,hJU,hJK]

theorem clearMoment8KineticCoeff3_noJ : pderiv Coord.J clearMoment8KineticCoeff3=0 := by
  rw [clearMoment8KineticCoeff3Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment8KineticCoeff3Norm,pderiv_X,Pi.single_apply,hJU,hJK]

theorem clearMoment8KineticCoeff4_noJ : pderiv Coord.J clearMoment8KineticCoeff4=0 := by
  rw [clearMoment8KineticCoeff4Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment8KineticCoeff4Norm,pderiv_X,Pi.single_apply,hJU,hJK]

theorem clearMoment8KineticCoeff5_noJ : pderiv Coord.J clearMoment8KineticCoeff5=0 := by
  rw [clearMoment8KineticCoeff5Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment8KineticCoeff5Norm,pderiv_X,Pi.single_apply,hJU,hJK]

theorem clearMoment8KineticCoeff6_noJ : pderiv Coord.J clearMoment8KineticCoeff6=0 := by
  rw [clearMoment8KineticCoeff6Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment8KineticCoeff6Norm,pderiv_X,Pi.single_apply,hJU,hJK]

theorem clearMoment8KineticCoeff7_noJ : pderiv Coord.J clearMoment8KineticCoeff7=0 := by
  rw [clearMoment8KineticCoeff7Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment8KineticCoeff7Norm,pderiv_X,Pi.single_apply,hJU,hJK]

theorem clearMoment8KineticCoeff8_noJ : pderiv Coord.J clearMoment8KineticCoeff8=0 := by
  rw [clearMoment8KineticCoeff8Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment8KineticCoeff8Norm,pderiv_X,Pi.single_apply,hJU,hJK]

end
end HTGeometry.ThetaRatioKineticContraction
