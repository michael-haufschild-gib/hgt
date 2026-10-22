import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticClockMoments
/-! Complete kinetic coefficient decomposition; every literal source term is retained. -/
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def clearMoment6Part0KineticCoeff (d : ℕ) : Poly := (((((if 0=d then (X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((0+0)/2)*(-8338360320) else 0)) + (((if 0=d then (X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((0+0)/2)*(-90870584832) else 0)) + ((if 1=d then (X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((1+1)/2)*(31536096768) else 0)))) + (((if 1=d then (X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((3+1)/2)*(-934861824) else 0)) + (((if 1=d then (X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((5+1)/2)*(21026304) else 0)) + ((if 2=d then (X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((0+2)/2)*(-32045393664) else 0))))) + ((((if 2=d then (X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((2+2)/2)*(-4303176192) else 0)) + (((if 2=d then (X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((4+2)/2)*(149154048) else 0)) + ((if 3=d then (X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((1+3)/2)*(3321160704) else 0)))) + (((if 3=d then (X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((3+3)/2)*(377478144) else 0)) + (((if 4=d then (X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((0+4)/2)*(4911197184) else 0)) + ((if 4=d then (X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((2+4)/2)*(-127650816) else 0))))))

theorem clearMoment6Part0_kinetic : clearMoment6Part0=
    (((X Coord.J)^0*clearMoment6Part0KineticCoeff 0 + ((X Coord.J)^1*clearMoment6Part0KineticCoeff 1 + (X Coord.J)^2*clearMoment6Part0KineticCoeff 2)) + (((X Coord.J)^3*clearMoment6Part0KineticCoeff 3 + (X Coord.J)^4*clearMoment6Part0KineticCoeff 4) + ((X Coord.J)^5*clearMoment6Part0KineticCoeff 5 + (X Coord.J)^6*clearMoment6Part0KineticCoeff 6))) := by
  norm_num [clearMoment6Part0,clearMoment6Part0KineticCoeff]
  ring

def clearMoment6Part1KineticCoeff (d : ℕ) : Poly := (((((if 5=d then (X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((1+5)/2)*(-232906752) else 0)) + (((if 6=d then (X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((0+6)/2)*(-107495424) else 0)) + ((if 0=d then (X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((2+0)/2)*(1239681024) else 0)))) + (((if 0=d then (X Coord.U : Poly)^(7-1)*(X Coord.K : Poly)^((4+0)/2)*(-54120960) else 0)) + (((if 0=d then (X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((0+0)/2)*(-262125911808) else 0)) + ((if 1=d then (X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((1+1)/2)*(98870035968) else 0))))) + ((((if 1=d then (X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((3+1)/2)*(1579585536) else 0)) + (((if 1=d then (X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((5+1)/2)*(-73446912) else 0)) + ((if 2=d then (X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((0+2)/2)*(-6505152768) else 0)))) + (((if 2=d then (X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((2+2)/2)*(-17677398528) else 0)) + (((if 2=d then (X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((4+2)/2)*(-85536000) else 0)) + ((if 3=d then (X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((1+3)/2)*(-11663253504) else 0))))))

theorem clearMoment6Part1_kinetic : clearMoment6Part1=
    (((X Coord.J)^0*clearMoment6Part1KineticCoeff 0 + ((X Coord.J)^1*clearMoment6Part1KineticCoeff 1 + (X Coord.J)^2*clearMoment6Part1KineticCoeff 2)) + (((X Coord.J)^3*clearMoment6Part1KineticCoeff 3 + (X Coord.J)^4*clearMoment6Part1KineticCoeff 4) + ((X Coord.J)^5*clearMoment6Part1KineticCoeff 5 + (X Coord.J)^6*clearMoment6Part1KineticCoeff 6))) := by
  norm_num [clearMoment6Part1,clearMoment6Part1KineticCoeff]
  ring

def clearMoment6Part2KineticCoeff (d : ℕ) : Poly := (((((if 3=d then (X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((3+3)/2)*(1206337536) else 0)) + (((if 4=d then (X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((0+4)/2)*(886837248) else 0)) + ((if 4=d then (X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((2+4)/2)*(1155575808) else 0)))) + (((if 5=d then (X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((1+5)/2)*(537477120) else 0)) + (((if 0=d then (X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((2+0)/2)*(-5641643520) else 0)) + ((if 0=d then (X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((4+0)/2)*(110419200) else 0))))) + ((((if 0=d then (X Coord.U : Poly)^(7-2)*(X Coord.K : Poly)^((6+0)/2)*(1492992) else 0)) + (((if 0=d then (X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((0+0)/2)*(-203900763456) else 0)) + ((if 1=d then (X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((1+1)/2)*(50993141760) else 0)))) + (((if 1=d then (X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((3+1)/2)*(15311379456) else 0)) + (((if 1=d then (X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((5+1)/2)*(-151041024) else 0)) + ((if 2=d then (X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((0+2)/2)*(-16144468992) else 0))))))

theorem clearMoment6Part2_kinetic : clearMoment6Part2=
    (((X Coord.J)^0*clearMoment6Part2KineticCoeff 0 + ((X Coord.J)^1*clearMoment6Part2KineticCoeff 1 + (X Coord.J)^2*clearMoment6Part2KineticCoeff 2)) + (((X Coord.J)^3*clearMoment6Part2KineticCoeff 3 + (X Coord.J)^4*clearMoment6Part2KineticCoeff 4) + ((X Coord.J)^5*clearMoment6Part2KineticCoeff 5 + (X Coord.J)^6*clearMoment6Part2KineticCoeff 6))) := by
  norm_num [clearMoment6Part2,clearMoment6Part2KineticCoeff]
  ring

def clearMoment6Part3KineticCoeff (d : ℕ) : Poly := (((((if 2=d then (X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((2+2)/2)*(7874039808) else 0)) + (((if 2=d then (X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((4+2)/2)*(-1541514240) else 0)) + ((if 3=d then (X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((1+3)/2)*(-1370566656) else 0)))) + (((if 3=d then (X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((3+3)/2)*(-1818464256) else 0)) + (((if 4=d then (X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((0+4)/2)*(241864704) else 0)) + ((if 4=d then (X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((2+4)/2)*(-1101828096) else 0))))) + ((((if 0=d then (X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((2+0)/2)*(-47910346560) else 0)) + (((if 0=d then (X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((4+0)/2)*(1067535936) else 0)) + ((if 0=d then (X Coord.U : Poly)^(7-3)*(X Coord.K : Poly)^((6+0)/2)*(-18035136) else 0)))) + (((if 0=d then (X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((0+0)/2)*(-122353307136) else 0)) + (((if 1=d then (X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((1+1)/2)*(39484412928) else 0)) + ((if 1=d then (X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((3+1)/2)*(-2002102272) else 0))))))

theorem clearMoment6Part3_kinetic : clearMoment6Part3=
    (((X Coord.J)^0*clearMoment6Part3KineticCoeff 0 + ((X Coord.J)^1*clearMoment6Part3KineticCoeff 1 + (X Coord.J)^2*clearMoment6Part3KineticCoeff 2)) + (((X Coord.J)^3*clearMoment6Part3KineticCoeff 3 + (X Coord.J)^4*clearMoment6Part3KineticCoeff 4) + ((X Coord.J)^5*clearMoment6Part3KineticCoeff 5 + (X Coord.J)^6*clearMoment6Part3KineticCoeff 6))) := by
  norm_num [clearMoment6Part3,clearMoment6Part3KineticCoeff]
  ring

def clearMoment6Part4KineticCoeff (d : ℕ) : Poly := (((((if 1=d then (X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((5+1)/2)*(750228480) else 0)) + (((if 2=d then (X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((0+2)/2)*(-3083774976) else 0)) + ((if 2=d then (X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((2+2)/2)*(-524040192) else 0)))) + (((if 2=d then (X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((4+2)/2)*(1350411264) else 0)) + (((if 3=d then (X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((1+3)/2)*(-967458816) else 0)) + ((if 3=d then (X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((3+3)/2)*(1182449664) else 0))))) + ((((if 0=d then (X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((2+0)/2)*(-15444069120) else 0)) + (((if 0=d then (X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((4+0)/2)*(-4425228288) else 0)) + ((if 0=d then (X Coord.U : Poly)^(7-4)*(X Coord.K : Poly)^((6+0)/2)*(93747456) else 0)))) + (((if 0=d then (X Coord.U : Poly)^(7-5)*(X Coord.K : Poly)^((0+0)/2)*(952342272) else 0)) + (((if 1=d then (X Coord.U : Poly)^(7-5)*(X Coord.K : Poly)^((1+1)/2)*(6167549952) else 0)) + ((if 1=d then (X Coord.U : Poly)^(7-5)*(X Coord.K : Poly)^((3+1)/2)*(1612431360) else 0))))))

theorem clearMoment6Part4_kinetic : clearMoment6Part4=
    (((X Coord.J)^0*clearMoment6Part4KineticCoeff 0 + ((X Coord.J)^1*clearMoment6Part4KineticCoeff 1 + (X Coord.J)^2*clearMoment6Part4KineticCoeff 2)) + (((X Coord.J)^3*clearMoment6Part4KineticCoeff 3 + (X Coord.J)^4*clearMoment6Part4KineticCoeff 4) + ((X Coord.J)^5*clearMoment6Part4KineticCoeff 5 + (X Coord.J)^6*clearMoment6Part4KineticCoeff 6))) := by
  norm_num [clearMoment6Part4,clearMoment6Part4KineticCoeff]
  ring

def clearMoment6Part5KineticCoeff (d : ℕ) : Poly := (((((if 1=d then (X Coord.U : Poly)^(7-5)*(X Coord.K : Poly)^((5+1)/2)*(-488208384) else 0)) + (((if 2=d then (X Coord.U : Poly)^(7-5)*(X Coord.K : Poly)^((2+2)/2)*(1451188224) else 0)) + ((if 2=d then (X Coord.U : Poly)^(7-5)*(X Coord.K : Poly)^((4+2)/2)*(-698720256) else 0)))) + (((if 0=d then (X Coord.U : Poly)^(7-5)*(X Coord.K : Poly)^((2+0)/2)*(-23657391360) else 0)) + (((if 0=d then (X Coord.U : Poly)^(7-5)*(X Coord.K : Poly)^((4+0)/2)*(915390720) else 0)) + ((if 0=d then (X Coord.U : Poly)^(7-5)*(X Coord.K : Poly)^((6+0)/2)*(-151352064) else 0))))) + ((((if 1=d then (X Coord.U : Poly)^(7-6)*(X Coord.K : Poly)^((3+1)/2)*(-967458816) else 0)) + (((if 1=d then (X Coord.U : Poly)^(7-6)*(X Coord.K : Poly)^((5+1)/2)*(214990848) else 0)) + ((if 0=d then (X Coord.U : Poly)^(7-6)*(X Coord.K : Poly)^((2+0)/2)*(-3083774976) else 0)))) + (((if 0=d then (X Coord.U : Poly)^(7-6)*(X Coord.K : Poly)^((4+0)/2)*(-604661760) else 0)) + (((if 0=d then (X Coord.U : Poly)^(7-6)*(X Coord.K : Poly)^((6+0)/2)*(69424128) else 0)) + ((if 0=d then (X Coord.U : Poly)^(7-7)*(X Coord.K : Poly)^((4+0)/2)*(241864704) else 0))))))

theorem clearMoment6Part5_kinetic : clearMoment6Part5=
    (((X Coord.J)^0*clearMoment6Part5KineticCoeff 0 + ((X Coord.J)^1*clearMoment6Part5KineticCoeff 1 + (X Coord.J)^2*clearMoment6Part5KineticCoeff 2)) + (((X Coord.J)^3*clearMoment6Part5KineticCoeff 3 + (X Coord.J)^4*clearMoment6Part5KineticCoeff 4) + ((X Coord.J)^5*clearMoment6Part5KineticCoeff 5 + (X Coord.J)^6*clearMoment6Part5KineticCoeff 6))) := by
  norm_num [clearMoment6Part5,clearMoment6Part5KineticCoeff]
  ring

def clearMoment6Part6KineticCoeff (d : ℕ) : Poly := (((((if 0=d then (X Coord.U : Poly)^(7-7)*(X Coord.K : Poly)^((6+0)/2)*(-26873856) else 0)) + (((if 1=d then (X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((1+1)/2)*(953026560) else 0)) + ((if 1=d then (X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((3+1)/2)*(112637952) else 0)))) + (((if 1=d then (X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((5+1)/2)*(-1990656) else 0)) + (((if 2=d then (X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((0+2)/2)*(-10518875136) else 0)) + ((if 2=d then (X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((2+2)/2)*(833836032) else 0))))) + ((((if 2=d then (X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((4+2)/2)*(-17418240) else 0)) + (((if 3=d then (X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((1+3)/2)*(2364152832) else 0)) + ((if 3=d then (X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((3+3)/2)*(-90160128) else 0)))) + (((if 4=d then (X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((0+4)/2)*(1547486208) else 0)) + (((if 4=d then (X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((2+4)/2)*(-211756032) else 0)) + ((if 5=d then (X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((1+5)/2)*(-137355264) else 0))))))

theorem clearMoment6Part6_kinetic : clearMoment6Part6=
    (((X Coord.J)^0*clearMoment6Part6KineticCoeff 0 + ((X Coord.J)^1*clearMoment6Part6KineticCoeff 1 + (X Coord.J)^2*clearMoment6Part6KineticCoeff 2)) + (((X Coord.J)^3*clearMoment6Part6KineticCoeff 3 + (X Coord.J)^4*clearMoment6Part6KineticCoeff 4) + ((X Coord.J)^5*clearMoment6Part6KineticCoeff 5 + (X Coord.J)^6*clearMoment6Part6KineticCoeff 6))) := by
  norm_num [clearMoment6Part6,clearMoment6Part6KineticCoeff]
  ring

def clearMoment6Part7KineticCoeff (d : ℕ) : Poly := ((((if 6=d then (X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((0+6)/2)*(-35831808) else 0)) + ((if 0=d then (X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((2+0)/2)*(-167712768) else 0))) + (((if 0=d then (X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((4+0)/2)*(5971968) else 0)) + ((if 0=d then (X Coord.U : Poly)^(7-0)*(X Coord.K : Poly)^((0+0)/2)*(0) else 0))))

theorem clearMoment6Part7_kinetic : clearMoment6Part7=
    (((X Coord.J)^0*clearMoment6Part7KineticCoeff 0 + ((X Coord.J)^1*clearMoment6Part7KineticCoeff 1 + (X Coord.J)^2*clearMoment6Part7KineticCoeff 2)) + (((X Coord.J)^3*clearMoment6Part7KineticCoeff 3 + (X Coord.J)^4*clearMoment6Part7KineticCoeff 4) + ((X Coord.J)^5*clearMoment6Part7KineticCoeff 5 + (X Coord.J)^6*clearMoment6Part7KineticCoeff 6))) := by
  norm_num [clearMoment6Part7,clearMoment6Part7KineticCoeff]
  ring

def clearMoment6KineticCoeff0 : Poly := ((((clearMoment6Part0KineticCoeff 0) + (clearMoment6Part1KineticCoeff 0)) + ((clearMoment6Part2KineticCoeff 0) + (clearMoment6Part3KineticCoeff 0))) + (((clearMoment6Part4KineticCoeff 0) + (clearMoment6Part5KineticCoeff 0)) + ((clearMoment6Part6KineticCoeff 0) + (clearMoment6Part7KineticCoeff 0))))

def clearMoment6KineticCoeff1 : Poly := ((((clearMoment6Part0KineticCoeff 1) + (clearMoment6Part1KineticCoeff 1)) + ((clearMoment6Part2KineticCoeff 1) + (clearMoment6Part3KineticCoeff 1))) + (((clearMoment6Part4KineticCoeff 1) + (clearMoment6Part5KineticCoeff 1)) + ((clearMoment6Part6KineticCoeff 1) + (clearMoment6Part7KineticCoeff 1))))

def clearMoment6KineticCoeff2 : Poly := ((((clearMoment6Part0KineticCoeff 2) + (clearMoment6Part1KineticCoeff 2)) + ((clearMoment6Part2KineticCoeff 2) + (clearMoment6Part3KineticCoeff 2))) + (((clearMoment6Part4KineticCoeff 2) + (clearMoment6Part5KineticCoeff 2)) + ((clearMoment6Part6KineticCoeff 2) + (clearMoment6Part7KineticCoeff 2))))

def clearMoment6KineticCoeff3 : Poly := ((((clearMoment6Part0KineticCoeff 3) + (clearMoment6Part1KineticCoeff 3)) + ((clearMoment6Part2KineticCoeff 3) + (clearMoment6Part3KineticCoeff 3))) + (((clearMoment6Part4KineticCoeff 3) + (clearMoment6Part5KineticCoeff 3)) + ((clearMoment6Part6KineticCoeff 3) + (clearMoment6Part7KineticCoeff 3))))

def clearMoment6KineticCoeff4 : Poly := ((((clearMoment6Part0KineticCoeff 4) + (clearMoment6Part1KineticCoeff 4)) + ((clearMoment6Part2KineticCoeff 4) + (clearMoment6Part3KineticCoeff 4))) + (((clearMoment6Part4KineticCoeff 4) + (clearMoment6Part5KineticCoeff 4)) + ((clearMoment6Part6KineticCoeff 4) + (clearMoment6Part7KineticCoeff 4))))

def clearMoment6KineticCoeff5 : Poly := ((((clearMoment6Part0KineticCoeff 5) + (clearMoment6Part1KineticCoeff 5)) + ((clearMoment6Part2KineticCoeff 5) + (clearMoment6Part3KineticCoeff 5))) + (((clearMoment6Part4KineticCoeff 5) + (clearMoment6Part5KineticCoeff 5)) + ((clearMoment6Part6KineticCoeff 5) + (clearMoment6Part7KineticCoeff 5))))

def clearMoment6KineticCoeff6 : Poly := ((((clearMoment6Part0KineticCoeff 6) + (clearMoment6Part1KineticCoeff 6)) + ((clearMoment6Part2KineticCoeff 6) + (clearMoment6Part3KineticCoeff 6))) + (((clearMoment6Part4KineticCoeff 6) + (clearMoment6Part5KineticCoeff 6)) + ((clearMoment6Part6KineticCoeff 6) + (clearMoment6Part7KineticCoeff 6))))

theorem clearMoment6_kinetic : clearMoment6=
    (((X Coord.J)^0*clearMoment6KineticCoeff0 + ((X Coord.J)^1*clearMoment6KineticCoeff1 + (X Coord.J)^2*clearMoment6KineticCoeff2)) + (((X Coord.J)^3*clearMoment6KineticCoeff3 + (X Coord.J)^4*clearMoment6KineticCoeff4) + ((X Coord.J)^5*clearMoment6KineticCoeff5 + (X Coord.J)^6*clearMoment6KineticCoeff6))) := by
  simp only [clearMoment6,clearMoment6KineticCoeff0,clearMoment6KineticCoeff1,clearMoment6KineticCoeff2,clearMoment6KineticCoeff3,clearMoment6KineticCoeff4,clearMoment6KineticCoeff5,clearMoment6KineticCoeff6,clearMoment6Part0_kinetic,clearMoment6Part1_kinetic,clearMoment6Part2_kinetic,clearMoment6Part3_kinetic,clearMoment6Part4_kinetic,clearMoment6Part5_kinetic,clearMoment6Part6_kinetic,clearMoment6Part7_kinetic]
  ring

def clearMoment6KineticCoeff0Norm : {P : Poly // clearMoment6KineticCoeff0=P} := by
  have he : clearMoment6KineticCoeff0=clearMoment6KineticCoeff0 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment6KineticCoeff0,clearMoment6Part0KineticCoeff,clearMoment6Part1KineticCoeff,clearMoment6Part2KineticCoeff,clearMoment6Part3KineticCoeff,clearMoment6Part4KineticCoeff,clearMoment6Part5KineticCoeff,clearMoment6Part6KineticCoeff,clearMoment6Part7KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment6KineticCoeff1Norm : {P : Poly // clearMoment6KineticCoeff1=P} := by
  have he : clearMoment6KineticCoeff1=clearMoment6KineticCoeff1 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment6KineticCoeff1,clearMoment6Part0KineticCoeff,clearMoment6Part1KineticCoeff,clearMoment6Part2KineticCoeff,clearMoment6Part3KineticCoeff,clearMoment6Part4KineticCoeff,clearMoment6Part5KineticCoeff,clearMoment6Part6KineticCoeff,clearMoment6Part7KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment6KineticCoeff2Norm : {P : Poly // clearMoment6KineticCoeff2=P} := by
  have he : clearMoment6KineticCoeff2=clearMoment6KineticCoeff2 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment6KineticCoeff2,clearMoment6Part0KineticCoeff,clearMoment6Part1KineticCoeff,clearMoment6Part2KineticCoeff,clearMoment6Part3KineticCoeff,clearMoment6Part4KineticCoeff,clearMoment6Part5KineticCoeff,clearMoment6Part6KineticCoeff,clearMoment6Part7KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment6KineticCoeff3Norm : {P : Poly // clearMoment6KineticCoeff3=P} := by
  have he : clearMoment6KineticCoeff3=clearMoment6KineticCoeff3 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment6KineticCoeff3,clearMoment6Part0KineticCoeff,clearMoment6Part1KineticCoeff,clearMoment6Part2KineticCoeff,clearMoment6Part3KineticCoeff,clearMoment6Part4KineticCoeff,clearMoment6Part5KineticCoeff,clearMoment6Part6KineticCoeff,clearMoment6Part7KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment6KineticCoeff4Norm : {P : Poly // clearMoment6KineticCoeff4=P} := by
  have he : clearMoment6KineticCoeff4=clearMoment6KineticCoeff4 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment6KineticCoeff4,clearMoment6Part0KineticCoeff,clearMoment6Part1KineticCoeff,clearMoment6Part2KineticCoeff,clearMoment6Part3KineticCoeff,clearMoment6Part4KineticCoeff,clearMoment6Part5KineticCoeff,clearMoment6Part6KineticCoeff,clearMoment6Part7KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment6KineticCoeff5Norm : {P : Poly // clearMoment6KineticCoeff5=P} := by
  have he : clearMoment6KineticCoeff5=clearMoment6KineticCoeff5 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment6KineticCoeff5,clearMoment6Part0KineticCoeff,clearMoment6Part1KineticCoeff,clearMoment6Part2KineticCoeff,clearMoment6Part3KineticCoeff,clearMoment6Part4KineticCoeff,clearMoment6Part5KineticCoeff,clearMoment6Part6KineticCoeff,clearMoment6Part7KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment6KineticCoeff6Norm : {P : Poly // clearMoment6KineticCoeff6=P} := by
  have he : clearMoment6KineticCoeff6=clearMoment6KineticCoeff6 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment6KineticCoeff6,clearMoment6Part0KineticCoeff,clearMoment6Part1KineticCoeff,clearMoment6Part2KineticCoeff,clearMoment6Part3KineticCoeff,clearMoment6Part4KineticCoeff,clearMoment6Part5KineticCoeff,clearMoment6Part6KineticCoeff,clearMoment6Part7KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem clearMoment6KineticCoeff0_noJ : pderiv Coord.J clearMoment6KineticCoeff0=0 := by
  rw [clearMoment6KineticCoeff0Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment6KineticCoeff0Norm,pderiv_X,Pi.single_apply,hJU,hJK]

theorem clearMoment6KineticCoeff1_noJ : pderiv Coord.J clearMoment6KineticCoeff1=0 := by
  rw [clearMoment6KineticCoeff1Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment6KineticCoeff1Norm,pderiv_X,Pi.single_apply,hJU,hJK]

theorem clearMoment6KineticCoeff2_noJ : pderiv Coord.J clearMoment6KineticCoeff2=0 := by
  rw [clearMoment6KineticCoeff2Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment6KineticCoeff2Norm,pderiv_X,Pi.single_apply,hJU,hJK]

theorem clearMoment6KineticCoeff3_noJ : pderiv Coord.J clearMoment6KineticCoeff3=0 := by
  rw [clearMoment6KineticCoeff3Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment6KineticCoeff3Norm,pderiv_X,Pi.single_apply,hJU,hJK]

theorem clearMoment6KineticCoeff4_noJ : pderiv Coord.J clearMoment6KineticCoeff4=0 := by
  rw [clearMoment6KineticCoeff4Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment6KineticCoeff4Norm,pderiv_X,Pi.single_apply,hJU,hJK]

theorem clearMoment6KineticCoeff5_noJ : pderiv Coord.J clearMoment6KineticCoeff5=0 := by
  rw [clearMoment6KineticCoeff5Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment6KineticCoeff5Norm,pderiv_X,Pi.single_apply,hJU,hJK]

theorem clearMoment6KineticCoeff6_noJ : pderiv Coord.J clearMoment6KineticCoeff6=0 := by
  rw [clearMoment6KineticCoeff6Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment6KineticCoeff6Norm,pderiv_X,Pi.single_apply,hJU,hJK]

end
end HTGeometry.ThetaRatioKineticContraction
