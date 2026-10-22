import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioInfinityFlow
/-! # Exact source-flow compactification and the third-slope expanding mode. -/

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def scaled6Part0Low : Poly := ((((if 0≤5 then (X Coord.U:Poly)^(5-0)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(-8338360320) else 0) + ((if 1≤5 then (X Coord.U:Poly)^(5-1)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(-90870584832) else 0) + (if 1≤5 then (X Coord.U:Poly)^(5-1)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(31536096768) else 0))) + ((if 1≤5 then (X Coord.U:Poly)^(5-1)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(-934861824) else 0) + ((if 1≤5 then (X Coord.U:Poly)^(5-1)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(21026304) else 0) + (if 1≤5 then (X Coord.U:Poly)^(5-1)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(-32045393664) else 0)))) + (((if 1≤5 then (X Coord.U:Poly)^(5-1)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(-4303176192) else 0) + ((if 1≤5 then (X Coord.U:Poly)^(5-1)*driftSquare^((4+2)/2)*(C (1/3:ℂ)*deficit)^2*(149154048) else 0) + (if 1≤5 then (X Coord.U:Poly)^(5-1)*driftSquare^((1+3)/2)*(C (1/3:ℂ)*deficit)^3*(3321160704) else 0))) + ((if 1≤5 then (X Coord.U:Poly)^(5-1)*driftSquare^((3+3)/2)*(C (1/3:ℂ)*deficit)^3*(377478144) else 0) + ((if 1≤5 then (X Coord.U:Poly)^(5-1)*driftSquare^((0+4)/2)*(C (1/3:ℂ)*deficit)^4*(4911197184) else 0) + (if 1≤5 then (X Coord.U:Poly)^(5-1)*driftSquare^((2+4)/2)*(C (1/3:ℂ)*deficit)^4*(-127650816) else 0)))))
def scaled6Part0Mid : Poly := (0:Poly)
def scaled6Part0Upper : Poly := (0:Poly)

theorem scaled6Part0_clear (h r t : ℂ) (hh : h≠0) :
    h^(5+2)*eval (sourcePoint h r t) moment6Part0 =
      h^2*eval (basePoint h r t) scaled6Part0Low+
      h*eval (basePoint h r t) scaled6Part0Mid+eval (basePoint h r t) scaled6Part0Upper := by
  norm_num [moment6Part0,scaled6Part0Low,scaled6Part0Mid,scaled6Part0Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled6Part1Low : Poly := ((((if 1≤5 then (X Coord.U:Poly)^(5-1)*driftSquare^((1+5)/2)*(C (1/3:ℂ)*deficit)^5*(-232906752) else 0) + ((if 1≤5 then (X Coord.U:Poly)^(5-1)*driftSquare^((0+6)/2)*(C (1/3:ℂ)*deficit)^6*(-107495424) else 0) + (if 1≤5 then (X Coord.U:Poly)^(5-1)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(1239681024) else 0))) + ((if 1≤5 then (X Coord.U:Poly)^(5-1)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(-54120960) else 0) + ((if 2≤5 then (X Coord.U:Poly)^(5-2)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(-262125911808) else 0) + (if 2≤5 then (X Coord.U:Poly)^(5-2)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(98870035968) else 0)))) + (((if 2≤5 then (X Coord.U:Poly)^(5-2)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(1579585536) else 0) + ((if 2≤5 then (X Coord.U:Poly)^(5-2)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(-73446912) else 0) + (if 2≤5 then (X Coord.U:Poly)^(5-2)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(-6505152768) else 0))) + ((if 2≤5 then (X Coord.U:Poly)^(5-2)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(-17677398528) else 0) + ((if 2≤5 then (X Coord.U:Poly)^(5-2)*driftSquare^((4+2)/2)*(C (1/3:ℂ)*deficit)^2*(-85536000) else 0) + (if 2≤5 then (X Coord.U:Poly)^(5-2)*driftSquare^((1+3)/2)*(C (1/3:ℂ)*deficit)^3*(-11663253504) else 0)))))
def scaled6Part1Mid : Poly := (0:Poly)
def scaled6Part1Upper : Poly := (0:Poly)

theorem scaled6Part1_clear (h r t : ℂ) (hh : h≠0) :
    h^(5+2)*eval (sourcePoint h r t) moment6Part1 =
      h^2*eval (basePoint h r t) scaled6Part1Low+
      h*eval (basePoint h r t) scaled6Part1Mid+eval (basePoint h r t) scaled6Part1Upper := by
  norm_num [moment6Part1,scaled6Part1Low,scaled6Part1Mid,scaled6Part1Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled6Part2Low : Poly := ((((if 2≤5 then (X Coord.U:Poly)^(5-2)*driftSquare^((3+3)/2)*(C (1/3:ℂ)*deficit)^3*(1206337536) else 0) + ((if 2≤5 then (X Coord.U:Poly)^(5-2)*driftSquare^((0+4)/2)*(C (1/3:ℂ)*deficit)^4*(886837248) else 0) + (if 2≤5 then (X Coord.U:Poly)^(5-2)*driftSquare^((2+4)/2)*(C (1/3:ℂ)*deficit)^4*(1155575808) else 0))) + ((if 2≤5 then (X Coord.U:Poly)^(5-2)*driftSquare^((1+5)/2)*(C (1/3:ℂ)*deficit)^5*(537477120) else 0) + ((if 2≤5 then (X Coord.U:Poly)^(5-2)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(-5641643520) else 0) + (if 2≤5 then (X Coord.U:Poly)^(5-2)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(110419200) else 0)))) + (((if 2≤5 then (X Coord.U:Poly)^(5-2)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(1492992) else 0) + ((if 3≤5 then (X Coord.U:Poly)^(5-3)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(-203900763456) else 0) + (if 3≤5 then (X Coord.U:Poly)^(5-3)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(50993141760) else 0))) + ((if 3≤5 then (X Coord.U:Poly)^(5-3)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(15311379456) else 0) + ((if 3≤5 then (X Coord.U:Poly)^(5-3)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(-151041024) else 0) + (if 3≤5 then (X Coord.U:Poly)^(5-3)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(-16144468992) else 0)))))
def scaled6Part2Mid : Poly := (0:Poly)
def scaled6Part2Upper : Poly := (0:Poly)

theorem scaled6Part2_clear (h r t : ℂ) (hh : h≠0) :
    h^(5+2)*eval (sourcePoint h r t) moment6Part2 =
      h^2*eval (basePoint h r t) scaled6Part2Low+
      h*eval (basePoint h r t) scaled6Part2Mid+eval (basePoint h r t) scaled6Part2Upper := by
  norm_num [moment6Part2,scaled6Part2Low,scaled6Part2Mid,scaled6Part2Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled6Part3Low : Poly := ((((if 3≤5 then (X Coord.U:Poly)^(5-3)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(7874039808) else 0) + ((if 3≤5 then (X Coord.U:Poly)^(5-3)*driftSquare^((4+2)/2)*(C (1/3:ℂ)*deficit)^2*(-1541514240) else 0) + (if 3≤5 then (X Coord.U:Poly)^(5-3)*driftSquare^((1+3)/2)*(C (1/3:ℂ)*deficit)^3*(-1370566656) else 0))) + ((if 3≤5 then (X Coord.U:Poly)^(5-3)*driftSquare^((3+3)/2)*(C (1/3:ℂ)*deficit)^3*(-1818464256) else 0) + ((if 3≤5 then (X Coord.U:Poly)^(5-3)*driftSquare^((0+4)/2)*(C (1/3:ℂ)*deficit)^4*(241864704) else 0) + (if 3≤5 then (X Coord.U:Poly)^(5-3)*driftSquare^((2+4)/2)*(C (1/3:ℂ)*deficit)^4*(-1101828096) else 0)))) + (((if 3≤5 then (X Coord.U:Poly)^(5-3)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(-47910346560) else 0) + ((if 3≤5 then (X Coord.U:Poly)^(5-3)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(1067535936) else 0) + (if 3≤5 then (X Coord.U:Poly)^(5-3)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(-18035136) else 0))) + ((if 4≤5 then (X Coord.U:Poly)^(5-4)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(-122353307136) else 0) + ((if 4≤5 then (X Coord.U:Poly)^(5-4)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(39484412928) else 0) + (if 4≤5 then (X Coord.U:Poly)^(5-4)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(-2002102272) else 0)))))
def scaled6Part3Mid : Poly := (0:Poly)
def scaled6Part3Upper : Poly := (0:Poly)

theorem scaled6Part3_clear (h r t : ℂ) (hh : h≠0) :
    h^(5+2)*eval (sourcePoint h r t) moment6Part3 =
      h^2*eval (basePoint h r t) scaled6Part3Low+
      h*eval (basePoint h r t) scaled6Part3Mid+eval (basePoint h r t) scaled6Part3Upper := by
  norm_num [moment6Part3,scaled6Part3Low,scaled6Part3Mid,scaled6Part3Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled6Part4Low : Poly := ((((if 4≤5 then (X Coord.U:Poly)^(5-4)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(750228480) else 0) + ((if 4≤5 then (X Coord.U:Poly)^(5-4)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(-3083774976) else 0) + (if 4≤5 then (X Coord.U:Poly)^(5-4)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(-524040192) else 0))) + ((if 4≤5 then (X Coord.U:Poly)^(5-4)*driftSquare^((4+2)/2)*(C (1/3:ℂ)*deficit)^2*(1350411264) else 0) + ((if 4≤5 then (X Coord.U:Poly)^(5-4)*driftSquare^((1+3)/2)*(C (1/3:ℂ)*deficit)^3*(-967458816) else 0) + (if 4≤5 then (X Coord.U:Poly)^(5-4)*driftSquare^((3+3)/2)*(C (1/3:ℂ)*deficit)^3*(1182449664) else 0)))) + (((if 4≤5 then (X Coord.U:Poly)^(5-4)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(-15444069120) else 0) + ((if 4≤5 then (X Coord.U:Poly)^(5-4)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(-4425228288) else 0) + (if 4≤5 then (X Coord.U:Poly)^(5-4)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(93747456) else 0))) + ((if 5≤5 then (X Coord.U:Poly)^(5-5)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(952342272) else 0) + ((if 5≤5 then (X Coord.U:Poly)^(5-5)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(6167549952) else 0) + (if 5≤5 then (X Coord.U:Poly)^(5-5)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(1612431360) else 0)))))
def scaled6Part4Mid : Poly := (0:Poly)
def scaled6Part4Upper : Poly := (0:Poly)

theorem scaled6Part4_clear (h r t : ℂ) (hh : h≠0) :
    h^(5+2)*eval (sourcePoint h r t) moment6Part4 =
      h^2*eval (basePoint h r t) scaled6Part4Low+
      h*eval (basePoint h r t) scaled6Part4Mid+eval (basePoint h r t) scaled6Part4Upper := by
  norm_num [moment6Part4,scaled6Part4Low,scaled6Part4Mid,scaled6Part4Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled6Part5Low : Poly := ((((if 5≤5 then (X Coord.U:Poly)^(5-5)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(-488208384) else 0) + ((if 5≤5 then (X Coord.U:Poly)^(5-5)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(1451188224) else 0) + (if 5≤5 then (X Coord.U:Poly)^(5-5)*driftSquare^((4+2)/2)*(C (1/3:ℂ)*deficit)^2*(-698720256) else 0))) + ((if 5≤5 then (X Coord.U:Poly)^(5-5)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(-23657391360) else 0) + ((if 5≤5 then (X Coord.U:Poly)^(5-5)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(915390720) else 0) + (if 5≤5 then (X Coord.U:Poly)^(5-5)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(-151352064) else 0)))) + (((if 6≤5 then (X Coord.U:Poly)^(5-6)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(-967458816) else 0) + ((if 6≤5 then (X Coord.U:Poly)^(5-6)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(214990848) else 0) + (if 6≤5 then (X Coord.U:Poly)^(5-6)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(-3083774976) else 0))) + ((if 6≤5 then (X Coord.U:Poly)^(5-6)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(-604661760) else 0) + ((if 6≤5 then (X Coord.U:Poly)^(5-6)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(69424128) else 0) + (if 7≤5 then (X Coord.U:Poly)^(5-7)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(241864704) else 0)))))
def scaled6Part5Mid : Poly := (((driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(-967458816)) + (driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(214990848))) + ((driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(-3083774976)) + ((driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(-604661760)) + (driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(69424128)))))
def scaled6Part5Upper : Poly := (driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(241864704))

theorem scaled6Part5_clear (h r t : ℂ) (hh : h≠0) :
    h^(5+2)*eval (sourcePoint h r t) moment6Part5 =
      h^2*eval (basePoint h r t) scaled6Part5Low+
      h*eval (basePoint h r t) scaled6Part5Mid+eval (basePoint h r t) scaled6Part5Upper := by
  norm_num [moment6Part5,scaled6Part5Low,scaled6Part5Mid,scaled6Part5Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled6Part6Low : Poly := ((((if 7≤5 then (X Coord.U:Poly)^(5-7)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(-26873856) else 0) + ((if 0≤5 then (X Coord.U:Poly)^(5-0)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(953026560) else 0) + (if 0≤5 then (X Coord.U:Poly)^(5-0)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(112637952) else 0))) + ((if 0≤5 then (X Coord.U:Poly)^(5-0)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(-1990656) else 0) + ((if 0≤5 then (X Coord.U:Poly)^(5-0)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(-10518875136) else 0) + (if 0≤5 then (X Coord.U:Poly)^(5-0)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(833836032) else 0)))) + (((if 0≤5 then (X Coord.U:Poly)^(5-0)*driftSquare^((4+2)/2)*(C (1/3:ℂ)*deficit)^2*(-17418240) else 0) + ((if 0≤5 then (X Coord.U:Poly)^(5-0)*driftSquare^((1+3)/2)*(C (1/3:ℂ)*deficit)^3*(2364152832) else 0) + (if 0≤5 then (X Coord.U:Poly)^(5-0)*driftSquare^((3+3)/2)*(C (1/3:ℂ)*deficit)^3*(-90160128) else 0))) + ((if 0≤5 then (X Coord.U:Poly)^(5-0)*driftSquare^((0+4)/2)*(C (1/3:ℂ)*deficit)^4*(1547486208) else 0) + ((if 0≤5 then (X Coord.U:Poly)^(5-0)*driftSquare^((2+4)/2)*(C (1/3:ℂ)*deficit)^4*(-211756032) else 0) + (if 0≤5 then (X Coord.U:Poly)^(5-0)*driftSquare^((1+5)/2)*(C (1/3:ℂ)*deficit)^5*(-137355264) else 0)))))
def scaled6Part6Mid : Poly := (0:Poly)
def scaled6Part6Upper : Poly := (driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(-26873856))

theorem scaled6Part6_clear (h r t : ℂ) (hh : h≠0) :
    h^(5+2)*eval (sourcePoint h r t) moment6Part6 =
      h^2*eval (basePoint h r t) scaled6Part6Low+
      h*eval (basePoint h r t) scaled6Part6Mid+eval (basePoint h r t) scaled6Part6Upper := by
  norm_num [moment6Part6,scaled6Part6Low,scaled6Part6Mid,scaled6Part6Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled6Part7Low : Poly := (((if 0≤5 then (X Coord.U:Poly)^(5-0)*driftSquare^((0+6)/2)*(C (1/3:ℂ)*deficit)^6*(-35831808) else 0) + (if 0≤5 then (X Coord.U:Poly)^(5-0)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(-167712768) else 0)) + ((if 0≤5 then (X Coord.U:Poly)^(5-0)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(5971968) else 0) + (if 0≤5 then (X Coord.U:Poly)^(5-0)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(0) else 0)))
def scaled6Part7Mid : Poly := (0:Poly)
def scaled6Part7Upper : Poly := (0:Poly)

theorem scaled6Part7_clear (h r t : ℂ) (hh : h≠0) :
    h^(5+2)*eval (sourcePoint h r t) moment6Part7 =
      h^2*eval (basePoint h r t) scaled6Part7Low+
      h*eval (basePoint h r t) scaled6Part7Mid+eval (basePoint h r t) scaled6Part7Upper := by
  norm_num [moment6Part7,scaled6Part7Low,scaled6Part7Mid,scaled6Part7Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def low6 : Poly := (((scaled6Part0Low + scaled6Part1Low) + (scaled6Part2Low + scaled6Part3Low)) + ((scaled6Part4Low + scaled6Part5Low) + (scaled6Part6Low + scaled6Part7Low)))
def mid6 : Poly := (((scaled6Part0Mid + scaled6Part1Mid) + (scaled6Part2Mid + scaled6Part3Mid)) + ((scaled6Part4Mid + scaled6Part5Mid) + (scaled6Part6Mid + scaled6Part7Mid)))
def upper6 : Poly := (((scaled6Part0Upper + scaled6Part1Upper) + (scaled6Part2Upper + scaled6Part3Upper)) + ((scaled6Part4Upper + scaled6Part5Upper) + (scaled6Part6Upper + scaled6Part7Upper)))

def midScaled6 : Poly := ((((-967458816:Poly)*(-X Coord.K*X Coord.U*C ((1/3:ℂ)^1)*(∑ i ∈ Finset.range ((3+1)/2), driftSquare^i*(9:Poly)^(((3+1)/2)-1-i)) - X Coord.J*C (1/3:ℂ)*1*driftSquare^((3+1)/2))) + ((214990848:Poly)*(-X Coord.K*X Coord.U*C ((1/3:ℂ)^1)*(∑ i ∈ Finset.range ((5+1)/2), driftSquare^i*(9:Poly)^(((5+1)/2)-1-i)) - X Coord.J*C (1/3:ℂ)*1*driftSquare^((5+1)/2)))) + (((-3083774976:Poly)*(-X Coord.K*X Coord.U*C ((1/3:ℂ)^0)*(∑ i ∈ Finset.range ((2+0)/2), driftSquare^i*(9:Poly)^(((2+0)/2)-1-i)) - X Coord.J*C (1/3:ℂ)*0*driftSquare^((2+0)/2))) + (((-604661760:Poly)*(-X Coord.K*X Coord.U*C ((1/3:ℂ)^0)*(∑ i ∈ Finset.range ((4+0)/2), driftSquare^i*(9:Poly)^(((4+0)/2)-1-i)) - X Coord.J*C (1/3:ℂ)*0*driftSquare^((4+0)/2))) + ((69424128:Poly)*(-X Coord.K*X Coord.U*C ((1/3:ℂ)^0)*(∑ i ∈ Finset.range ((6+0)/2), driftSquare^i*(9:Poly)^(((6+0)/2)-1-i)) - X Coord.J*C (1/3:ℂ)*0*driftSquare^((6+0)/2))))))
def upperScaled6 : Poly := (26873856:Poly)*X Coord.K*driftSquare^2
def scaledMoment6 : Poly := low6+midScaled6+upperScaled6

theorem mid6_scaled : mid6=X Coord.U*midScaled6 := by
  apply MvPolynomial.funext
  intro v
  norm_num [mid6,midScaled6,scaled6Part0Mid,scaled6Part1Mid,scaled6Part2Mid,scaled6Part3Mid,scaled6Part4Mid,scaled6Part5Mid,scaled6Part6Mid,scaled6Part7Mid,driftSquare,deficit,Finset.sum_range_succ] <;> ring

theorem upper6_scaled : upper6=(X Coord.U)^2*upperScaled6 := by
  apply MvPolynomial.funext
  intro v
  norm_num [upper6,upperScaled6,scaled6Part0Upper,scaled6Part1Upper,scaled6Part2Upper,scaled6Part3Upper,scaled6Part4Upper,scaled6Part5Upper,scaled6Part6Upper,scaled6Part7Upper,driftSquare,deficit] <;> ring

theorem scaledMoment6_eq (h r t : ℂ) (hh : h≠0) :
    h^5*eval (sourcePoint h r t) moment6=eval (basePoint h r t) scaledMoment6 := by
  have he : h^(5+2)*eval (sourcePoint h r t) moment6=
      h^2*eval (basePoint h r t) low6+h*eval (basePoint h r t) mid6+
        eval (basePoint h r t) upper6 := by
    simp only [moment6,low6,mid6,upper6,map_add,mul_add]
    rw [scaled6Part0_clear h r t hh,scaled6Part1_clear h r t hh,scaled6Part2_clear h r t hh,scaled6Part3_clear h r t hh,scaled6Part4_clear h r t hh,scaled6Part5_clear h r t hh,scaled6Part6_clear h r t hh,scaled6Part7_clear h r t hh]
    ring
  rw [mid6_scaled,upper6_scaled] at he
  apply mul_left_cancel₀ (pow_ne_zero 2 hh)
  calc h^2*(h^5*eval (sourcePoint h r t) moment6)=
        h^(5+2)*eval (sourcePoint h r t) moment6 := by ring
       _ = h^2*eval (basePoint h r t) scaledMoment6 := by
         rw [he]
         simp only [scaledMoment6,map_add,map_mul,map_pow,eval_X,basePoint]
         ring

theorem scaledMoment6_zero (r t : ℂ) :
    eval (basePoint 0 r t) scaledMoment6=(6:ℂ)^8*(-207360+1296*(r-12*t)) := by
  norm_num [scaledMoment6,low6,midScaled6,upperScaled6,scaled6Part0Low,scaled6Part1Low,scaled6Part2Low,scaled6Part3Low,scaled6Part4Low,scaled6Part5Low,scaled6Part6Low,scaled6Part7Low,basePoint,driftSquare,deficit,Finset.sum_range_succ] <;> ring

end
end HTGeometry.ThetaRatioInfinity
