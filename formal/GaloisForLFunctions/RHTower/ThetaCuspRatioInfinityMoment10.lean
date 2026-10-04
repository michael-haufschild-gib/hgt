import GaloisForLFunctions.RHTower.ThetaCuspRatioInfinityFlow
/-! # Exact source-flow compactification and the third-slope expanding mode. -/

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def scaled10Part0Low : Poly := ((((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(-312165555505201152) else 0) + ((if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(-2936102282906370048) else 0) + (if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(1818995586674982912) else 0))) + ((if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(-56594005935390720) else 0) + ((if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(1534590913609728) else 0) + (if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((7+1)/2)*(C (1/3:ℂ)*deficit)^1*(-43083242274816) else 0)))) + (((if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((9+1)/2)*(C (1/3:ℂ)*deficit)^1*(266524950528) else 0) + ((if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(-367565196123832320) else 0) + (if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(-460966580336590848) else 0))) + ((if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((4+2)/2)*(C (1/3:ℂ)*deficit)^2*(24334188461752320) else 0) + ((if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((6+2)/2)*(C (1/3:ℂ)*deficit)^2*(-708382995775488) else 0) + (if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((8+2)/2)*(C (1/3:ℂ)*deficit)^2*(4615386365952) else 0)))))
def scaled10Part0Mid : Poly := (0:Poly)
def scaled10Part0Upper : Poly := (0:Poly)

theorem scaled10Part0_clear (h r t : ℂ) (hh : h≠0) :
    h^(9+2)*eval (sourcePoint h r t) moment10Part0 =
      h^2*eval (basePoint h r t) scaled10Part0Low+
      h*eval (basePoint h r t) scaled10Part0Mid+eval (basePoint h r t) scaled10Part0Upper := by
  norm_num [moment10Part0,scaled10Part0Low,scaled10Part0Mid,scaled10Part0Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled10Part1Low : Poly := ((((if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((1+3)/2)*(C (1/3:ℂ)*deficit)^3*(260607039842746368) else 0) + ((if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((3+3)/2)*(C (1/3:ℂ)*deficit)^3*(60342327082156032) else 0) + (if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((5+3)/2)*(C (1/3:ℂ)*deficit)^3*(-4217261764313088) else 0))) + ((if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((7+3)/2)*(C (1/3:ℂ)*deficit)^3*(74382549516288) else 0) + ((if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((0+4)/2)*(C (1/3:ℂ)*deficit)^4*(207945326055112704) else 0) + (if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((2+4)/2)*(C (1/3:ℂ)*deficit)^4*(-57642006020308992) else 0)))) + (((if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((4+4)/2)*(C (1/3:ℂ)*deficit)^4*(-5306918690930688) else 0) + ((if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((6+4)/2)*(C (1/3:ℂ)*deficit)^4*(266907136573440) else 0) + (if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((1+5)/2)*(C (1/3:ℂ)*deficit)^5*(-54580396493242368) else 0))) + ((if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((3+5)/2)*(C (1/3:ℂ)*deficit)^5*(3929776432349184) else 0) + ((if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((5+5)/2)*(C (1/3:ℂ)*deficit)^5*(281445092425728) else 0) + (if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((0+6)/2)*(C (1/3:ℂ)*deficit)^6*(-17956085932818432) else 0)))))
def scaled10Part1Mid : Poly := (0:Poly)
def scaled10Part1Upper : Poly := (0:Poly)

theorem scaled10Part1_clear (h r t : ℂ) (hh : h≠0) :
    h^(9+2)*eval (sourcePoint h r t) moment10Part1 =
      h^2*eval (basePoint h r t) scaled10Part1Low+
      h*eval (basePoint h r t) scaled10Part1Mid+eval (basePoint h r t) scaled10Part1Upper := by
  norm_num [moment10Part1,scaled10Part1Low,scaled10Part1Mid,scaled10Part1Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled10Part2Low : Poly := ((((if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((2+6)/2)*(C (1/3:ℂ)*deficit)^6*(4715990223814656) else 0) + ((if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((4+6)/2)*(C (1/3:ℂ)*deficit)^6*(12592873930752) else 0) + (if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((1+7)/2)*(C (1/3:ℂ)*deficit)^7*(2225170756141056) else 0))) + ((if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((3+7)/2)*(C (1/3:ℂ)*deficit)^7*(-94841922650112) else 0) + ((if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((0+8)/2)*(C (1/3:ℂ)*deficit)^8*(386039286595584) else 0) + (if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((2+8)/2)*(C (1/3:ℂ)*deficit)^8*(-73851936178176) else 0)))) + (((if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((1+9)/2)*(C (1/3:ℂ)*deficit)^9*(-21175738564608) else 0) + ((if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((0+10)/2)*(C (1/3:ℂ)*deficit)^10*(-2229025112064) else 0) + (if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(61684770355347456) else 0))) + ((if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(-197242493534208) else 0) + ((if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(80341172158464) else 0) + (if 1≤9 then (X Coord.U:Poly)^(9-1)*driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(-762883080192) else 0)))))
def scaled10Part2Mid : Poly := (0:Poly)
def scaled10Part2Upper : Poly := (0:Poly)

theorem scaled10Part2_clear (h r t : ℂ) (hh : h≠0) :
    h^(9+2)*eval (sourcePoint h r t) moment10Part2 =
      h^2*eval (basePoint h r t) scaled10Part2Low+
      h*eval (basePoint h r t) scaled10Part2Mid+eval (basePoint h r t) scaled10Part2Upper := by
  norm_num [moment10Part2,scaled10Part2Low,scaled10Part2Mid,scaled10Part2Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled10Part3Low : Poly := ((((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(-9455534033560731648) else 0) + ((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(6034557931751079936) else 0) + (if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(77107829817212928) else 0))) + ((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(-7239659433099264) else 0) + ((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((7+1)/2)*(C (1/3:ℂ)*deficit)^1*(247320885067776) else 0) + (if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((9+1)/2)*(C (1/3:ℂ)*deficit)^1*(-3329120010240) else 0)))) + (((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(283490304519241728) else 0) + ((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(-1830188307339214848) else 0) + (if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((4+2)/2)*(C (1/3:ℂ)*deficit)^2*(25356104889532416) else 0))) + ((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((6+2)/2)*(C (1/3:ℂ)*deficit)^2*(1132149688565760) else 0) + ((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((8+2)/2)*(C (1/3:ℂ)*deficit)^2*(-27635385434112) else 0) + (if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((1+3)/2)*(C (1/3:ℂ)*deficit)^3*(-183915869383655424) else 0)))))
def scaled10Part3Mid : Poly := (0:Poly)
def scaled10Part3Upper : Poly := (0:Poly)

theorem scaled10Part3_clear (h r t : ℂ) (hh : h≠0) :
    h^(9+2)*eval (sourcePoint h r t) moment10Part3 =
      h^2*eval (basePoint h r t) scaled10Part3Low+
      h*eval (basePoint h r t) scaled10Part3Mid+eval (basePoint h r t) scaled10Part3Upper := by
  norm_num [moment10Part3,scaled10Part3Low,scaled10Part3Mid,scaled10Part3Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled10Part4Low : Poly := ((((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((3+3)/2)*(C (1/3:ℂ)*deficit)^3*(299556403542392832) else 0) + ((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((5+3)/2)*(C (1/3:ℂ)*deficit)^3*(-5141271574904832) else 0) + (if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((7+3)/2)*(C (1/3:ℂ)*deficit)^3*(-100206207074304) else 0))) + ((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((0+4)/2)*(C (1/3:ℂ)*deficit)^4*(29860612486004736) else 0) + ((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((2+4)/2)*(C (1/3:ℂ)*deficit)^4*(145249023007457280) else 0) + (if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((4+4)/2)*(C (1/3:ℂ)*deficit)^4*(-30422992425910272) else 0)))) + (((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((6+4)/2)*(C (1/3:ℂ)*deficit)^4*(244872425963520) else 0) + ((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((1+5)/2)*(C (1/3:ℂ)*deficit)^5*(32470139150401536) else 0) + (if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((3+5)/2)*(C (1/3:ℂ)*deficit)^5*(-20769282027159552) else 0))) + ((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((5+5)/2)*(C (1/3:ℂ)*deficit)^5*(1027096417271808) else 0) + ((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((0+6)/2)*(C (1/3:ℂ)*deficit)^6*(-8705631717752832) else 0) + (if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((2+6)/2)*(C (1/3:ℂ)*deficit)^6*(-10727531636981760) else 0)))))
def scaled10Part4Mid : Poly := (0:Poly)
def scaled10Part4Upper : Poly := (0:Poly)

theorem scaled10Part4_clear (h r t : ℂ) (hh : h≠0) :
    h^(9+2)*eval (sourcePoint h r t) moment10Part4 =
      h^2*eval (basePoint h r t) scaled10Part4Low+
      h*eval (basePoint h r t) scaled10Part4Mid+eval (basePoint h r t) scaled10Part4Upper := by
  norm_num [moment10Part4,scaled10Part4Low,scaled10Part4Mid,scaled10Part4Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled10Part5Low : Poly := ((((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((4+6)/2)*(C (1/3:ℂ)*deficit)^6*(1085108257751040) else 0) + ((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((1+7)/2)*(C (1/3:ℂ)*deficit)^7*(-1743654893912064) else 0) + (if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((3+7)/2)*(C (1/3:ℂ)*deficit)^7*(661215532548096) else 0))) + ((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((0+8)/2)*(C (1/3:ℂ)*deficit)^8*(91947285872640) else 0) + ((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((2+8)/2)*(C (1/3:ℂ)*deficit)^8*(185194836393984) else 0) + (if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((1+9)/2)*(C (1/3:ℂ)*deficit)^9*(20061226008576) else 0)))) + (((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(-412258829129220096) else 0) + ((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(19009199682551808) else 0) + (if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(-403853428260864) else 0))) + ((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(7818213851136) else 0) + ((if 2≤9 then (X Coord.U:Poly)^(9-2)*driftSquare^((10+0)/2)*(C (1/3:ℂ)*deficit)^0*(6115295232) else 0) + (if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(-13150464920064589824) else 0)))))
def scaled10Part5Mid : Poly := (0:Poly)
def scaled10Part5Upper : Poly := (0:Poly)

theorem scaled10Part5_clear (h r t : ℂ) (hh : h≠0) :
    h^(9+2)*eval (sourcePoint h r t) moment10Part5 =
      h^2*eval (basePoint h r t) scaled10Part5Low+
      h*eval (basePoint h r t) scaled10Part5Mid+eval (basePoint h r t) scaled10Part5Upper := by
  norm_num [moment10Part5,scaled10Part5Low,scaled10Part5Mid,scaled10Part5Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled10Part6Low : Poly := ((((if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(7490578609634623488) else 0) + ((if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(1074125894882033664) else 0) + (if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(-15869968032301056) else 0))) + ((if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((7+1)/2)*(C (1/3:ℂ)*deficit)^1*(-691019570479104) else 0) + ((if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((9+1)/2)*(C (1/3:ℂ)*deficit)^1*(19221849980928) else 0) + (if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(93245636404076544) else 0)))) + (((if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(-1594312423014629376) else 0) + ((if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((4+2)/2)*(C (1/3:ℂ)*deficit)^2*(-240029402699907072) else 0) + (if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((6+2)/2)*(C (1/3:ℂ)*deficit)^2*(4743924629667840) else 0))) + ((if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((8+2)/2)*(C (1/3:ℂ)*deficit)^2*(67437439377408) else 0) + ((if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((1+3)/2)*(C (1/3:ℂ)*deficit)^3*(79758889488580608) else 0) + (if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((3+3)/2)*(C (1/3:ℂ)*deficit)^3*(6742504921595904) else 0)))))
def scaled10Part6Mid : Poly := (0:Poly)
def scaled10Part6Upper : Poly := (0:Poly)

theorem scaled10Part6_clear (h r t : ℂ) (hh : h≠0) :
    h^(9+2)*eval (sourcePoint h r t) moment10Part6 =
      h^2*eval (basePoint h r t) scaled10Part6Low+
      h*eval (basePoint h r t) scaled10Part6Mid+eval (basePoint h r t) scaled10Part6Upper := by
  norm_num [moment10Part6,scaled10Part6Low,scaled10Part6Mid,scaled10Part6Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled10Part7Low : Poly := ((((if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((5+3)/2)*(C (1/3:ℂ)*deficit)^3*(35264505271320576) else 0) + ((if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((7+3)/2)*(C (1/3:ℂ)*deficit)^3*(-339866777124864) else 0) + (if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((0+4)/2)*(C (1/3:ℂ)*deficit)^4*(-162275805732519936) else 0))) + ((if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((2+4)/2)*(C (1/3:ℂ)*deficit)^4*(37155767614193664) else 0) + ((if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((4+4)/2)*(C (1/3:ℂ)*deficit)^4*(20442577957208064) else 0) + (if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((6+4)/2)*(C (1/3:ℂ)*deficit)^4*(-1788924764307456) else 0)))) + (((if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((1+5)/2)*(C (1/3:ℂ)*deficit)^5*(21372728658886656) else 0) + ((if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((3+5)/2)*(C (1/3:ℂ)*deficit)^5*(21837248204636160) else 0) + (if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((5+5)/2)*(C (1/3:ℂ)*deficit)^5*(-2644485466226688) else 0))) + ((if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((0+6)/2)*(C (1/3:ℂ)*deficit)^6*(-2526460650455040) else 0) + ((if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((2+6)/2)*(C (1/3:ℂ)*deficit)^6*(3281403593097216) else 0) + (if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((4+6)/2)*(C (1/3:ℂ)*deficit)^6*(-1958740337885184) else 0)))))
def scaled10Part7Mid : Poly := (0:Poly)
def scaled10Part7Upper : Poly := (0:Poly)

theorem scaled10Part7_clear (h r t : ℂ) (hh : h≠0) :
    h^(9+2)*eval (sourcePoint h r t) moment10Part7 =
      h^2*eval (basePoint h r t) scaled10Part7Low+
      h*eval (basePoint h r t) scaled10Part7Mid+eval (basePoint h r t) scaled10Part7Upper := by
  norm_num [moment10Part7,scaled10Part7Low,scaled10Part7Mid,scaled10Part7Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled10Part8Low : Poly := ((((if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((1+7)/2)*(C (1/3:ℂ)*deficit)^7*(-573416710078464) else 0) + ((if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((3+7)/2)*(C (1/3:ℂ)*deficit)^7*(-648089051332608) else 0) + (if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((0+8)/2)*(C (1/3:ℂ)*deficit)^8*(5015306502144) else 0))) + ((if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((2+8)/2)*(C (1/3:ℂ)*deficit)^8*(-80802160312320) else 0) + ((if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(-2447771852650954752) else 0) + (if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(20716788679262208) else 0)))) + (((if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(1256456716075008) else 0) + ((if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(-27614129209344) else 0) + (if 3≤9 then (X Coord.U:Poly)^(9-3)*driftSquare^((10+0)/2)*(C (1/3:ℂ)*deficit)^0*(-209066655744) else 0))) + ((if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(-8554127497378209792) else 0) + ((if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(4188357258535084032) else 0) + (if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(1578703866224246784) else 0)))))
def scaled10Part8Mid : Poly := (0:Poly)
def scaled10Part8Upper : Poly := (0:Poly)

theorem scaled10Part8_clear (h r t : ℂ) (hh : h≠0) :
    h^(9+2)*eval (sourcePoint h r t) moment10Part8 =
      h^2*eval (basePoint h r t) scaled10Part8Low+
      h*eval (basePoint h r t) scaled10Part8Mid+eval (basePoint h r t) scaled10Part8Upper := by
  norm_num [moment10Part8,scaled10Part8Low,scaled10Part8Mid,scaled10Part8Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled10Part9Low : Poly := ((((if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(54261410809724928) else 0) + ((if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((7+1)/2)*(C (1/3:ℂ)*deficit)^1*(-266793322807296) else 0) + (if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((9+1)/2)*(C (1/3:ℂ)*deficit)^1*(-44450211815424) else 0))) + ((if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(-518080260483588096) else 0) + ((if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(-801251635915653120) else 0) + (if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((4+2)/2)*(C (1/3:ℂ)*deficit)^2*(-151499636071022592) else 0)))) + (((if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((6+2)/2)*(C (1/3:ℂ)*deficit)^2*(-14721930448404480) else 0) + ((if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((8+2)/2)*(C (1/3:ℂ)*deficit)^2*(-7410716614656) else 0) + (if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((1+3)/2)*(C (1/3:ℂ)*deficit)^3*(468204878877622272) else 0))) + ((if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((3+3)/2)*(C (1/3:ℂ)*deficit)^3*(-66591881423290368) else 0) + ((if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((5+3)/2)*(C (1/3:ℂ)*deficit)^3*(-4292773429837824) else 0) + (if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((7+3)/2)*(C (1/3:ℂ)*deficit)^3*(1325204017053696) else 0)))))
def scaled10Part9Mid : Poly := (0:Poly)
def scaled10Part9Upper : Poly := (0:Poly)

theorem scaled10Part9_clear (h r t : ℂ) (hh : h≠0) :
    h^(9+2)*eval (sourcePoint h r t) moment10Part9 =
      h^2*eval (basePoint h r t) scaled10Part9Low+
      h*eval (basePoint h r t) scaled10Part9Mid+eval (basePoint h r t) scaled10Part9Upper := by
  norm_num [moment10Part9,scaled10Part9Low,scaled10Part9Mid,scaled10Part9Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled10Part10Low : Poly := ((((if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((0+4)/2)*(C (1/3:ℂ)*deficit)^4*(-158036696275746816) else 0) + ((if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((2+4)/2)*(C (1/3:ℂ)*deficit)^4*(49152197917605888) else 0) + (if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((4+4)/2)*(C (1/3:ℂ)*deficit)^4*(-34257886947311616) else 0))) + ((if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((6+4)/2)*(C (1/3:ℂ)*deficit)^4*(3518770258575360) else 0) + ((if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((1+5)/2)*(C (1/3:ℂ)*deficit)^5*(10641226570924032) else 0) + (if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((3+5)/2)*(C (1/3:ℂ)*deficit)^5*(-3685971650936832) else 0)))) + (((if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((5+5)/2)*(C (1/3:ℂ)*deficit)^5*(3117090387787776) else 0) + ((if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((0+6)/2)*(C (1/3:ℂ)*deficit)^6*(-229450272473088) else 0) + (if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((2+6)/2)*(C (1/3:ℂ)*deficit)^6*(1490381915553792) else 0))) + ((if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((4+6)/2)*(C (1/3:ℂ)*deficit)^6*(1283129018155008) else 0) + ((if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((1+7)/2)*(C (1/3:ℂ)*deficit)^7*(-40122452017152) else 0) + (if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((3+7)/2)*(C (1/3:ℂ)*deficit)^7*(191696159637504) else 0)))))
def scaled10Part10Mid : Poly := (0:Poly)
def scaled10Part10Upper : Poly := (0:Poly)

theorem scaled10Part10_clear (h r t : ℂ) (hh : h≠0) :
    h^(9+2)*eval (sourcePoint h r t) moment10Part10 =
      h^2*eval (basePoint h r t) scaled10Part10Low+
      h*eval (basePoint h r t) scaled10Part10Mid+eval (basePoint h r t) scaled10Part10Upper := by
  norm_num [moment10Part10,scaled10Part10Low,scaled10Part10Mid,scaled10Part10Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled10Part11Low : Poly := ((((if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(-3961660559120695296) else 0) + ((if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(-173128209213800448) else 0) + (if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(5898464181780480) else 0))) + ((if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(-87926724108288) else 0) + ((if 4≤9 then (X Coord.U:Poly)^(9-4)*driftSquare^((10+0)/2)*(C (1/3:ℂ)*deficit)^0*(2911629017088) else 0) + (if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(677116232091085824) else 0)))) + (((if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(632117280995205120) else 0) + ((if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(1344442243046768640) else 0) + (if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(1706936929468416) else 0))) + ((if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((7+1)/2)*(C (1/3:ℂ)*deficit)^1*(7781627281932288) else 0) + ((if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((9+1)/2)*(C (1/3:ℂ)*deficit)^1*(-69760642424832) else 0) + (if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(-1228382486731505664) else 0)))))
def scaled10Part11Mid : Poly := (0:Poly)
def scaled10Part11Upper : Poly := (0:Poly)

theorem scaled10Part11_clear (h r t : ℂ) (hh : h≠0) :
    h^(9+2)*eval (sourcePoint h r t) moment10Part11 =
      h^2*eval (basePoint h r t) scaled10Part11Low+
      h*eval (basePoint h r t) scaled10Part11Mid+eval (basePoint h r t) scaled10Part11Upper := by
  norm_num [moment10Part11,scaled10Part11Low,scaled10Part11Mid,scaled10Part11Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled10Part12Low : Poly := ((((if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(-54432845479378944) else 0) + ((if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((4+2)/2)*(C (1/3:ℂ)*deficit)^2*(-113036754199707648) else 0) + (if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((6+2)/2)*(C (1/3:ℂ)*deficit)^2*(8431935683788800) else 0))) + ((if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((8+2)/2)*(C (1/3:ℂ)*deficit)^2*(-896245999976448) else 0) + ((if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((1+3)/2)*(C (1/3:ℂ)*deficit)^3*(633002521774915584) else 0) + (if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((3+3)/2)*(C (1/3:ℂ)*deficit)^3*(-236508689461542912) else 0)))) + (((if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((5+3)/2)*(C (1/3:ℂ)*deficit)^3*(48716063613517824) else 0) + ((if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((7+3)/2)*(C (1/3:ℂ)*deficit)^3*(-3315615516721152) else 0) + (if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((0+4)/2)*(C (1/3:ℂ)*deficit)^4*(32705127157137408) else 0))) + ((if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((2+4)/2)*(C (1/3:ℂ)*deficit)^4*(-26210932150173696) else 0) + ((if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((4+4)/2)*(C (1/3:ℂ)*deficit)^4*(4425276589277184) else 0) + (if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((6+4)/2)*(C (1/3:ℂ)*deficit)^4*(-3051879793754112) else 0)))))
def scaled10Part12Mid : Poly := (0:Poly)
def scaled10Part12Upper : Poly := (0:Poly)

theorem scaled10Part12_clear (h r t : ℂ) (hh : h≠0) :
    h^(9+2)*eval (sourcePoint h r t) moment10Part12 =
      h^2*eval (basePoint h r t) scaled10Part12Low+
      h*eval (basePoint h r t) scaled10Part12Mid+eval (basePoint h r t) scaled10Part12Upper := by
  norm_num [moment10Part12,scaled10Part12Low,scaled10Part12Mid,scaled10Part12Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled10Part13Low : Poly := ((((if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((1+5)/2)*(C (1/3:ℂ)*deficit)^5*(1376701634838528) else 0) + ((if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((3+5)/2)*(C (1/3:ℂ)*deficit)^5*(-2049588590542848) else 0) + (if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((5+5)/2)*(C (1/3:ℂ)*deficit)^5*(-1604433700454400) else 0))) + ((if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((2+6)/2)*(C (1/3:ℂ)*deficit)^6*(140428582060032) else 0) + ((if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((4+6)/2)*(C (1/3:ℂ)*deficit)^6*(-296460339904512) else 0) + (if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(-4382336574963588096) else 0)))) + (((if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(-28115931239221248) else 0) + ((if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(-30272545686878208) else 0) + (if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(1220349372668928) else 0))) + ((if 5≤9 then (X Coord.U:Poly)^(9-5)*driftSquare^((10+0)/2)*(C (1/3:ℂ)*deficit)^0*(-21649604520960) else 0) + ((if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(328311602422530048) else 0) + (if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(2303805099558223872) else 0)))))
def scaled10Part13Mid : Poly := (0:Poly)
def scaled10Part13Upper : Poly := (0:Poly)

theorem scaled10Part13_clear (h r t : ℂ) (hh : h≠0) :
    h^(9+2)*eval (sourcePoint h r t) moment10Part13 =
      h^2*eval (basePoint h r t) scaled10Part13Low+
      h*eval (basePoint h r t) scaled10Part13Mid+eval (basePoint h r t) scaled10Part13Upper := by
  norm_num [moment10Part13,scaled10Part13Low,scaled10Part13Mid,scaled10Part13Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled10Part14Low : Poly := ((((if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(-578663556564123648) else 0) + ((if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(211281541027430400) else 0) + (if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((7+1)/2)*(C (1/3:ℂ)*deficit)^1*(-15769153018920960) else 0))) + ((if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((9+1)/2)*(C (1/3:ℂ)*deficit)^1*(658392165236736) else 0) + ((if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(53484012180504576) else 0) + (if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(-974558059750490112) else 0)))) + (((if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((4+2)/2)*(C (1/3:ℂ)*deficit)^2*(335431848736456704) else 0) + ((if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((6+2)/2)*(C (1/3:ℂ)*deficit)^2*(-48404603792130048) else 0) + (if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((8+2)/2)*(C (1/3:ℂ)*deficit)^2*(2351529262153728) else 0))) + ((if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((1+3)/2)*(C (1/3:ℂ)*deficit)^3*(-130820508628549632) else 0) + ((if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((3+3)/2)*(C (1/3:ℂ)*deficit)^3*(48960675900555264) else 0) + (if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((5+3)/2)*(C (1/3:ℂ)*deficit)^3*(-7059740472115200) else 0)))))
def scaled10Part14Mid : Poly := (0:Poly)
def scaled10Part14Upper : Poly := (0:Poly)

theorem scaled10Part14_clear (h r t : ℂ) (hh : h≠0) :
    h^(9+2)*eval (sourcePoint h r t) moment10Part14 =
      h^2*eval (basePoint h r t) scaled10Part14Low+
      h*eval (basePoint h r t) scaled10Part14Mid+eval (basePoint h r t) scaled10Part14Upper := by
  norm_num [moment10Part14,scaled10Part14Low,scaled10Part14Mid,scaled10Part14Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled10Part15Low : Poly := ((((if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((7+3)/2)*(C (1/3:ℂ)*deficit)^3*(1984745630859264) else 0) + ((if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((2+4)/2)*(C (1/3:ℂ)*deficit)^4*(-3441754087096320) else 0) + (if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((4+4)/2)*(C (1/3:ℂ)*deficit)^4*(1525489061068800) else 0))) + ((if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((6+4)/2)*(C (1/3:ℂ)*deficit)^4*(1318886295994368) else 0) + ((if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((3+5)/2)*(C (1/3:ℂ)*deficit)^5*(-280857164120064) else 0) + (if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((5+5)/2)*(C (1/3:ℂ)*deficit)^5*(312063515688960) else 0)))) + (((if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(-294241410708922368) else 0) + ((if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(-613251565613383680) else 0) + (if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(53149080840781824) else 0))) + ((if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(-4460464678846464) else 0) + ((if 6≤9 then (X Coord.U:Poly)^(9-6)*driftSquare^((10+0)/2)*(C (1/3:ℂ)*deficit)^0*(91471564873728) else 0) + (if 7≤9 then (X Coord.U:Poly)^(9-7)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(383949003059269632) else 0)))))
def scaled10Part15Mid : Poly := (0:Poly)
def scaled10Part15Upper : Poly := (0:Poly)

theorem scaled10Part15_clear (h r t : ℂ) (hh : h≠0) :
    h^(9+2)*eval (sourcePoint h r t) moment10Part15 =
      h^2*eval (basePoint h r t) scaled10Part15Low+
      h*eval (basePoint h r t) scaled10Part15Mid+eval (basePoint h r t) scaled10Part15Upper := by
  norm_num [moment10Part15,scaled10Part15Low,scaled10Part15Mid,scaled10Part15Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled10Part16Low : Poly := ((((if 7≤9 then (X Coord.U:Poly)^(9-7)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(-106968024361009152) else 0) + ((if 7≤9 then (X Coord.U:Poly)^(9-7)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(682255339279220736) else 0) + (if 7≤9 then (X Coord.U:Poly)^(9-7)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(-212576273746624512) else 0))) + ((if 7≤9 then (X Coord.U:Poly)^(9-7)*driftSquare^((7+1)/2)*(C (1/3:ℂ)*deficit)^1*(26346124845121536) else 0) + ((if 7≤9 then (X Coord.U:Poly)^(9-7)*driftSquare^((9+1)/2)*(C (1/3:ℂ)*deficit)^1*(-1070124255608832) else 0) + (if 7≤9 then (X Coord.U:Poly)^(9-7)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(196230762942824448) else 0)))) + (((if 7≤9 then (X Coord.U:Poly)^(9-7)*driftSquare^((4+2)/2)*(C (1/3:ℂ)*deficit)^2*(-58131790753038336) else 0) + ((if 7≤9 then (X Coord.U:Poly)^(9-7)*driftSquare^((6+2)/2)*(C (1/3:ℂ)*deficit)^2*(8073877241069568) else 0) + (if 7≤9 then (X Coord.U:Poly)^(9-7)*driftSquare^((8+2)/2)*(C (1/3:ℂ)*deficit)^2*(-916075143364608) else 0))) + ((if 7≤9 then (X Coord.U:Poly)^(9-7)*driftSquare^((3+3)/2)*(C (1/3:ℂ)*deficit)^3*(4589005449461760) else 0) + ((if 7≤9 then (X Coord.U:Poly)^(9-7)*driftSquare^((5+3)/2)*(C (1/3:ℂ)*deficit)^3*(-493171806044160) else 0) + (if 7≤9 then (X Coord.U:Poly)^(9-7)*driftSquare^((7+3)/2)*(C (1/3:ℂ)*deficit)^3*(-713659540045824) else 0)))))
def scaled10Part16Mid : Poly := (0:Poly)
def scaled10Part16Upper : Poly := (0:Poly)

theorem scaled10Part16_clear (h r t : ℂ) (hh : h≠0) :
    h^(9+2)*eval (sourcePoint h r t) moment10Part16 =
      h^2*eval (basePoint h r t) scaled10Part16Low+
      h*eval (basePoint h r t) scaled10Part16Mid+eval (basePoint h r t) scaled10Part16Upper := by
  norm_num [moment10Part16,scaled10Part16Low,scaled10Part16Mid,scaled10Part16Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled10Part17Low : Poly := ((((if 7≤9 then (X Coord.U:Poly)^(9-7)*driftSquare^((4+4)/2)*(C (1/3:ℂ)*deficit)^4*(351071455150080) else 0) + ((if 7≤9 then (X Coord.U:Poly)^(9-7)*driftSquare^((6+4)/2)*(C (1/3:ℂ)*deficit)^4*(-226246048874496) else 0) + (if 7≤9 then (X Coord.U:Poly)^(9-7)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(-1288727614526312448) else 0))) + ((if 7≤9 then (X Coord.U:Poly)^(9-7)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(374568440387198976) else 0) + ((if 7≤9 then (X Coord.U:Poly)^(9-7)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(-88589516401631232) else 0) + (if 7≤9 then (X Coord.U:Poly)^(9-7)*driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(6618583363719168) else 0)))) + (((if 7≤9 then (X Coord.U:Poly)^(9-7)*driftSquare^((10+0)/2)*(C (1/3:ℂ)*deficit)^0*(-213164635115520) else 0) + ((if 8≤9 then (X Coord.U:Poly)^(9-8)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(-130820508628549632) else 0) + (if 8≤9 then (X Coord.U:Poly)^(9-8)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(36177913453215744) else 0))) + ((if 8≤9 then (X Coord.U:Poly)^(9-8)*driftSquare^((7+1)/2)*(C (1/3:ℂ)*deficit)^1*(-4810932762181632) else 0) + ((if 8≤9 then (X Coord.U:Poly)^(9-8)*driftSquare^((9+1)/2)*(C (1/3:ℂ)*deficit)^1*(298317860831232) else 0) + (if 8≤9 then (X Coord.U:Poly)^(9-8)*driftSquare^((4+2)/2)*(C (1/3:ℂ)*deficit)^2*(-3441754087096320) else 0)))))
def scaled10Part17Mid : Poly := (0:Poly)
def scaled10Part17Upper : Poly := (0:Poly)

theorem scaled10Part17_clear (h r t : ℂ) (hh : h≠0) :
    h^(9+2)*eval (sourcePoint h r t) moment10Part17 =
      h^2*eval (basePoint h r t) scaled10Part17Low+
      h*eval (basePoint h r t) scaled10Part17Mid+eval (basePoint h r t) scaled10Part17Upper := by
  norm_num [moment10Part17,scaled10Part17Low,scaled10Part17Mid,scaled10Part17Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled10Part18Low : Poly := ((((if 8≤9 then (X Coord.U:Poly)^(9-8)*driftSquare^((6+2)/2)*(C (1/3:ℂ)*deficit)^2*(-66034868944896) else 0) + ((if 8≤9 then (X Coord.U:Poly)^(9-8)*driftSquare^((8+2)/2)*(C (1/3:ℂ)*deficit)^2*(245239200350208) else 0) + (if 8≤9 then (X Coord.U:Poly)^(9-8)*driftSquare^((5+3)/2)*(C (1/3:ℂ)*deficit)^3*(-280857164120064) else 0))) + ((if 8≤9 then (X Coord.U:Poly)^(9-8)*driftSquare^((7+3)/2)*(C (1/3:ℂ)*deficit)^3*(111451255603200) else 0) + ((if 8≤9 then (X Coord.U:Poly)^(9-8)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(53484012180504576) else 0) + (if 8≤9 then (X Coord.U:Poly)^(9-8)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(-182663105027899392) else 0)))) + (((if 8≤9 then (X Coord.U:Poly)^(9-8)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(51833819612971008) else 0) + ((if 8≤9 then (X Coord.U:Poly)^(9-8)*driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(-5853234192187392) else 0) + (if 8≤9 then (X Coord.U:Poly)^(9-8)*driftSquare^((10+0)/2)*(C (1/3:ℂ)*deficit)^0*(217846571433984) else 0))) + ((if 9≤9 then (X Coord.U:Poly)^(9-9)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(1376701634838528) else 0) + ((if 9≤9 then (X Coord.U:Poly)^(9-9)*driftSquare^((7+1)/2)*(C (1/3:ℂ)*deficit)^1*(93619054706688) else 0) + (if 9≤9 then (X Coord.U:Poly)^(9-9)*driftSquare^((9+1)/2)*(C (1/3:ℂ)*deficit)^1*(-48574172233728) else 0)))))
def scaled10Part18Mid : Poly := (0:Poly)
def scaled10Part18Upper : Poly := (0:Poly)

theorem scaled10Part18_clear (h r t : ℂ) (hh : h≠0) :
    h^(9+2)*eval (sourcePoint h r t) moment10Part18 =
      h^2*eval (basePoint h r t) scaled10Part18Low+
      h*eval (basePoint h r t) scaled10Part18Mid+eval (basePoint h r t) scaled10Part18Upper := by
  norm_num [moment10Part18,scaled10Part18Low,scaled10Part18Mid,scaled10Part18Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled10Part19Low : Poly := ((((if 9≤9 then (X Coord.U:Poly)^(9-9)*driftSquare^((6+2)/2)*(C (1/3:ℂ)*deficit)^2*(140428582060032) else 0) + ((if 9≤9 then (X Coord.U:Poly)^(9-9)*driftSquare^((8+2)/2)*(C (1/3:ℂ)*deficit)^2*(-35664401793024) else 0) + (if 9≤9 then (X Coord.U:Poly)^(9-9)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(32705127157137408) else 0))) + ((if 9≤9 then (X Coord.U:Poly)^(9-9)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(-8910632371027968) else 0) + ((if 9≤9 then (X Coord.U:Poly)^(9-9)*driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(1133703069106176) else 0) + (if 9≤9 then (X Coord.U:Poly)^(9-9)*driftSquare^((10+0)/2)*(C (1/3:ℂ)*deficit)^0*(-51534596210688) else 0)))) + (((if 10≤9 then (X Coord.U:Poly)^(9-10)*driftSquare^((7+1)/2)*(C (1/3:ℂ)*deficit)^1*(-40122452017152) else 0) + ((if 10≤9 then (X Coord.U:Poly)^(9-10)*driftSquare^((9+1)/2)*(C (1/3:ℂ)*deficit)^1*(6687075336192) else 0) + (if 10≤9 then (X Coord.U:Poly)^(9-10)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(-229450272473088) else 0))) + ((if 10≤9 then (X Coord.U:Poly)^(9-10)*driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(-19225341591552) else 0) + ((if 10≤9 then (X Coord.U:Poly)^(9-10)*driftSquare^((10+0)/2)*(C (1/3:ℂ)*deficit)^0*(4225860108288) else 0) + (if 11≤9 then (X Coord.U:Poly)^(9-11)*driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(5015306502144) else 0)))))
def scaled10Part19Mid : Poly := (((driftSquare^((7+1)/2)*(C (1/3:ℂ)*deficit)^1*(-40122452017152)) + (driftSquare^((9+1)/2)*(C (1/3:ℂ)*deficit)^1*(6687075336192))) + ((driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(-229450272473088)) + ((driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(-19225341591552)) + (driftSquare^((10+0)/2)*(C (1/3:ℂ)*deficit)^0*(4225860108288)))))
def scaled10Part19Upper : Poly := (driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(5015306502144))

theorem scaled10Part19_clear (h r t : ℂ) (hh : h≠0) :
    h^(9+2)*eval (sourcePoint h r t) moment10Part19 =
      h^2*eval (basePoint h r t) scaled10Part19Low+
      h*eval (basePoint h r t) scaled10Part19Mid+eval (basePoint h r t) scaled10Part19Upper := by
  norm_num [moment10Part19,scaled10Part19Low,scaled10Part19Mid,scaled10Part19Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled10Part20Low : Poly := ((((if 11≤9 then (X Coord.U:Poly)^(9-11)*driftSquare^((10+0)/2)*(C (1/3:ℂ)*deficit)^0*(-557256278016) else 0) + ((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(160938316815925248) else 0) + (if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(-481576059666432) else 0))) + ((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((5+1)/2)*(C (1/3:ℂ)*deficit)^1*(-327177085648896) else 0) + ((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((7+1)/2)*(C (1/3:ℂ)*deficit)^1*(2299011268608) else 0) + (if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((9+1)/2)*(C (1/3:ℂ)*deficit)^1*(-8153726976) else 0)))) + (((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(-149299498311745536) else 0) + ((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(1744681690202112) else 0) + (if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((4+2)/2)*(C (1/3:ℂ)*deficit)^2*(-2676914685739008) else 0))) + ((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((6+2)/2)*(C (1/3:ℂ)*deficit)^2*(100337980538880) else 0) + ((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((8+2)/2)*(C (1/3:ℂ)*deficit)^2*(-173776306176) else 0) + (if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((1+3)/2)*(C (1/3:ℂ)*deficit)^3*(107262236326625280) else 0)))))
def scaled10Part20Mid : Poly := (0:Poly)
def scaled10Part20Upper : Poly := (driftSquare^((10+0)/2)*(C (1/3:ℂ)*deficit)^0*(-557256278016))

theorem scaled10Part20_clear (h r t : ℂ) (hh : h≠0) :
    h^(9+2)*eval (sourcePoint h r t) moment10Part20 =
      h^2*eval (basePoint h r t) scaled10Part20Low+
      h*eval (basePoint h r t) scaled10Part20Mid+eval (basePoint h r t) scaled10Part20Upper := by
  norm_num [moment10Part20,scaled10Part20Low,scaled10Part20Mid,scaled10Part20Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled10Part21Low : Poly := ((((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((3+3)/2)*(C (1/3:ℂ)*deficit)^3*(-13136441311494144) else 0) + ((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((5+3)/2)*(C (1/3:ℂ)*deficit)^3*(734567543341056) else 0) + (if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((7+3)/2)*(C (1/3:ℂ)*deficit)^3*(-9730368995328) else 0))) + ((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((0+4)/2)*(C (1/3:ℂ)*deficit)^4*(62072707151167488) else 0) + ((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((2+4)/2)*(C (1/3:ℂ)*deficit)^4*(-34686602777198592) else 0) + (if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((4+4)/2)*(C (1/3:ℂ)*deficit)^4*(2807707951300608) else 0)))) + (((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((6+4)/2)*(C (1/3:ℂ)*deficit)^4*(-62408881078272) else 0) + ((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((1+5)/2)*(C (1/3:ℂ)*deficit)^5*(-21135383922475008) else 0) + (if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((3+5)/2)*(C (1/3:ℂ)*deficit)^5*(4463867016511488) else 0))) + ((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((5+5)/2)*(C (1/3:ℂ)*deficit)^5*(-163763975356416) else 0) + ((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((0+6)/2)*(C (1/3:ℂ)*deficit)^6*(-5108809461792768) else 0) + (if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((2+6)/2)*(C (1/3:ℂ)*deficit)^6*(2867656286011392) else 0)))))
def scaled10Part21Mid : Poly := (0:Poly)
def scaled10Part21Upper : Poly := (0:Poly)

theorem scaled10Part21_clear (h r t : ℂ) (hh : h≠0) :
    h^(9+2)*eval (sourcePoint h r t) moment10Part21 =
      h^2*eval (basePoint h r t) scaled10Part21Low+
      h*eval (basePoint h r t) scaled10Part21Mid+eval (basePoint h r t) scaled10Part21Upper := by
  norm_num [moment10Part21,scaled10Part21Low,scaled10Part21Mid,scaled10Part21Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled10Part22Low : Poly := ((((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((4+6)/2)*(C (1/3:ℂ)*deficit)^6*(-205976998379520) else 0) + ((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((1+7)/2)*(C (1/3:ℂ)*deficit)^7*(914720701022208) else 0) + (if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((3+7)/2)*(C (1/3:ℂ)*deficit)^7*(-131452284174336) else 0))) + ((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((0+8)/2)*(C (1/3:ℂ)*deficit)^8*(118649149194240) else 0) + ((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((2+8)/2)*(C (1/3:ℂ)*deficit)^8*(-48187188707328) else 0) + (if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((1+9)/2)*(C (1/3:ℂ)*deficit)^9*(-9287604633600) else 0)))) + (((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((0+10)/2)*(C (1/3:ℂ)*deficit)^10*(-743008370688) else 0) + ((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(10648022001647616) else 0) + (if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(332976678764544) else 0))) + ((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((6+0)/2)*(C (1/3:ℂ)*deficit)^0*(-5278009393152) else 0) + ((if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((8+0)/2)*(C (1/3:ℂ)*deficit)^0*(24461180928) else 0) + (if 0≤9 then (X Coord.U:Poly)^(9-0)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(0) else 0)))))
def scaled10Part22Mid : Poly := (0:Poly)
def scaled10Part22Upper : Poly := (0:Poly)

theorem scaled10Part22_clear (h r t : ℂ) (hh : h≠0) :
    h^(9+2)*eval (sourcePoint h r t) moment10Part22 =
      h^2*eval (basePoint h r t) scaled10Part22Low+
      h*eval (basePoint h r t) scaled10Part22Mid+eval (basePoint h r t) scaled10Part22Upper := by
  norm_num [moment10Part22,scaled10Part22Low,scaled10Part22Mid,scaled10Part22Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def low10 : Poly := ((((scaled10Part0Low + scaled10Part1Low) + (scaled10Part2Low + (scaled10Part3Low + scaled10Part4Low))) + ((scaled10Part5Low + (scaled10Part6Low + scaled10Part7Low)) + (scaled10Part8Low + (scaled10Part9Low + scaled10Part10Low)))) + (((scaled10Part11Low + (scaled10Part12Low + scaled10Part13Low)) + (scaled10Part14Low + (scaled10Part15Low + scaled10Part16Low))) + ((scaled10Part17Low + (scaled10Part18Low + scaled10Part19Low)) + (scaled10Part20Low + (scaled10Part21Low + scaled10Part22Low)))))
def mid10 : Poly := ((((scaled10Part0Mid + scaled10Part1Mid) + (scaled10Part2Mid + (scaled10Part3Mid + scaled10Part4Mid))) + ((scaled10Part5Mid + (scaled10Part6Mid + scaled10Part7Mid)) + (scaled10Part8Mid + (scaled10Part9Mid + scaled10Part10Mid)))) + (((scaled10Part11Mid + (scaled10Part12Mid + scaled10Part13Mid)) + (scaled10Part14Mid + (scaled10Part15Mid + scaled10Part16Mid))) + ((scaled10Part17Mid + (scaled10Part18Mid + scaled10Part19Mid)) + (scaled10Part20Mid + (scaled10Part21Mid + scaled10Part22Mid)))))
def upper10 : Poly := ((((scaled10Part0Upper + scaled10Part1Upper) + (scaled10Part2Upper + (scaled10Part3Upper + scaled10Part4Upper))) + ((scaled10Part5Upper + (scaled10Part6Upper + scaled10Part7Upper)) + (scaled10Part8Upper + (scaled10Part9Upper + scaled10Part10Upper)))) + (((scaled10Part11Upper + (scaled10Part12Upper + scaled10Part13Upper)) + (scaled10Part14Upper + (scaled10Part15Upper + scaled10Part16Upper))) + ((scaled10Part17Upper + (scaled10Part18Upper + scaled10Part19Upper)) + (scaled10Part20Upper + (scaled10Part21Upper + scaled10Part22Upper)))))

def midScaled10 : Poly := ((((-40122452017152:Poly)*(-X Coord.K*X Coord.U*C ((1/3:ℂ)^1)*(∑ i ∈ Finset.range ((7+1)/2), driftSquare^i*(9:Poly)^(((7+1)/2)-1-i)) - X Coord.J*C (1/3:ℂ)*1*driftSquare^((7+1)/2))) + ((6687075336192:Poly)*(-X Coord.K*X Coord.U*C ((1/3:ℂ)^1)*(∑ i ∈ Finset.range ((9+1)/2), driftSquare^i*(9:Poly)^(((9+1)/2)-1-i)) - X Coord.J*C (1/3:ℂ)*1*driftSquare^((9+1)/2)))) + (((-229450272473088:Poly)*(-X Coord.K*X Coord.U*C ((1/3:ℂ)^0)*(∑ i ∈ Finset.range ((6+0)/2), driftSquare^i*(9:Poly)^(((6+0)/2)-1-i)) - X Coord.J*C (1/3:ℂ)*0*driftSquare^((6+0)/2))) + (((-19225341591552:Poly)*(-X Coord.K*X Coord.U*C ((1/3:ℂ)^0)*(∑ i ∈ Finset.range ((8+0)/2), driftSquare^i*(9:Poly)^(((8+0)/2)-1-i)) - X Coord.J*C (1/3:ℂ)*0*driftSquare^((8+0)/2))) + ((4225860108288:Poly)*(-X Coord.K*X Coord.U*C ((1/3:ℂ)^0)*(∑ i ∈ Finset.range ((10+0)/2), driftSquare^i*(9:Poly)^(((10+0)/2)-1-i)) - X Coord.J*C (1/3:ℂ)*0*driftSquare^((10+0)/2))))))
def upperScaled10 : Poly := (557256278016:Poly)*X Coord.K*driftSquare^4
def scaledMoment10 : Poly := low10+midScaled10+upperScaled10

theorem mid10_scaled : mid10=X Coord.U*midScaled10 := by
  apply MvPolynomial.funext
  intro v
  norm_num [mid10,midScaled10,scaled10Part0Mid,scaled10Part1Mid,scaled10Part2Mid,scaled10Part3Mid,scaled10Part4Mid,scaled10Part5Mid,scaled10Part6Mid,scaled10Part7Mid,scaled10Part8Mid,scaled10Part9Mid,scaled10Part10Mid,scaled10Part11Mid,scaled10Part12Mid,scaled10Part13Mid,scaled10Part14Mid,scaled10Part15Mid,scaled10Part16Mid,scaled10Part17Mid,scaled10Part18Mid,scaled10Part19Mid,scaled10Part20Mid,scaled10Part21Mid,scaled10Part22Mid,driftSquare,deficit,Finset.sum_range_succ] <;> ring

theorem upper10_scaled : upper10=(X Coord.U)^2*upperScaled10 := by
  apply MvPolynomial.funext
  intro v
  norm_num [upper10,upperScaled10,scaled10Part0Upper,scaled10Part1Upper,scaled10Part2Upper,scaled10Part3Upper,scaled10Part4Upper,scaled10Part5Upper,scaled10Part6Upper,scaled10Part7Upper,scaled10Part8Upper,scaled10Part9Upper,scaled10Part10Upper,scaled10Part11Upper,scaled10Part12Upper,scaled10Part13Upper,scaled10Part14Upper,scaled10Part15Upper,scaled10Part16Upper,scaled10Part17Upper,scaled10Part18Upper,scaled10Part19Upper,scaled10Part20Upper,scaled10Part21Upper,scaled10Part22Upper,driftSquare,deficit] <;> ring

theorem scaledMoment10_eq (h r t : ℂ) (hh : h≠0) :
    h^9*eval (sourcePoint h r t) moment10=eval (basePoint h r t) scaledMoment10 := by
  have he : h^(9+2)*eval (sourcePoint h r t) moment10=
      h^2*eval (basePoint h r t) low10+h*eval (basePoint h r t) mid10+
        eval (basePoint h r t) upper10 := by
    simp only [moment10,low10,mid10,upper10,map_add,mul_add]
    rw [scaled10Part0_clear h r t hh,scaled10Part1_clear h r t hh,scaled10Part2_clear h r t hh,scaled10Part3_clear h r t hh,scaled10Part4_clear h r t hh,scaled10Part5_clear h r t hh,scaled10Part6_clear h r t hh,scaled10Part7_clear h r t hh,scaled10Part8_clear h r t hh,scaled10Part9_clear h r t hh,scaled10Part10_clear h r t hh,scaled10Part11_clear h r t hh,scaled10Part12_clear h r t hh,scaled10Part13_clear h r t hh,scaled10Part14_clear h r t hh,scaled10Part15_clear h r t hh,scaled10Part16_clear h r t hh,scaled10Part17_clear h r t hh,scaled10Part18_clear h r t hh,scaled10Part19_clear h r t hh,scaled10Part20_clear h r t hh,scaled10Part21_clear h r t hh,scaled10Part22_clear h r t hh]
    ring
  rw [mid10_scaled,upper10_scaled] at he
  apply mul_left_cancel₀ (pow_ne_zero 2 hh)
  calc h^2*(h^9*eval (sourcePoint h r t) moment10)=
        h^(9+2)*eval (sourcePoint h r t) moment10 := by ring
       _ = h^2*eval (basePoint h r t) scaledMoment10 := by
         rw [he]
         simp only [scaledMoment10,map_add,map_mul,map_pow,eval_X,basePoint]
         ring

theorem scaledMoment10_zero (r t : ℂ) :
    eval (basePoint 0 r t) scaledMoment10=(6:ℂ)^12*1679616*(r-12*t) := by
  norm_num [scaledMoment10,low10,midScaled10,upperScaled10,scaled10Part0Low,scaled10Part1Low,scaled10Part2Low,scaled10Part3Low,scaled10Part4Low,scaled10Part5Low,scaled10Part6Low,scaled10Part7Low,scaled10Part8Low,scaled10Part9Low,scaled10Part10Low,scaled10Part11Low,scaled10Part12Low,scaled10Part13Low,scaled10Part14Low,scaled10Part15Low,scaled10Part16Low,scaled10Part17Low,scaled10Part18Low,scaled10Part19Low,scaled10Part20Low,scaled10Part21Low,scaled10Part22Low,basePoint,driftSquare,deficit,Finset.sum_range_succ] <;> ring

end
end HTGeometry.ThetaRatioInfinity
