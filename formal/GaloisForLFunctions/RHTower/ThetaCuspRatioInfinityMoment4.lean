import GaloisForLFunctions.RHTower.ThetaCuspRatioInfinityFlow
/-! # Exact source-flow compactification and the third-slope expanding mode. -/

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def scaled4Part0Low : Poly := ((((if 0≤4 then (X Coord.U:Poly)^(4-0)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(819072) else 0) + ((if 1≤4 then (X Coord.U:Poly)^(4-1)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(20481984) else 0) + (if 1≤4 then (X Coord.U:Poly)^(4-1)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(-6697728) else 0))) + ((if 1≤4 then (X Coord.U:Poly)^(4-1)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(158976) else 0) + ((if 1≤4 then (X Coord.U:Poly)^(4-1)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(11524032) else 0) + (if 1≤4 then (X Coord.U:Poly)^(4-1)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(502848) else 0)))) + (((if 1≤4 then (X Coord.U:Poly)^(4-1)*driftSquare^((1+3)/2)*(C (1/3:ℂ)*deficit)^3*(-373248) else 0) + ((if 1≤4 then (X Coord.U:Poly)^(4-1)*driftSquare^((0+4)/2)*(C (1/3:ℂ)*deficit)^4*(-746496) else 0) + (if 1≤4 then (X Coord.U:Poly)^(4-1)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(-312768) else 0))) + ((if 2≤4 then (X Coord.U:Poly)^(4-2)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(70368912) else 0) + ((if 2≤4 then (X Coord.U:Poly)^(4-2)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(-24603264) else 0) + (if 2≤4 then (X Coord.U:Poly)^(4-2)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(10368) else 0)))))
def scaled4Part0Mid : Poly := (0:Poly)
def scaled4Part0Upper : Poly := (0:Poly)

theorem scaled4Part0_clear (h r t : ℂ) (hh : h≠0) :
    h^(4+2)*eval (sourcePoint h r t) moment4Part0 =
      h^2*eval (basePoint h r t) scaled4Part0Low+
      h*eval (basePoint h r t) scaled4Part0Mid+eval (basePoint h r t) scaled4Part0Upper := by
  norm_num [moment4Part0,scaled4Part0Low,scaled4Part0Mid,scaled4Part0Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled4Part1Low : Poly := ((((if 2≤4 then (X Coord.U:Poly)^(4-2)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(559872) else 0) + ((if 2≤4 then (X Coord.U:Poly)^(4-2)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(2177280) else 0) + (if 2≤4 then (X Coord.U:Poly)^(4-2)*driftSquare^((1+3)/2)*(C (1/3:ℂ)*deficit)^3*(2239488) else 0))) + ((if 2≤4 then (X Coord.U:Poly)^(4-2)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(-609120) else 0) + ((if 2≤4 then (X Coord.U:Poly)^(4-2)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(23760) else 0) + (if 3≤4 then (X Coord.U:Poly)^(4-3)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(25894080) else 0)))) + (((if 3≤4 then (X Coord.U:Poly)^(4-3)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(-4478976) else 0) + ((if 3≤4 then (X Coord.U:Poly)^(4-3)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(-1866240) else 0) + (if 3≤4 then (X Coord.U:Poly)^(4-3)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(1679616) else 0))) + ((if 3≤4 then (X Coord.U:Poly)^(4-3)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(-2426112) else 0) + ((if 3≤4 then (X Coord.U:Poly)^(4-3)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(10435392) else 0) + (if 3≤4 then (X Coord.U:Poly)^(4-3)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(-165888) else 0)))))
def scaled4Part1Mid : Poly := (0:Poly)
def scaled4Part1Upper : Poly := (0:Poly)

theorem scaled4Part1_clear (h r t : ℂ) (hh : h≠0) :
    h^(4+2)*eval (sourcePoint h r t) moment4Part1 =
      h^2*eval (basePoint h r t) scaled4Part1Low+
      h*eval (basePoint h r t) scaled4Part1Mid+eval (basePoint h r t) scaled4Part1Upper := by
  norm_num [moment4Part1,scaled4Part1Low,scaled4Part1Mid,scaled4Part1Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled4Part2Low : Poly := ((((if 4≤4 then (X Coord.U:Poly)^(4-4)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(11337408) else 0) + ((if 4≤4 then (X Coord.U:Poly)^(4-4)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(-3359232) else 0) + (if 4≤4 then (X Coord.U:Poly)^(4-4)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(1119744) else 0))) + ((if 4≤4 then (X Coord.U:Poly)^(4-4)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(1399680) else 0) + ((if 4≤4 then (X Coord.U:Poly)^(4-4)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(451008) else 0) + (if 5≤4 then (X Coord.U:Poly)^(4-5)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(1679616) else 0)))) + (((if 5≤4 then (X Coord.U:Poly)^(4-5)*driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(-186624) else 0) + ((if 0≤4 then (X Coord.U:Poly)^(4-0)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(376704) else 0) + (if 0≤4 then (X Coord.U:Poly)^(4-0)*driftSquare^((3+1)/2)*(C (1/3:ℂ)*deficit)^1*(-31104) else 0))) + ((if 0≤4 then (X Coord.U:Poly)^(4-0)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(3841344) else 0) + ((if 0≤4 then (X Coord.U:Poly)^(4-0)*driftSquare^((2+2)/2)*(C (1/3:ℂ)*deficit)^2*(-164160) else 0) + (if 0≤4 then (X Coord.U:Poly)^(4-0)*driftSquare^((1+3)/2)*(C (1/3:ℂ)*deficit)^3*(-373248) else 0)))))
def scaled4Part2Mid : Poly := ((driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(1679616)) + (driftSquare^((4+0)/2)*(C (1/3:ℂ)*deficit)^0*(-186624)))
def scaled4Part2Upper : Poly := (0:Poly)

theorem scaled4Part2_clear (h r t : ℂ) (hh : h≠0) :
    h^(4+2)*eval (sourcePoint h r t) moment4Part2 =
      h^2*eval (basePoint h r t) scaled4Part2Low+
      h*eval (basePoint h r t) scaled4Part2Mid+eval (basePoint h r t) scaled4Part2Upper := by
  norm_num [moment4Part2,scaled4Part2Low,scaled4Part2Mid,scaled4Part2Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled4Part3Low : Poly := ((if 0≤4 then (X Coord.U:Poly)^(4-0)*driftSquare^((0+4)/2)*(C (1/3:ℂ)*deficit)^4*(-248832) else 0) + ((if 0≤4 then (X Coord.U:Poly)^(4-0)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(93312) else 0) + (if 0≤4 then (X Coord.U:Poly)^(4-0)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(0) else 0)))
def scaled4Part3Mid : Poly := (0:Poly)
def scaled4Part3Upper : Poly := (0:Poly)

theorem scaled4Part3_clear (h r t : ℂ) (hh : h≠0) :
    h^(4+2)*eval (sourcePoint h r t) moment4Part3 =
      h^2*eval (basePoint h r t) scaled4Part3Low+
      h*eval (basePoint h r t) scaled4Part3Mid+eval (basePoint h r t) scaled4Part3Upper := by
  norm_num [moment4Part3,scaled4Part3Low,scaled4Part3Mid,scaled4Part3Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def low4 : Poly := ((scaled4Part0Low + scaled4Part1Low) + (scaled4Part2Low + scaled4Part3Low))
def mid4 : Poly := ((scaled4Part0Mid + scaled4Part1Mid) + (scaled4Part2Mid + scaled4Part3Mid))
def upper4 : Poly := ((scaled4Part0Upper + scaled4Part1Upper) + (scaled4Part2Upper + scaled4Part3Upper))

def midScaled4 : Poly := (((1679616:Poly)*(-X Coord.K*X Coord.U*C ((1/3:ℂ)^0)*(∑ i ∈ Finset.range ((2+0)/2), driftSquare^i*(9:Poly)^(((2+0)/2)-1-i)) - X Coord.J*C (1/3:ℂ)*0*driftSquare^((2+0)/2))) + ((-186624:Poly)*(-X Coord.K*X Coord.U*C ((1/3:ℂ)^0)*(∑ i ∈ Finset.range ((4+0)/2), driftSquare^i*(9:Poly)^(((4+0)/2)-1-i)) - X Coord.J*C (1/3:ℂ)*0*driftSquare^((4+0)/2))))
def upperScaled4 : Poly := (0:Poly)*X Coord.K*driftSquare^0
def scaledMoment4 : Poly := low4+midScaled4+upperScaled4

theorem mid4_scaled : mid4=X Coord.U*midScaled4 := by
  apply MvPolynomial.funext
  intro v
  norm_num [mid4,midScaled4,scaled4Part0Mid,scaled4Part1Mid,scaled4Part2Mid,scaled4Part3Mid,driftSquare,deficit,Finset.sum_range_succ] <;> ring

theorem upper4_scaled : upper4=(X Coord.U)^2*upperScaled4 := by
  apply MvPolynomial.funext
  intro v
  norm_num [upper4,upperScaled4,scaled4Part0Upper,scaled4Part1Upper,scaled4Part2Upper,scaled4Part3Upper,driftSquare,deficit] <;> ring

theorem scaledMoment4_eq (h r t : ℂ) (hh : h≠0) :
    h^4*eval (sourcePoint h r t) moment4=eval (basePoint h r t) scaledMoment4 := by
  have he : h^(4+2)*eval (sourcePoint h r t) moment4=
      h^2*eval (basePoint h r t) low4+h*eval (basePoint h r t) mid4+
        eval (basePoint h r t) upper4 := by
    simp only [moment4,low4,mid4,upper4,map_add,mul_add]
    rw [scaled4Part0_clear h r t hh,scaled4Part1_clear h r t hh,scaled4Part2_clear h r t hh,scaled4Part3_clear h r t hh]
    ring
  rw [mid4_scaled,upper4_scaled] at he
  apply mul_left_cancel₀ (pow_ne_zero 2 hh)
  calc h^2*(h^4*eval (sourcePoint h r t) moment4)=
        h^(4+2)*eval (sourcePoint h r t) moment4 := by ring
       _ = h^2*eval (basePoint h r t) scaledMoment4 := by
         rw [he]
         simp only [scaledMoment4,map_add,map_mul,map_pow,eval_X,basePoint]
         ring

theorem scaledMoment4_zero (r t : ℂ) :
    eval (basePoint 0 r t) scaledMoment4=(6:ℂ)^6*1728 := by
  norm_num [scaledMoment4,low4,midScaled4,upperScaled4,scaled4Part0Low,scaled4Part1Low,scaled4Part2Low,scaled4Part3Low,basePoint,driftSquare,deficit,Finset.sum_range_succ] <;> ring

end
end HTGeometry.ThetaRatioInfinity
