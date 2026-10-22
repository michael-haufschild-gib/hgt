import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioInfinityFlow
/-! # Exact source-flow compactification and the third-slope expanding mode. -/

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def scaled2Part0Low : Poly := ((((if 0≤3 then (X Coord.U:Poly)^(3-0)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(1152) else 0) + ((if 1≤3 then (X Coord.U:Poly)^(3-1)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(-1620) else 0) + (if 1≤3 then (X Coord.U:Poly)^(3-1)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(1440) else 0))) + ((if 1≤3 then (X Coord.U:Poly)^(3-1)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(-12) else 0) + ((if 1≤3 then (X Coord.U:Poly)^(3-1)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(-5184) else 0) + (if 2≤3 then (X Coord.U:Poly)^(3-2)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(-31104) else 0)))) + (((if 2≤3 then (X Coord.U:Poly)^(3-2)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(8640) else 0) + ((if 2≤3 then (X Coord.U:Poly)^(3-2)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(576) else 0) + (if 3≤3 then (X Coord.U:Poly)^(3-3)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(-3888) else 0))) + ((if 3≤3 then (X Coord.U:Poly)^(3-3)*driftSquare^((2+0)/2)*(C (1/3:ℂ)*deficit)^0*(-3024) else 0) + ((if 0≤3 then (X Coord.U:Poly)^(3-0)*driftSquare^((1+1)/2)*(C (1/3:ℂ)*deficit)^1*(-480) else 0) + (if 0≤3 then (X Coord.U:Poly)^(3-0)*driftSquare^((0+2)/2)*(C (1/3:ℂ)*deficit)^2*(-1728) else 0)))))
def scaled2Part0Mid : Poly := (0:Poly)
def scaled2Part0Upper : Poly := (0:Poly)

theorem scaled2Part0_clear (h r t : ℂ) (hh : h≠0) :
    h^(3+2)*eval (sourcePoint h r t) moment2Part0 =
      h^2*eval (basePoint h r t) scaled2Part0Low+
      h*eval (basePoint h r t) scaled2Part0Mid+eval (basePoint h r t) scaled2Part0Upper := by
  norm_num [moment2Part0,scaled2Part0Low,scaled2Part0Mid,scaled2Part0Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def scaled2Part1Low : Poly := (if 0≤3 then (X Coord.U:Poly)^(3-0)*driftSquare^((0+0)/2)*(C (1/3:ℂ)*deficit)^0*(0) else 0)
def scaled2Part1Mid : Poly := (0:Poly)
def scaled2Part1Upper : Poly := (0:Poly)

theorem scaled2Part1_clear (h r t : ℂ) (hh : h≠0) :
    h^(3+2)*eval (sourcePoint h r t) moment2Part1 =
      h^2*eval (basePoint h r t) scaled2Part1Low+
      h*eval (basePoint h r t) scaled2Part1Mid+eval (basePoint h r t) scaled2Part1Upper := by
  norm_num [moment2Part1,scaled2Part1Low,scaled2Part1Mid,scaled2Part1Upper,sourcePoint,basePoint,driftSquare,deficit] <;> field_simp [hh] <;> ring

def low2 : Poly := (scaled2Part0Low + scaled2Part1Low)
def mid2 : Poly := (scaled2Part0Mid + scaled2Part1Mid)
def upper2 : Poly := (scaled2Part0Upper + scaled2Part1Upper)

def midScaled2 : Poly := (0:Poly)
def upperScaled2 : Poly := (0:Poly)*X Coord.K*driftSquare^0
def scaledMoment2 : Poly := low2+midScaled2+upperScaled2

theorem mid2_scaled : mid2=X Coord.U*midScaled2 := by
  apply MvPolynomial.funext
  intro v
  norm_num [mid2,midScaled2,scaled2Part0Mid,scaled2Part1Mid,driftSquare,deficit,Finset.sum_range_succ] <;> ring

theorem upper2_scaled : upper2=(X Coord.U)^2*upperScaled2 := by
  apply MvPolynomial.funext
  intro v
  norm_num [upper2,upperScaled2,scaled2Part0Upper,scaled2Part1Upper,driftSquare,deficit] <;> ring

theorem scaledMoment2_eq (h r t : ℂ) (hh : h≠0) :
    h^3*eval (sourcePoint h r t) moment2=eval (basePoint h r t) scaledMoment2 := by
  have he : h^(3+2)*eval (sourcePoint h r t) moment2=
      h^2*eval (basePoint h r t) low2+h*eval (basePoint h r t) mid2+
        eval (basePoint h r t) upper2 := by
    simp only [moment2,low2,mid2,upper2,map_add,mul_add]
    rw [scaled2Part0_clear h r t hh,scaled2Part1_clear h r t hh]
    ring
  rw [mid2_scaled,upper2_scaled] at he
  apply mul_left_cancel₀ (pow_ne_zero 2 hh)
  calc h^2*(h^3*eval (sourcePoint h r t) moment2)=
        h^(3+2)*eval (sourcePoint h r t) moment2 := by ring
       _ = h^2*eval (basePoint h r t) scaledMoment2 := by
         rw [he]
         simp only [scaledMoment2,map_add,map_mul,map_pow,eval_X,basePoint]
         ring

theorem scaledMoment2_zero (r t : ℂ) :
    eval (basePoint 0 r t) scaledMoment2=-(6:ℂ)^4*24 := by
  norm_num [scaledMoment2,low2,midScaled2,upperScaled2,scaled2Part0Low,scaled2Part1Low,basePoint,driftSquare,deficit,Finset.sum_range_succ] <;> ring

end
end HTGeometry.ThetaRatioInfinity
