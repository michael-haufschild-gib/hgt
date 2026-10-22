import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioSquareSlope
/-! # Exact source-flow compactification and the third-slope expanding mode. -/

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def basePoint (h r t : ℂ) : Coord → ℂ
  | .U => h
  | .K => r
  | .J => t

def sourcePoint (h r t : ℂ) : Coord → ℂ
  | .U => 9-r*h^2
  | .K => h⁻¹
  | .J => (1-t*h)/3

def driftSquare : Poly := 9-X Coord.K*(X Coord.U)^2
def deficit : Poly := 1-X Coord.J*X Coord.U
def speed : Poly := X Coord.K-6*X Coord.J-
  C (2/3:ℂ)*X Coord.K*X Coord.U-4*X Coord.J*X Coord.U+
  C (2/3:ℂ)*X Coord.K*X Coord.J*(X Coord.U)^2-
  C (4/9:ℂ)*X Coord.K*(X Coord.U)^2+
  C (4/9:ℂ)*X Coord.K*X Coord.J*(X Coord.U)^3

/-- The original square-chart derivation multiplied by h=1/k. -/
def infinityField : Coord → Poly
  | .U => C (-4/3:ℂ)*(X Coord.U)^2*(3+X Coord.U)*driftSquare*deficit
  | .K => C (8/3:ℂ)*X Coord.K*X Coord.U*(3+X Coord.U)*driftSquare*deficit-
      12*driftSquare*X Coord.K
  | .J => C (4/3:ℂ)*X Coord.J*X Coord.U*(3+X Coord.U)*driftSquare*deficit-
      18*speed+6*X Coord.K*X Coord.U*deficit

def expandingMode : Poly := X Coord.K-12*X Coord.J

theorem field_change (h r t : ℂ) (hh : h≠0) :
    -h^2*eval (basePoint h r t) (infinityField Coord.K)-
        2*r*h*eval (basePoint h r t) (infinityField Coord.U)=
      h*eval (sourcePoint h r t) (squareField Coord.U) ∧
    -h⁻¹^2*eval (basePoint h r t) (infinityField Coord.U)=
      h*eval (sourcePoint h r t) (squareField Coord.K) ∧
    -(h*eval (basePoint h r t) (infinityField Coord.J)+
        t*eval (basePoint h r t) (infinityField Coord.U))/3=
      h*eval (sourcePoint h r t) (squareField Coord.J) := by
  refine ⟨?_,?_,?_⟩ <;>
    norm_num [infinityField,squareField,basePoint,sourcePoint,driftSquare,deficit,speed] <;>
    field_simp [hh] <;> ring

theorem infinityField_zero (r t : ℂ) :
    eval (basePoint 0 r t) (infinityField Coord.U)=0 ∧
    eval (basePoint 0 r t) (infinityField Coord.K)=-108*r ∧
    eval (basePoint 0 r t) (infinityField Coord.J)=-18*r+108*t := by
  norm_num [infinityField,basePoint,driftSquare,deficit,speed]
  ring

theorem expandingMode_zero (r t : ℂ) :
    eval (basePoint 0 r t) (flow infinityField expandingMode)=108*(r-12*t) := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by
    ext i
    cases i <;> simp
  simp [flow,expandingMode,hu,pderiv_X,Pi.single_apply,pderiv_mul,
    infinityField,basePoint,driftSquare,deficit,speed]
  ring

end
end HTGeometry.ThetaRatioInfinity
