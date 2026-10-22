import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioInfinitySlope
import Mathlib.Algebra.QuadraticAlgebra.Basic
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def boundaryMass (v k : ℂ) : ℂ := k*(6*k-7)*(9-v)/72
def boundaryA (v k : ℂ) : ℂ := (k-1-boundaryMass v k)/9
def boundaryB (k : ℂ) : ℂ := (2-k)/3
abbrev BoundaryAlg (v k : ℂ) := QuadraticAlgebra ℂ (boundaryA v k) (boundaryB k)

def boundaryCoord (v k : ℂ) : Coord → BoundaryAlg v k
  | .U => algebraMap ℂ (BoundaryAlg v k) v
  | .K => algebraMap ℂ (BoundaryAlg v k) k
  | .J => QuadraticAlgebra.omega

def boundaryHom (v k : ℂ) : Poly →+* BoundaryAlg v k :=
  eval₂Hom (algebraMap ℂ (BoundaryAlg v k)) (boundaryCoord v k)

@[simp] theorem boundaryHom_C (v k c : ℂ) :
    boundaryHom v k (C c)=algebraMap ℂ (BoundaryAlg v k) c := by simp [boundaryHom]
@[simp] theorem boundaryHom_X (v k : ℂ) (i : Coord) :
    boundaryHom v k (X i)=boundaryCoord v k i := by simp [boundaryHom]

def boundaryEval (v k z : ℂ) (hz : z^2=boundaryA v k+boundaryB k*z) :
    BoundaryAlg v k →+* ℂ where
  toFun w := w.re+z*w.im
  map_one' := by simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  map_zero' := by simp
  map_add' p q := by simp only [QuadraticAlgebra.re_add,QuadraticAlgebra.im_add]; ring
  map_mul' p q := by
    simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul]
    linear_combination -(p.im*q.im)*hz

@[simp] theorem boundaryEval_C (v k z : ℂ) (hz : z^2=boundaryA v k+boundaryB k*z) (c : ℂ) :
    boundaryEval v k z hz (algebraMap ℂ (BoundaryAlg v k) c)=c := by simp [boundaryEval]

@[simp] theorem boundaryEval_coord (v k z : ℂ) (hz : z^2=boundaryA v k+boundaryB k*z) (i : Coord) :
    boundaryEval v k z hz (boundaryCoord v k i)=basePoint v k z i := by
  cases i <;> simp [boundaryCoord,boundaryEval,basePoint,QuadraticAlgebra.omega]

theorem boundaryHom_eval (P : Poly) (v k z : ℂ)
    (hz : z^2=boundaryA v k+boundaryB k*z) :
    eval (basePoint v k z) P=(boundaryHom v k P).re+z*(boundaryHom v k P).im := by
  change eval (basePoint v k z) P=boundaryEval v k z hz (boundaryHom v k P)
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [hp]

theorem boundary_root_iff (v k z : ℂ) :
    z^2=boundaryA v k+boundaryB k*z ↔
      (1-3*z)^2-k*(1-3*z)+boundaryMass v k=0 := by
  unfold boundaryA boundaryB
  constructor
  · intro h
    linear_combination h*9
  · intro h
    linear_combination h/9

theorem compact_boundary_mass (h r t : ℂ) (hh : h≠0) :
    (1-3*((1-t*h)/3))^2-h⁻¹*(1-3*((1-t*h)/3))+
      boundaryMass (9-r*h^2) h⁻¹ = -(t-h^2*t^2-r*(1/12-7*h/72)) := by
  unfold boundaryMass
  field_simp
  ring

end
end HTGeometry.ThetaRatioInfinity
