import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioNonlinearBoundaryCore
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioScaledDriftFactor
/-!
The complete nonlinear-boundary core is a polynomial and has its forced
drift factor V=9-h^2*R. The Bezout identity for V and h removes the
clock factor algebraically. No sign premise is used.
-/
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def nonlinearBoundarySeedPoly : Poly := C (1/12:ℂ)-C (7/72:ℂ)*X Coord.U
def nonlinearBoundaryRPoly : Poly := X Coord.K*(1-(X Coord.U)^2*nonlinearBoundarySeedPoly*X Coord.K)
def nonlinearBoundaryTPoly : Poly := nonlinearBoundarySeedPoly*X Coord.K
def nonlinearBoundaryVPoly : Poly := 9-nonlinearBoundaryRPoly*(X Coord.U)^2
def nonlinearBoundaryGapPoly : Poly := nonlinearBoundarySeedPoly*(X Coord.K)^3*
  (2-(X Coord.U)^2*nonlinearBoundarySeedPoly*X Coord.K)*
  (C (1/144:ℂ)-C (7/432:ℂ)*X Coord.U)+C (49/5184:ℂ)*(X Coord.K)^2

@[simp] theorem nonlinearBoundarySeedPoly_eval (h s u : ℂ) :
    eval (basePoint h s u) nonlinearBoundarySeedPoly=nonlinearBoundarySeed h := by
  simp [nonlinearBoundarySeedPoly,nonlinearBoundarySeed,basePoint]
  ring
@[simp] theorem nonlinearBoundaryRPoly_eval (h s u : ℂ) :
    eval (basePoint h s u) nonlinearBoundaryRPoly=nonlinearBoundaryR h s := by
  simp [nonlinearBoundaryRPoly,nonlinearBoundaryR,basePoint]
@[simp] theorem nonlinearBoundaryTPoly_eval (h s u : ℂ) :
    eval (basePoint h s u) nonlinearBoundaryTPoly=nonlinearBoundaryT h s := by
  simp [nonlinearBoundaryTPoly,nonlinearBoundaryT,basePoint]
@[simp] theorem nonlinearBoundaryVPoly_eval (h s u : ℂ) :
    eval (basePoint h s u) nonlinearBoundaryVPoly=nonlinearBoundaryV h s := by
  simp [nonlinearBoundaryVPoly,nonlinearBoundaryV,basePoint]
@[simp] theorem nonlinearBoundaryGapPoly_eval (h s u : ℂ) :
    eval (basePoint h s u) nonlinearBoundaryGapPoly=nonlinearBoundaryCubicGap h s := by
  simp [nonlinearBoundaryGapPoly,nonlinearBoundaryCubicGap,basePoint]
  ring

def nonlinearBoundaryLiftCoord (W : Poly) : Coord → Poly
  | .U => X .U
  | .K => nonlinearBoundaryRPoly
  | .J => W
def nonlinearBoundaryLift (W : Poly) : Poly →+* Poly := eval₂Hom C (nonlinearBoundaryLiftCoord W)
@[simp] theorem nonlinearBoundaryLift_C (W : Poly) (c : ℂ) :
    nonlinearBoundaryLift W (C c)=C c := by simp [nonlinearBoundaryLift]
@[simp] theorem nonlinearBoundaryLift_X (W : Poly) (i : Coord) :
    nonlinearBoundaryLift W (X i)=nonlinearBoundaryLiftCoord W i := by simp [nonlinearBoundaryLift]

theorem nonlinearBoundaryLift_eval (W P : Poly) (h s u : ℂ) :
    eval (basePoint h s u) (nonlinearBoundaryLift W P)=
      eval (basePoint h (nonlinearBoundaryR h s) (eval (basePoint h s u) W)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,nonlinearBoundaryLift_X,eval_X,hp]
    congr 1
    cases i <;> simp [nonlinearBoundaryLiftCoord,basePoint]

def nonlinearBoundaryCorePoly : Poly := nonlinearBoundaryLift 0 nonlinearCubicCore+
  X Coord.U*nonlinearBoundaryGapPoly*
    nonlinearBoundaryLift ((X Coord.U)^4*nonlinearBoundaryGapPoly) nonlinearTransverseCore

@[simp] theorem nonlinearBoundaryCorePoly_eval (h s u : ℂ) :
    eval (basePoint h s u) nonlinearBoundaryCorePoly=nonlinearBoundaryCore h s := by
  simp [nonlinearBoundaryCorePoly,nonlinearBoundaryLift_eval,nonlinearBoundaryCore,basePoint]

theorem nonlinearBoundaryLift_scaledSlope :
    nonlinearBoundaryLift nonlinearBoundaryTPoly scaledSlope=(X Coord.U)^3*nonlinearBoundaryCorePoly := by
  apply MvPolynomial.funext
  intro v
  rw [←basePoint_eta v]
  simp only [nonlinearBoundaryLift_eval,nonlinearBoundaryTPoly_eval,map_mul,map_pow,eval_X,
    basePoint,nonlinearBoundaryCorePoly_eval]
  exact nonlinearBoundary_scaledSlope _ _

theorem nonlinearBoundaryLift_drift : nonlinearBoundaryLift nonlinearBoundaryTPoly driftSquare=nonlinearBoundaryVPoly := by
  change nonlinearBoundaryLift nonlinearBoundaryTPoly (C (9:ℂ)-X Coord.K*(X Coord.U)^2)=
    C (9:ℂ)-nonlinearBoundaryRPoly*(X Coord.U)^2
  simp [nonlinearBoundaryLiftCoord]

theorem nonlinearBoundaryVPoly_coprime_clock : IsCoprime nonlinearBoundaryVPoly (X Coord.U) := by
  refine ⟨C (1/9:ℂ),C (1/9:ℂ)*nonlinearBoundaryRPoly*X Coord.U,?_⟩
  apply MvPolynomial.funext
  intro v
  norm_num [nonlinearBoundaryVPoly]
  ring

theorem nonlinearBoundaryCorePoly_dvd : nonlinearBoundaryVPoly ∣ nonlinearBoundaryCorePoly := by
  have he := congrArg (nonlinearBoundaryLift nonlinearBoundaryTPoly) scaledSlope_drift_factor
  rw [nonlinearBoundaryLift_scaledSlope,map_mul,nonlinearBoundaryLift_drift] at he
  have hd : nonlinearBoundaryVPoly ∣ (X Coord.U)^3*nonlinearBoundaryCorePoly :=
    ⟨nonlinearBoundaryLift nonlinearBoundaryTPoly reducedScaledSlope,he⟩
  exact (nonlinearBoundaryVPoly_coprime_clock.pow_right).dvd_of_dvd_mul_left hd

def reducedNonlinearBoundaryCore : Poly := nonlinearBoundaryCorePoly_dvd.choose
theorem nonlinearBoundaryCorePoly_factor :
    nonlinearBoundaryCorePoly=nonlinearBoundaryVPoly*reducedNonlinearBoundaryCore :=
  nonlinearBoundaryCorePoly_dvd.choose_spec

theorem nonlinearBoundaryVPoly_ne_zero : nonlinearBoundaryVPoly≠0 := by
  intro he
  have hv := congrArg (eval (basePoint 0 0 0)) he
  norm_num [nonlinearBoundaryV,nonlinearBoundaryR] at hv

end
end HTGeometry.ThetaRatioInfinity
