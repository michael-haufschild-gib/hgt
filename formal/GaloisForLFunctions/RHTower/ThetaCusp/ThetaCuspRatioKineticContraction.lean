import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticClockReduced
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioNonlinearBoundaryQuotient
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def boundaryZPoly : Poly := C (1/3:ℂ)*(1-X Coord.U*nonlinearBoundaryTPoly)

theorem boundaryZPoly_eval (h s e : ℂ) :
    eval (basePoint h s e) boundaryZPoly=nonlinearBoundaryZ h s := by
  simp only [boundaryZPoly,map_mul,map_sub,map_one,eval_C,eval_X,basePoint,
    nonlinearBoundaryTPoly_eval,nonlinearBoundaryZ]
  ring

def contractionSource : Poly :=
  nonlinearBoundaryLift (X Coord.J*boundaryZPoly) compactReducedSlope

theorem contractionSource_eval (h s e : ℂ) (hh : h≠0) :
    eval (basePoint h s e) contractionSource=
      h^20*eval (basePoint (nonlinearBoundaryV h s) h⁻¹ (e*nonlinearBoundaryZ h s))
        reducedSlope := by
  rw [contractionSource,nonlinearBoundaryLift_eval]
  simp only [map_mul,eval_X,basePoint,boundaryZPoly_eval]
  exact compactReducedSlope_eval h _ _ hh

def kineticOneCoord : Coord → Poly
  | .U => X .U
  | .K => X .K
  | .J => 1

def kineticOne : Poly →+* Poly := eval₂Hom C kineticOneCoord

@[simp] theorem kineticOne_C (c : ℂ) : kineticOne (C c)=C c := by simp [kineticOne]
@[simp] theorem kineticOne_X (i : Coord) : kineticOne (X i)=kineticOneCoord i := by simp [kineticOne]

theorem kineticOne_eval (P : Poly) (h s e : ℂ) :
    eval (basePoint h s e) (kineticOne P)=eval (basePoint h s 1) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => cases i <;> simp [hp,kineticOneCoord,basePoint]

theorem kineticOne_division (P : Poly) :
    ∃ Q : Poly, P=(1-X Coord.J)*Q+kineticOne P := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨0,by simp⟩
  | add p q hp hq =>
    obtain ⟨a,ha⟩ := hp
    obtain ⟨b,hb⟩ := hq
    refine ⟨a+b,?_⟩
    rw [map_add]
    conv_lhs => rw [ha,hb]
    ring
  | mul_X p i hp =>
    obtain ⟨a,ha⟩ := hp
    cases i with
    | U =>
      refine ⟨a*X Coord.U,?_⟩
      simp only [map_mul,kineticOne_X,kineticOneCoord]
      conv_lhs => rw [ha]
      ring
    | K =>
      refine ⟨a*X Coord.K,?_⟩
      simp only [map_mul,kineticOne_X,kineticOneCoord]
      conv_lhs => rw [ha]
      ring
    | J =>
      refine ⟨a*X Coord.J-kineticOne p,?_⟩
      simp only [map_mul,kineticOne_X,kineticOneCoord]
      conv_lhs => rw [ha]
      ring

theorem contractionSource_boundary :
    kineticOne contractionSource=(X Coord.U)^4*reducedNonlinearBoundaryCore := by
  apply polynomial_ext_clock_nonzero
  intro h s e hh
  rw [kineticOne_eval,contractionSource_eval h s 1 hh]
  simp only [one_mul,map_mul,map_pow,eval_X,basePoint]
  rw [reducedNonlinearBoundaryCore_source hh]
  ring

def contractionRemainder : Poly := (kineticOne_division contractionSource).choose

theorem complete_kinetic_contraction : contractionSource=
    (X Coord.U)^4*reducedNonlinearBoundaryCore+(1-X Coord.J)*contractionRemainder := by
  rw [add_comm,←contractionSource_boundary]
  exact (kineticOne_division contractionSource).choose_spec

theorem complete_kinetic_contraction_eval (h s e : ℂ) (hh : h≠0) :
    h^20*eval (basePoint (nonlinearBoundaryV h s) h⁻¹ (e*nonlinearBoundaryZ h s))
        reducedSlope=
      h^4*eval (basePoint h s e) reducedNonlinearBoundaryCore+
        (1-e)*eval (basePoint h s e) contractionRemainder := by
  rw [←contractionSource_eval h s e hh,complete_kinetic_contraction]
  simp only [map_add,map_mul,map_sub,map_one,map_pow,eval_X,basePoint]

end
end HTGeometry.ThetaRatioKineticContraction
