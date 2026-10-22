import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticClockMinor
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticClockDefect
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticClockMomentJets
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

theorem defectMoment4_clock_factor :
    ∃ Q : Poly, defectLift clearMoment4=X Coord.U*Q := by
  apply clock_factor_of_zero
  intro r z
  rw [defectLift_eval]
  simpa using clearMoment4_zero z

def defectMoment4Core : Poly := defectMoment4_clock_factor.choose

theorem defectMoment4_factor :
    defectLift clearMoment4=X Coord.U*defectMoment4Core :=
  defectMoment4_clock_factor.choose_spec

theorem defectMoment4Core_zero (r z : ℂ) :
    eval (basePoint 0 r z) defectMoment4Core=12^5*3^5*(z+1) := by
  rw [clock_factor_first _ _ defectMoment4_factor,defectLift_pderiv_zero,clearMoment4_first]

theorem defectMoment6_clock_factor :
    ∃ Q : Poly, defectLift clearMoment6=X Coord.U*Q := by
  apply clock_factor_of_zero
  intro r z
  rw [defectLift_eval]
  simpa using clearMoment6_zero z

def defectMoment6Core : Poly := defectMoment6_clock_factor.choose

theorem defectMoment6_factor :
    defectLift clearMoment6=X Coord.U*defectMoment6Core :=
  defectMoment6_clock_factor.choose_spec

theorem defectMoment6Core_zero (r z : ℂ) :
    eval (basePoint 0 r z) defectMoment6Core=12^7*3^6*(3*z-1) := by
  rw [clock_factor_first _ _ defectMoment6_factor,defectLift_pderiv_zero,clearMoment6_first]

theorem defectMoment8_clock_factor :
    ∃ Q : Poly, defectLift clearMoment8=X Coord.U*Q := by
  apply clock_factor_of_zero
  intro r z
  rw [defectLift_eval]
  simpa using clearMoment8_zero z

def defectMoment8Core : Poly := defectMoment8_clock_factor.choose

theorem defectMoment8_factor :
    defectLift clearMoment8=X Coord.U*defectMoment8Core :=
  defectMoment8_clock_factor.choose_spec

theorem defectMoment8Core_zero (r z : ℂ) :
    eval (basePoint 0 r z) defectMoment8Core=12^9*3^8*(3*z-1) := by
  rw [clock_factor_first _ _ defectMoment8_factor,defectLift_pderiv_zero,clearMoment8_first]

theorem defectMoment10_clock_factor :
    ∃ Q : Poly, defectLift clearMoment10=X Coord.U*Q := by
  apply clock_factor_of_zero
  intro r z
  rw [defectLift_eval]
  simpa using clearMoment10_zero z

def defectMoment10Core : Poly := defectMoment10_clock_factor.choose

theorem defectMoment10_factor :
    defectLift clearMoment10=X Coord.U*defectMoment10Core :=
  defectMoment10_clock_factor.choose_spec

theorem defectMoment10Core_zero (r z : ℂ) :
    eval (basePoint 0 r z) defectMoment10Core=12^11*3^10*(3*z-1) := by
  rw [clock_factor_first _ _ defectMoment10_factor,defectLift_pderiv_zero,clearMoment10_first]

def kineticCross : Poly := defectMoment6Core*defectMoment10Core-defectMoment8Core^2

theorem kineticCross_clock_factor : ∃ Q : Poly, kineticCross=X Coord.U*Q := by
  apply clock_factor_of_zero
  intro r z
  simp only [kineticCross,map_sub,map_mul,map_pow,defectMoment6Core_zero,
    defectMoment8Core_zero,defectMoment10Core_zero]
  ring

def kineticCrossCore : Poly := kineticCross_clock_factor.choose

theorem kineticCross_factor : kineticCross=X Coord.U*kineticCrossCore :=
  kineticCross_clock_factor.choose_spec

def compactMinor : Poly :=
  -defectLift clearMoment2*kineticCrossCore+defectMoment4Core^2*defectMoment10Core-
    2*defectMoment4Core*defectMoment6Core*defectMoment8Core+defectMoment6Core^3

theorem compactMinor_factor : defectLift clearMinor=(X Coord.U)^3*compactMinor := by
  have hc : defectMoment6Core*defectMoment10Core-defectMoment8Core^2=
      X Coord.U*kineticCrossCore := kineticCross_factor
  simp only [clearMinor,map_add,map_sub,map_mul,map_neg,map_pow,map_ofNat,
    defectMoment4_factor,defectMoment6_factor,defectMoment8_factor,defectMoment10_factor,
    compactMinor]
  linear_combination -(defectLift clearMoment2*(X Coord.U)^2)*hc

theorem compactMinor_eval (h r z : ℂ) (hh : h≠0) :
    eval (basePoint h r z) compactMinor=
      h^18*eval (basePoint (9-r*h^2) h⁻¹ z) minor := by
  have he := congrArg (eval (basePoint h r z)) compactMinor_factor
  rw [defectLift_eval,clearMinor_eval _ _ _ hh] at he
  simp only [map_mul,map_pow,eval_X,basePoint] at he
  apply mul_left_cancel₀ (pow_ne_zero 3 hh)
  calc
    _ = h^21*eval (basePoint (9-r*h^2) h⁻¹ z) minor := he.symm
    _ = _ := by ring

end
end HTGeometry.ThetaRatioKineticContraction
