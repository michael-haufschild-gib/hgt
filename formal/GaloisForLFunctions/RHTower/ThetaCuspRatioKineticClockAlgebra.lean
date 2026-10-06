import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticClockMoment2
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Dynamics
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

theorem clockFlow_add (d : ℕ) (P Q : Poly) :
    clockFlow d (P+Q)=clockFlow d P+clockFlow d Q := by
  simp only [clockFlow,clockLie,flow_add]
  ring

theorem clockFlow_sub (d : ℕ) (P Q : Poly) :
    clockFlow d (P-Q)=clockFlow d P-clockFlow d Q := by
  simp only [clockFlow,clockLie,flow_sub75]
  ring

theorem clockFlow_neg (d : ℕ) (P : Poly) :
    clockFlow d (-P)= -clockFlow d P := by
  simp only [clockFlow,clockLie,flow_neg75]
  ring

theorem clockFlow_mul (d e : ℕ) (P Q : Poly) :
    clockFlow (d+e) (P*Q)=clockFlow d P*Q+P*clockFlow e Q := by
  simp only [clockFlow,clockLie,flow_mul,Nat.cast_add,map_add]
  ring

theorem clockFlow_C_mul (d : ℕ) (c : ℂ) (P : Poly) :
    clockFlow d (C c*P)=C c*clockFlow d P := by
  simp only [clockFlow,clockLie,flow_mul,flow_C,zero_mul,zero_add]
  ring

end
end HTGeometry.ThetaRatioKineticContraction
