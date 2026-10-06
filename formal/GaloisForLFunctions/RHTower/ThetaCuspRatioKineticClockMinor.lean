import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticClockMoments
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def clearMinor : Poly :=
  -clearMoment2*clearMoment6*clearMoment10+clearMoment2*clearMoment8^2+
    clearMoment4^2*clearMoment10-2*clearMoment4*clearMoment6*clearMoment8+
    clearMoment6^3

theorem clearMinor_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMinor=h^21*eval (basePoint v h⁻¹ z) minor := by
  simp only [clearMinor,minor,map_sub,map_add,map_neg,map_mul,map_pow,map_ofNat,
    clearMoment2_eval h v z hh,clearMoment4_eval h v z hh,clearMoment6_eval h v z hh,clearMoment8_eval h v z hh,
    clearMoment10_eval h v z hh]
  ring

theorem clockLie_eval_of_flow (d : ℕ) (P : Poly) (h v z : ℂ) :
    eval (basePoint h v z) (clockLie P)=
      eval (basePoint h v z) (clockFlow d P)-
        (d:ℂ)*h^2*(12+4*h)*v*z*eval (basePoint h v z) P := by
  simp only [clockFlow,map_add,map_mul,map_pow,eval_C,eval_X,basePoint,map_ofNat]
  ring

theorem clearMinor_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 21 clearMinor)=
      h^23*eval (basePoint v h⁻¹ z) (squareLie minor) := by
  have h2 := clockLie_eval_of_flow 3 clearMoment2 h v z
  have h4 := clockLie_eval_of_flow 5 clearMoment4 h v z
  have h6 := clockLie_eval_of_flow 7 clearMoment6 h v z
  have h8 := clockLie_eval_of_flow 9 clearMoment8 h v z
  have h10 := clockLie_eval_of_flow 11 clearMoment10 h v z
  rw [clearMoment2_flow h v z hh] at h2
  rw [clearMoment4_flow h v z hh] at h4
  rw [clearMoment6_flow h v z hh] at h6
  rw [clearMoment8_flow h v z hh] at h8
  rw [clearMoment10_flow h v z hh] at h10
  have hc (f : Coord → Poly) : flow f (2:Poly)=0 := by
    change flow f (C (2:ℂ))=0
    exact flow_C f 2
  unfold clockFlow
  simp only [clearMinor,clockLie,squareLie,minor,flow_add,flow_sub75,
    flow_neg75,flow_mul,flow_pow75,hc]
  simp only [map_add,map_sub,map_mul,map_neg,map_pow,map_ofNat,map_natCast,
    eval_X,basePoint]
  simp only [clockLie] at h2 h4 h6 h8 h10
  rw [h2,h4,h6,h8,h10]
  simp only [clearMoment2_eval h v z hh,clearMoment4_eval h v z hh,clearMoment6_eval h v z hh,
    clearMoment8_eval h v z hh,clearMoment10_eval h v z hh]
  norm_num
  ring

end
end HTGeometry.ThetaRatioKineticContraction
