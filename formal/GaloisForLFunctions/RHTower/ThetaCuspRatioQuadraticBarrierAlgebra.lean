import GaloisForLFunctions.RHTower.ThetaCuspRatioCriticalBarrierAlgebra

namespace HTGeometry.ThetaCriticalBarrier
noncomputable section

def quadraticError (h v q : ℝ) : ℝ := q-(9-v)*q^2-b h
def quadraticField (h v q : ℝ) : ℝ :=
  6*(1-2*(9-v)*q)*G h v q+(7/36)*(9-v)*q*fieldH h v q+12*v*(9-v)*q^2

def quadraticBoundaryCore (h v q : ℝ) : ℝ :=
  (1-2*(9-v)*q)*(D h v+q^2*A h v q)+(7/216)*q*fieldH h v q+2*v*q^2

theorem quadraticField_split (h v q : ℝ) :
    quadraticField h v q=6*(9-v)*quadraticBoundaryCore h v q+
      6*(1-2*(9-v)*q)*A h v q*quadraticError h v q := by
  rw [quadraticField,G_split]
  unfold quadraticBoundaryCore quadraticError
  ring

end
end HTGeometry.ThetaCriticalBarrier
namespace HTGeometry.ThetaCriticalBarrier
noncomputable section

def qField (h v q : ℝ) : ℝ := 6*G h v q-(7/72)*fieldH h v q

def qQuadraticRate (h v q : ℝ) : ℝ := (1-2*(9-v)*q)*A h v q+2*v

/-- Exact normalized-defect evolution, stated after multiplying by its positive T denominator. -/
theorem normalized_quadratic_field (h v q : ℝ) :
    quadraticField h v q+12*v*quadraticError h v q=
      6*(qQuadraticRate h v q*quadraticError h v q+(9-v)*quadraticBoundaryCore h v q) := by
  rw [quadraticField_split]
  unfold qQuadraticRate
  ring

theorem quadraticBoundaryCore_seam (h q : ℝ) :
    quadraticBoundaryCore h 0 q=(1-18*q)*(D h 0-9*q^2) := by
  unfold quadraticBoundaryCore D A b fieldH
  ring

theorem qField_seam (h q : ℝ) :
    qField h 0 q=54*(D h 0-9*q^2-quadraticError h 0 q) := by
  unfold qField G D quadraticError b fieldH
  ring

/-- At the zero-drift face, the forcing's directional derivative has an exact sign decomposition. -/
theorem quadratic_forcing_seam (h q : ℝ) :
    (-18*(D h 0-9*q^2)-18*q*(1-18*q))*qField h 0 q=
      -972*(D h 0-9*q^2)*((D h 0-9*q^2)-quadraticError h 0 q+q*(1-18*q))+
        972*q*(1-18*q)*quadraticError h 0 q := by
  rw [qField_seam]
  ring

theorem quadratic_forcing_seam_nonpos {h q : ℝ} (hq : 0≤q) (hb : q<1/18)
    (hy : quadraticError h 0 q≤0) (hR : quadraticBoundaryCore h 0 q=0) :
    (-18*(D h 0-9*q^2)-18*q*(1-18*q))*qField h 0 q≤0 := by
  have hf : 0<1-18*q := by linarith
  rw [quadraticBoundaryCore_seam] at hR
  have hd : D h 0-9*q^2=0 := (mul_eq_zero.mp hR).resolve_left hf.ne'
  rw [quadratic_forcing_seam,hd]
  have hc : 0≤972*q*(1-18*q) := by positivity
  simpa using mul_nonpos_of_nonneg_of_nonpos hc hy

/-- The limiting forcing has a strictly negative first clock jet. -/
def quadratic_tail_remainder (h : ℝ) : ℝ :=
  4*h^2/27+31*h/72-5/12+(1+h/3)*b h/2+
    (b h)^2*(54+6*h-2*h^2)-(7/18)*b h*h^2*(3+h)

theorem quadraticBoundaryCore_tail (h : ℝ) :
    quadraticBoundaryCore h 9 (b h)=quadratic_tail_remainder h := by
  unfold quadraticBoundaryCore quadratic_tail_remainder D A fieldH
  ring

end
end HTGeometry.ThetaCriticalBarrier
