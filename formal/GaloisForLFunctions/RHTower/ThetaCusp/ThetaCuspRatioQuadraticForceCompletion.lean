import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioQuadraticForceDifferentials
/-! First completion of the nonlinear source forcing. -/

namespace HTGeometry.ThetaCriticalBarrier
noncomputable section

def qDerivativeRemainder (h v q : ℝ) : ℝ :=
  (forcingFactor v q)^2*q^2*((2/3)*(1+h/3)*(9-v))+
    2*(9-v)*((7/216)*q*hFieldCore h v q+2*q^2)+
    (7/216)*forcingFactor v q*(hFieldCore h v q+q*(4/3)*h*(3+h)*(9-v))+
    4*q*forcingFactor v q

theorem Rq_forcing_split (h v q : ℝ) :
    forcingFactor v q*Rq h v q= -2*(9-v)*quadraticBoundaryCore h v q+
      2*q*(forcingFactor v q)^2*A h v q+v*qDerivativeRemainder h v q := by
  unfold Rq quadraticBoundaryCore Aq Hhq qDerivativeRemainder
  rw [hFieldCore_eq]
  unfold forcingFactor
  ring

def forcingDrift (h v q : ℝ) : ℝ :=
  Rh h v q*fieldH h v q+Rv h v q*fieldV v+Rq h v q*qField h v q

def completedForcingRemainder (h v q : ℝ) : ℝ :=
  forcingRemainder h v q (Rh h v q) (Rv h v q) (Rq h v q)+
    6*A h v q*qDerivativeRemainder h v q*quadraticError h v q

/-- Completing the error contribution exposes a square, so its sign is unconditional. -/
theorem completed_forcing_split (h v q : ℝ) :
    forcingFactor v q*forcingDrift h v q=
      (6*(9-v)*Rq h v q-12*A h v q*(9-v)*quadraticError h v q)*quadraticBoundaryCore h v q+
        12*q*(forcingFactor v q)^2*(A h v q)^2*quadraticError h v q+
          v*completedForcingRemainder h v q := by
  have he := forcing_direction_split h v q (Rh h v q) (Rv h v q) (Rq h v q)
  have hq := Rq_forcing_split h v q
  unfold forcingDrift completedForcingRemainder
  linear_combination he+6*A h v q*quadraticError h v q*hq

theorem forcingDrift_neg_of_completed {h v q : ℝ} (hv : 0<v) (hq : 0≤q)
    (hf : 0<forcingFactor v q) (hy : quadraticError h v q≤0)
    (hR : quadraticBoundaryCore h v q=0) (hK : completedForcingRemainder h v q<0) :
    forcingDrift h v q<0 := by
  have he := completed_forcing_split h v q
  rw [hR,mul_zero,zero_add] at he
  have hcoef : 0≤12*q*(forcingFactor v q)^2*(A h v q)^2 := by positivity
  have hyterm := mul_nonpos_of_nonneg_of_nonpos hcoef hy
  have hstrict := mul_neg_of_pos_of_neg hv hK
  have hn : forcingFactor v q*forcingDrift h v q<0 := by linarith only [he,hyterm,hstrict]
  by_contra hd
  have hp := mul_nonneg hf.le (le_of_not_gt hd)
  linarith only [hn,hp]

end
end HTGeometry.ThetaCriticalBarrier
