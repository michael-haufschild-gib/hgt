import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioQuadraticForceCompletion
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioQuadraticForceHighBounds
/-! Second exact completion of the nonlinear source forcing. -/

namespace HTGeometry.ThetaCriticalBarrier
noncomputable section

def forceCorrection (h v q : ℝ) : ℝ := -(7/72)*hFieldCore h v q-12*(9-v)*q^2
def middleForce (h v q : ℝ) : ℝ :=
  hFieldCore h v q*Rh h v q+12*(9-v)*Rv h v q+2*q*A h v q*forceCorrection h v q

theorem remainder_second_completion (h v q : ℝ) :
    forcingFactor v q*completedForcingRemainder h v q=
      (forcingFactor v q)^2*middleForce h v q+
        qDerivativeRemainder h v q*(v*forceCorrection h v q+
          6*forcingFactor v q*A h v q*quadraticError h v q)-
        2*(9-v)*quadraticBoundaryCore h v q*forceCorrection h v q := by
  have he := Rq_forcing_split h v q
  unfold completedForcingRemainder forcingRemainder middleForce forceCorrection
  linear_combination (-(7/72)*hFieldCore h v q-12*(9-v)*q^2)*he

theorem qDerivativeRemainder_simple (h v q : ℝ) :
    qDerivativeRemainder h v q=
      -(7/162)*h*(3+h)*(h-2*((9-v)*q)*(1-(9-v)*q))+
        4*q*(1-(9-v)*q)+
          (forcingFactor v q)^2*q^2*((2/3)*(1+h/3)*(9-v)) := by
  unfold qDerivativeRemainder hFieldCore forcingFactor
  ring

theorem middleForce_split (h v q : ℝ) :
    middleForce h v q=
      hFieldCore h v q*(forcingFactor v q*Dh h v-(7/36)*q*A h v q+(7/18)*(9-v)*q)+
      forcingFactor v q*hFieldCore h v q*q^2*Ah h v q+
      (7/216)*v*q*hFieldCore h v q*coreDerivativeH h v q+
      12*(9-v)*forcingFactor v q*Dv h+
      12*(9-v)*forcingFactor v q*q^2*Av h v q+
      (7/18)*v*(9-v)*q*coreDerivativeV h q+
      24*(9-v)*q^2+24*(9-v)*q*D h v := by
  unfold middleForce forceCorrection Rh Rv Hhh Hhv coreDerivativeH coreDerivativeV
    hFieldCore
  ring

end
end HTGeometry.ThetaCriticalBarrier
