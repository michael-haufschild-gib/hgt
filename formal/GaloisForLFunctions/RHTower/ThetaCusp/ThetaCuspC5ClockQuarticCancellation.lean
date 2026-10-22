import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5OuterClockCurrent
/-! The quadratic clock relaxation makes the complete enriched constant-shape
current strictly negative. The retained rational quartic correction restores
strict positivity for every positive clock coordinate. This diagnoses a
failed relaxation; it makes no constant-shape assertion about the actual
theta source and does not close the remaining inner-source current sign. -/
namespace RHTower.ThetaCuspDefect
noncomputable section
theorem linearClockEnvelope_quartic_correction {z : ℝ} (hz : 0 ≤ z) :
    linearClockEnvelope z=1+z^2/3-z^4/(3*(15+3*z+z^2)) := by
  have hd : 15+3*z+z^2 ≠ 0 := by positivity
  unfold linearClockEnvelope
  field_simp [hd]
  ring

/-- The quadratic clock relaxation destroys even the complete enriched constant-shape sign. -/
theorem constantShape_quadraticClock_current_neg {Z : ℝ} (hZ : 0 < Z) :
    actionPowerCurrentKernel 16 Z 1 1 0 0 0 (1+6*Z)+
      Z^2/15*actionPowerCurrentKernel 36 Z 1 1 0 0 0 (1+6*Z)<0 := by
  have hid : actionPowerCurrentKernel 16 Z 1 1 0 0 0 (1+6*Z)+
      Z^2/15*actionPowerCurrentKernel 36 Z 1 1 0 0 0 (1+6*Z)=
      -(5968/75)*Z^2-(4464/125)*Z^3-(336/25)*Z^4-(1728/625)*Z^5 := by
    unfold actionPowerCurrentKernel actionPowerReserveKernel actionPowerFlowKernel
    ring
  rw [hid]
  have hp : 0 < (5968/75)*Z^2+(4464/125)*Z^3+(336/25)*Z^4+(1728/625)*Z^5 := by
    positivity
  linarith only [hp]

/-- Retaining the exact rational clock correction restores the full constant-shape sign. -/
theorem constantShape_linearClock_current_pos {z : ℝ} (hz : 0 < z) :
    actionPowerCurrentKernel 16 (z^2/18) 1 1 0 0 0 (linearClockEnvelope z)+
      (z^2/18)^2/15*
        actionPowerCurrentKernel 36 (z^2/18) 1 1 0 0 0 (linearClockEnvelope z)>0 := by
  let Z:=z^2/18
  let R16:=actionPowerReserveKernel 16 Z 1 1 0 0
  let R36:=actionPowerReserveKernel 36 Z 1 1 0 0
  let F16:=actionPowerFlowKernel 16 Z 1 1 0 0 0
  let F36:=actionPowerFlowKernel 36 Z 1 1 0 0 0
  let K16:=actionPowerCurrentKernel 16 Z 1 1 0 0 0 (linearClockEnvelope z)
  let K36:=actionPowerCurrentKernel 36 Z 1 1 0 0 0 (linearClockEnvelope z)
  have hZ : 0 < Z := by dsimp only [Z]; positivity
  have hR16 : 0 < R16 := by
    dsimp only [R16,actionPowerReserveKernel]
    ring_nf
    positivity
  have hR36 : 0 < R36 := by
    dsimp only [R36,actionPowerReserveKernel]
    ring_nf
    positivity
  have hP : 0 < 1+z^2/10+z^4/675 := by positivity
  have hid : K16=(constantInverseClockGrowth z-linearClockEnvelope z)*R16 := by
    dsimp only [K16,R16,Z]
    unfold actionPowerCurrentKernel actionPowerReserveKernel actionPowerFlowKernel
      constantInverseClockGrowth
    field_simp [hP.ne']
    ring
  have hK16 : 0 < K16 := by
    rw [hid]
    exact mul_pos (sub_pos.mpr (linearEnvelope_lt_constantInverseClockGrowth hz)) hR16
  have hcross : 0 < 4*R36*R16+F36*R16-F16*R36 := by
    dsimp only [R16,R36,F16,F36,actionPowerReserveKernel,actionPowerFlowKernel]
    ring_nf
    positivity
  have heq : K36*R16-K16*R36=4*R36*R16+F36*R16-F16*R36 := by
    dsimp only [K16,K36,actionPowerCurrentKernel,R16,R36,F16,F36]
    ring
  rw [←heq] at hcross
  have hmul:=mul_pos hK16 hR36
  have hK36 : 0 < K36 :=
    (mul_pos_iff_of_pos_right hR16).mp (by linarith only [hcross,hmul])
  exact add_pos hK16 (mul_pos (by positivity : 0<Z^2/15) hK36)

end
end RHTower.ThetaCuspDefect
