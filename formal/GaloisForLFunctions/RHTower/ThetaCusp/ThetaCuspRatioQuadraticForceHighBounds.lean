import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioQuadraticForceDifferentials
/-! The high-clock failure box and its field bounds. -/

namespace HTGeometry.ThetaCriticalBarrier
noncomputable section

structure HighClockBox (h v q : ℝ) : Prop where
  h_lower : 3/4≤h
  h_upper : h≤4/5
  v_lower : 0≤v
  v_upper : v≤9
  q_lower : 0≤q
  q_upper : q≤1/80

def coreDerivativeH (h v q : ℝ) : ℝ :=
  -(4/3)*((3+2*h)*(h-q*(9-v))+h*(3+h))
def coreDerivativeV (h q : ℝ) : ℝ := -(4/3)*h*(3+h)*q

theorem high_b_bounds {h v q : ℝ} (H : HighClockBox h v q) : 0≤b h ∧ b h≤1/96 := by
  constructor
  · exact b_nonneg H.h_upper
  · unfold b; linarith only [H.h_lower]

theorem high_w_bounds {h v q : ℝ} (H : HighClockBox h v q) :
    0≤(9-v)*q ∧ (9-v)*q≤9/80 := by
  have ht : 0≤9-v := by linarith only [H.v_upper]
  have ht9 : 9-v≤9 := by linarith only [H.v_lower]
  have hq0 := H.q_lower
  have hq1 := H.q_upper
  constructor
  · exact mul_nonneg ht H.q_lower
  · calc
      _ ≤ (9:ℝ)*(1/80) := by gcongr
      _ = _ := by norm_num

theorem high_factor_bounds {h v q : ℝ} (H : HighClockBox h v q) :
    31/40≤forcingFactor v q ∧ forcingFactor v q≤1 := by
  have hw := high_w_bounds H
  unfold forcingFactor
  constructor <;> linarith only [hw.1,hw.2]

theorem high_m_bounds {h v q : ℝ} (H : HighClockBox h v q) :
    153/64≤ -hFieldCore h v q ∧ -hFieldCore h v q≤13/4 := by
  have hw := high_w_bounds H
  have hh0 : 0≤h := by linarith only [H.h_lower]
  have hgap : 51/80≤h-q*(9-v) := by nlinarith only [H.h_lower,hw.2]
  have hgap0 : 0≤h-q*(9-v) := by linarith only [hgap]
  have hgap1 : h-q*(9-v)≤4/5 := by nlinarith only [H.h_upper,hw.1]
  have hlo : 153/64≤(4/3)*h*(3+h)*(h-q*(9-v)) := by
    calc
      _ = (4/3:ℝ)*(3/4)*(15/4)*(51/80) := by norm_num
      _ ≤ _ := by gcongr <;> linarith only [H.h_lower]
  have hhi : (4/3)*h*(3+h)*(h-q*(9-v))≤(4/3:ℝ)*(4/5)*(19/5)*(4/5) := by
    gcongr
    · exact H.h_upper
    · linarith only [H.h_upper]
  unfold hFieldCore
  constructor <;> nlinarith only [hlo,hhi]

theorem high_mh_bounds {h v q : ℝ} (H : HighClockBox h v q) :
    0≤ -coreDerivativeH h v q ∧ -coreDerivativeH h v q≤9 := by
  have hw := high_w_bounds H
  have hh0 : 0≤h := by linarith only [H.h_lower]
  have hgap0 : 0≤h-q*(9-v) := by nlinarith only [H.h_lower,hw.2]
  have hgap1 : h-q*(9-v)≤4/5 := by nlinarith only [H.h_upper,hw.1]
  have hbound : (3+2*h)*(h-q*(9-v))+h*(3+h)≤(23/5:ℝ)*(4/5)+(4/5)*(19/5) := by
    gcongr
    · linarith only [H.h_upper]
    · exact H.h_upper
    · linarith only [H.h_upper]
  unfold coreDerivativeH
  constructor
  · have hp : 0≤(4/3:ℝ)*((3+2*h)*(h-q*(9-v))+h*(3+h)) := by positivity
    linarith only [hp]
  · nlinarith only [hbound]

theorem high_mv_nonpos {h v q : ℝ} (H : HighClockBox h v q) : coreDerivativeV h q≤0 := by
  have hh0 : 0≤h := by linarith only [H.h_lower]
  have hq := H.q_lower
  have hp : 0≤(4/3:ℝ)*h*(3+h)*q := by positivity
  unfold coreDerivativeV
  linarith only [hp]

end
end HTGeometry.ThetaCriticalBarrier
