import GaloisForLFunctions.RHTower.ThetaCuspRatioQuadraticForceSecondCompletion
import GaloisForLFunctions.RHTower.ThetaCuspRatioQuadraticForceHighCoefficients
/-! Strict sign of the second-completion middle term. -/

namespace HTGeometry.ThetaCriticalBarrier
noncomputable section

theorem middleForce_neg_high {h v q : ℝ} (H : HighClockBox h v q) : middleForce h v q<0 := by
  have hv0 := H.v_lower
  have hv1 := H.v_upper
  have hq0 := H.q_lower
  have hq1 := H.q_upper
  have hT0 : 0≤9-v := by linarith only [hv1]
  have hT1 : 9-v≤9 := by linarith only [hv0]
  have hf := high_factor_bounds H
  have hfl := hf.1
  have hfu := hf.2
  have hf0 : 0≤forcingFactor v q := by linarith only [hf.1]
  have hm := high_m_bounds H
  have hml := hm.1
  have hmu := hm.2
  have hm0 : 0≤ -hFieldCore h v q := by linarith only [hm.1]
  have hmn : hFieldCore h v q≤0 := by linarith only [hm.1]
  have hmh := high_mh_bounds H
  have hmhl := hmh.1
  have hmhu := hmh.2
  have hmv := high_mv_nonpos H
  have hA := high_A_bounds H
  have hAh := high_Ah_nonneg H
  have hAv := high_Av_upper H
  have hD := high_D_upper H
  have hDh := high_Dh_lower H
  have hDv := high_Dv_bounds H
  have hDvl := hDv.1
  have hDvu := hDv.2
  have hDh0 : 0≤Dh h v := by linarith only [hDh]
  have hq2 : q^2≤1/6400 := by nlinarith only [hq0,hq1]
  have hfd : 217/480≤forcingFactor v q*Dh h v := by
    calc
      _ = (31/40:ℝ)*(7/12) := by norm_num
      _ ≤ _ := by gcongr
  have hqa : q*A h v q≤3/5 := by
    calc
      _ ≤ q*48 := mul_le_mul_of_nonneg_left hA.2 hq0
      _ ≤ (1/80:ℝ)*48 := by gcongr
      _ = _ := by norm_num
  have hcf : 161/480≤forcingFactor v q*Dh h v-(7/36)*q*A h v q+(7/18)*(9-v)*q := by
    have hp : 0≤(9-v)*q := mul_nonneg hT0 hq0
    nlinarith only [hfd,hqa,hp]
  have hcf0 : 0≤forcingFactor v q*Dh h v-(7/36)*q*A h v q+(7/18)*(9-v)*q := by
    linarith only [hcf]
  have hmain : hFieldCore h v q*(forcingFactor v q*Dh h v-(7/36)*q*A h v q+(7/18)*(9-v)*q)
      ≤ -(153/64:ℝ)*(161/480) := by
    have hp : (153/64:ℝ)*(161/480)≤
        (-hFieldCore h v q)*(forcingFactor v q*Dh h v-(7/36)*q*A h v q+(7/18)*(9-v)*q) := by
      gcongr
    nlinarith only [hp]
  have hn1 : forcingFactor v q*hFieldCore h v q*q^2*Ah h v q≤0 := by
    have hp : 0≤forcingFactor v q*q^2*Ah h v q := by positivity
    have hn := mul_nonpos_of_nonneg_of_nonpos hp hmn
    nlinarith only [hn]
  have hn2 : (7/18)*v*(9-v)*q*coreDerivativeV h q≤0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hmv
  have hp1 : (7/216)*v*q*hFieldCore h v q*coreDerivativeH h v q≤
      (7/216:ℝ)*9*(1/80)*(13/4)*9 := by
    calc
      _ = (7/216)*v*q*((-hFieldCore h v q)*(-coreDerivativeH h v q)) := by ring
      _ ≤ (7/216:ℝ)*9*(1/80)*((13/4)*9) := by gcongr
      _ = _ := by ring
  have hp2 : 12*(9-v)*forcingFactor v q*Dv h≤12*9*1*(19/25920:ℝ) := by gcongr
  have hp3 : 12*(9-v)*forcingFactor v q*q^2*Av h v q≤12*9*1*(1/6400)*(25/4:ℝ) := by
    calc
      _ ≤ 12*(9-v)*forcingFactor v q*q^2*(25/4) :=
        mul_le_mul_of_nonneg_left hAv (by positivity)
      _ ≤ _ := by gcongr
  have hp4 : 24*(9-v)*q^2≤24*9*(1/6400:ℝ) := by gcongr
  have hp5 : 24*(9-v)*q*D h v≤24*9*(1/80)*(1/30:ℝ) := by
    calc
      _ ≤ 24*(9-v)*q*(1/30) := mul_le_mul_of_nonneg_left hD (by positivity)
      _ ≤ _ := by gcongr
  rw [middleForce_split]
  linarith only [hmain,hn1,hn2,hp1,hp2,hp3,hp4,hp5]

end
end HTGeometry.ThetaCriticalBarrier
