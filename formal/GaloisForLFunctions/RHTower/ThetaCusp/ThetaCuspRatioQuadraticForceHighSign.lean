import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioQuadraticForceMiddleSign
/-! Strict downward forcing crossing on the high-clock failure region. -/

namespace HTGeometry.ThetaCriticalBarrier
noncomputable section

theorem qDerivativeRemainder_neg_high {h v q : ℝ} (H : HighClockBox h v q)
    (hy : quadraticError h v q≤0) : qDerivativeRemainder h v q<0 := by
  have hh0 : 0≤h := by linarith only [H.h_lower]
  have hh1 := H.h_upper
  have hq0 := H.q_lower
  have hq1 := H.q_upper
  have hT0 : 0≤9-v := by linarith only [H.v_upper]
  have hT1 : 9-v≤9 := by linarith only [H.v_lower]
  have hb := high_b_bounds H
  have hbl := hb.1
  have hbu := hb.2
  have hf := high_factor_bounds H
  have hf0 : 0≤forcingFactor v q := by linarith only [hf.1]
  have hf2 : (forcingFactor v q)^2≤1 := by nlinarith only [hf.1,hf.2]
  have hq2 : q^2≤1/6400 := by nlinarith only [hq0,hq1]
  have hqf : q*(1-(9-v)*q)≤b h := by
    unfold quadraticError at hy
    nlinarith only [hy]
  have hwb : ((9-v)*q)*(1-(9-v)*q)≤(9-v)*b h := by
    have he := mul_le_mul_of_nonneg_left hqf hT0
    nlinarith only [he]
  have hTb : (9-v)*b h≤3/32 := by
    calc
      _ ≤ (9:ℝ)*(1/96) := by gcongr
      _ = _ := by norm_num
  have hgap : 9/16≤h-2*((9-v)*q)*(1-(9-v)*q) := by
    linarith only [H.h_lower,hwb,hTb]
  have hgap0 : 0≤h-2*((9-v)*q)*(1-(9-v)*q) := by linarith only [hgap]
  have hmain : 35/512≤(7/162)*h*(3+h)*(h-2*((9-v)*q)*(1-(9-v)*q)) := by
    calc
      _ = (7/162:ℝ)*(3/4)*(15/4)*(9/16) := by norm_num
      _ ≤ _ := by gcongr <;> linarith only [H.h_lower]
  have hlast : (forcingFactor v q)^2*q^2*((2/3)*(1+h/3)*(9-v))≤19/16000 := by
    calc
      _ ≤ 1*(1/6400)*((2/3:ℝ)*(19/15)*9) := by
        gcongr
        linarith only [hh1]
      _ = _ := by norm_num
  rw [qDerivativeRemainder_simple]
  nlinarith only [hmain,hlast,hqf,hb.2]

theorem completed_bracket_nonneg_high {h v q : ℝ} (H : HighClockBox h v q)
    (hy : quadraticError h v q≤0) (hy0 : -(9-v)*q^2≤quadraticError h v q) :
    0≤v*forceCorrection h v q+6*forcingFactor v q*A h v q*quadraticError h v q := by
  have hv0 := H.v_lower
  have hq0 := H.q_lower
  have hT0 : 0≤9-v := by linarith only [H.v_upper]
  have hT1 : 9-v≤9 := by linarith only [H.v_lower]
  have hq2 : q^2≤1/6400 := by nlinarith only [H.q_lower,H.q_upper]
  have hf := high_factor_bounds H
  have hf0 : 0≤forcingFactor v q := by linarith only [hf.1]
  have hm := high_m_bounds H
  have hA := (high_A_bounds H).1
  have hAy := mul_le_mul_of_nonpos_right hA hy
  have hyv := mul_le_mul_of_nonneg_left hy0 (show 0≤(25/4:ℝ)*v by positivity)
  have hbase : -(25/4)*v*(9-v)*q^2≤A h v q*quadraticError h v q := by
    nlinarith only [hAy,hyv]
  have hprod := mul_le_mul_of_nonneg_left hbase (show 0≤6*forcingFactor v q by positivity)
  have hneg : -(75/2:ℝ)*v*(9-v)*q^2≤0 := by
    have hp : 0≤(75/2:ℝ)*v*(9-v)*q^2 := by positivity
    linarith only [hp]
  have hfixed := mul_le_mul_of_nonpos_right hf.2 hneg
  have hterm : -(75/2)*v*(9-v)*q^2≤6*forcingFactor v q*A h v q*quadraticError h v q := by
    nlinarith only [hprod,hfixed]
  have htq : (9-v)*q^2≤9/6400 := by
    calc
      _ ≤ (9:ℝ)*(1/6400) := by gcongr
      _ = _ := by norm_num
  have hi : 0≤-(7/72)*hFieldCore h v q-(99/2)*(9-v)*q^2 := by
    linarith only [hm.1,htq]
  have hp := mul_nonneg hv0 hi
  unfold forceCorrection
  nlinarith only [hp,hterm]

theorem completedForcingRemainder_neg_high {h v q : ℝ} (H : HighClockBox h v q)
    (hy : quadraticError h v q≤0) (hy0 : -(9-v)*q^2≤quadraticError h v q)
    (hR : quadraticBoundaryCore h v q=0) : completedForcingRemainder h v q<0 := by
  have hf := high_factor_bounds H
  have hf0 : 0<forcingFactor v q := by linarith only [hf.1]
  have hm := middleForce_neg_high H
  have hl := qDerivativeRemainder_neg_high H hy
  have hj := completed_bracket_nonneg_high H hy hy0
  have he := remainder_second_completion h v q
  rw [hR,mul_zero,zero_mul,sub_zero] at he
  have hn1 := mul_neg_of_pos_of_neg (show 0<(forcingFactor v q)^2 by positivity) hm
  have hn2 := mul_nonpos_of_nonpos_of_nonneg hl.le hj
  have hn : forcingFactor v q*completedForcingRemainder h v q<0 := by
    linarith only [he,hn1,hn2]
  by_contra hnot
  have hp := mul_nonneg hf0.le (le_of_not_gt hnot)
  linarith only [hn,hp]

theorem forcingDrift_neg_high {h v q : ℝ} (H : HighClockBox h v q) (hv : 0<v)
    (hy : quadraticError h v q≤0) (hy0 : -(9-v)*q^2≤quadraticError h v q)
    (hR : quadraticBoundaryCore h v q=0) : forcingDrift h v q<0 := by
  have hf : 0<forcingFactor v q := by linarith only [(high_factor_bounds H).1]
  exact forcingDrift_neg_of_completed hv H.q_lower hf hy hR
    (completedForcingRemainder_neg_high H hy hy0 hR)

end
end HTGeometry.ThetaCriticalBarrier
