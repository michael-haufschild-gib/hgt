import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioQuadraticForceHighBounds
/-! Coefficient bounds used by the high-clock forcing cancellation. -/

namespace HTGeometry.ThetaCriticalBarrier
noncomputable section

theorem high_coefficient_param_bound {h v q s : ℝ} (H : HighClockBox h v q) (hs : s≤9) :
    5+(2/9)*h*(3-h)+(2/3)*(1+h/3)*s*(q+b h)+
      (7/108)*h*(1+h/3)*s≤25/4 := by
  have hh0 : 0≤h := by linarith only [H.h_lower]
  have hh1 := H.h_upper
  obtain ⟨hb0,hb1⟩ := high_b_bounds H
  have hq0 := H.q_lower
  have hq1 := H.q_upper
  have h3 : 0≤3-h := by linarith only [hh1]
  have h3b : 3-h≤9/4 := by linarith only [H.h_lower]
  have hfactor : 1+h/3≤19/15 := by linarith only [hh1]
  have hsum : q+b h≤1/80+1/96 := add_le_add hq1 hb1
  have hp1 : (2/9)*h*(3-h)≤2/5 := by
    calc
      _ ≤ (2/9:ℝ)*(4/5)*(9/4) := by gcongr
      _ = _ := by norm_num
  have hp2 : (2/3)*(1+h/3)*s*(q+b h)≤1/5 := by
    calc
      _ = ((2/3)*(1+h/3)*(q+b h))*s := by ring
      _ ≤ ((2/3)*(1+h/3)*(q+b h))*9 :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ ((2/3:ℝ)*(19/15)*(1/80+1/96))*9 := by gcongr
      _ ≤ _ := by norm_num
  have hp3 : (7/108)*h*(1+h/3)*s≤3/5 := by
    calc
      _ ≤ (7/108)*h*(1+h/3)*9 := mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ (7/108:ℝ)*(4/5)*(19/15)*9 := by gcongr
      _ ≤ _ := by norm_num
  linarith only [hp1,hp2,hp3]

theorem high_A_bounds {h v q : ℝ} (H : HighClockBox h v q) :
    A h v q≤(25/4)*v ∧ A h v q≤48 := by
  have ht9 : 9-v≤9 := by linarith only [H.v_lower]
  have hb := high_coefficient_param_bound H ht9
  have he : A h v q= -9+v*(5+(2/9)*h*(3-h)+
      (2/3)*(1+h/3)*(9-v)*(q+b h)+(7/108)*h*(1+h/3)*(9-v)) := by
    unfold A
    ring
  have hm := mul_le_mul_of_nonneg_left hb H.v_lower
  rw [he]
  constructor <;> nlinarith only [hm,H.v_upper]

theorem high_Ah_nonneg {h v q : ℝ} (H : HighClockBox h v q) : 0≤Ah h v q := by
  have hh0 : 0≤h := by linarith only [H.h_lower]
  have hv0 := H.v_lower
  have hq0 := H.q_lower
  have hT : 0≤9-v := by linarith only [H.v_upper]
  have hh3 : 0≤3-2*h := by linarith only [H.h_upper]
  have hb := (high_b_bounds H).1
  unfold Ah
  positivity

theorem high_Av_upper {h v q : ℝ} (H : HighClockBox h v q) : Av h v q≤25/4 := by
  have he := high_coefficient_param_bound H (show 9-2*v≤9 by linarith only [H.v_lower])
  unfold Av
  convert he using 1 <;> ring

theorem high_D_upper {h v q : ℝ} (H : HighClockBox h v q) : D h v≤1/30 := by
  have hh0 : 0≤h := by linarith only [H.h_lower]
  have hh1 := H.h_upper
  have hv0 := H.v_lower
  have hv1 := H.v_upper
  obtain ⟨hb0,hb1⟩ := high_b_bounds H
  have hs : h^2≤16/25 := by nlinarith only [hh0,hh1]
  have hf : 1+h/3≤19/15 := by linarith only [hh1]
  have hp : v*(1+h/3)*b h/18≤9*(19/15)*(1/96)/18 := by gcongr
  unfold D
  linarith only [hs,hh1,hp]

theorem high_Dh_lower {h v q : ℝ} (H : HighClockBox h v q) : 7/12≤Dh h v := by
  have hh0 : 0≤h := by linarith only [H.h_lower]
  have hh1 := H.h_upper
  have hv0 := H.v_lower
  have hv1 := H.v_upper
  have hp : v*(5/1296+7*h/1944)≤9*(5/1296+7*(4/5)/1944) := by gcongr
  unfold Dh
  linarith only [hp,H.h_lower]

theorem high_Dv_bounds {h v q : ℝ} (H : HighClockBox h v q) : 0≤Dv h ∧ Dv h≤19/25920 := by
  have hh0 : 0≤h := by linarith only [H.h_lower]
  have hh1 := H.h_upper
  obtain ⟨hb0,hb1⟩ := high_b_bounds H
  have hf : 1+h/3≤19/15 := by linarith only [hh1]
  unfold Dv
  constructor
  · positivity
  · calc
      _ ≤ (19/15:ℝ)*(1/96)/18 := by gcongr
      _ = _ := by norm_num

end
end HTGeometry.ThetaCriticalBarrier
