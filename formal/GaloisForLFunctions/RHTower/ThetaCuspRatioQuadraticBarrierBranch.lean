import GaloisForLFunctions.RHTower.ThetaCuspRatioQuadraticBarrierAlgebra

namespace HTGeometry.ThetaCriticalBarrier
noncomputable section

theorem failure_ratio_bound {h v q : ℝ} (hh : h<1) (hq : 0≤q)
    (hy : quadraticError h v q≤0) (hg : (9-v)*q<h) : q≤b h/(1-h) := by
  apply (le_div_iff₀ (sub_pos.mpr hh)).2
  have hm := mul_nonneg hq (sub_nonneg.mpr hg.le)
  unfold quadraticError at hy
  nlinarith only [hy,hm]

theorem cubic_barrier_max {h : ℝ} (hh : 0≤h) : h^2*b h≤4/441 := by
  have he : (4/441:ℝ)-h^2*b h=(h-4/7)^2*(7*h+2)/72 := by unfold b; ring
  have hp : 0≤(h-4/7)^2*(7*h+2)/72 := by positivity
  linarith only [he,hp]

/-- The kinetic constraint selects the small quadratic branch throughout the failure region. -/
theorem failure_factor_pos {h v q : ℝ} (hh0 : 0≤h) (hh : h≤4/5)
    (hv0 : 0<v) (hv : v≤9) (hq : 0≤q)
    (hy : quadraticError h v q≤0) (hg : (9-v)*q<h)
    (hk : 9-v≤(361/25)*h^2) : 0<1-2*(9-v)*q := by
  by_cases hqz : q=0
  · rw [hqz]
    norm_num
  have hqp : 0<q := lt_of_le_of_ne hq (Ne.symm hqz)
  have hh1 : h<1 := by linarith
  have hd : 0<1-h := sub_pos.mpr hh1
  have hb0 := b_nonneg hh
  have hqb := failure_ratio_bound hh1 hq hy hg
  have hqb' : q*(1-h)≤b h := (le_div_iff₀ hd).mp hqb
  have hT : 0≤9-v := by linarith
  by_cases hh2 : h≤2/3
  · have hm : ((9-v)*q)*(1-h)≤(361/25)*(4/441) := by
      calc
        _ = (9-v)*(q*(1-h)) := by ring
        _ ≤ (9-v)*b h := mul_le_mul_of_nonneg_left hqb' hT
        _ ≤ ((361/25)*h^2)*b h := mul_le_mul_of_nonneg_right hk hb0
        _ = (361/25)*(h^2*b h) := by ring
        _ ≤ (361/25)*(4/441) := mul_le_mul_of_nonneg_left (cubic_barrier_max hh0) (by norm_num)
    have hprod : 0≤(9-v)*q := mul_nonneg hT hq
    have hl := mul_le_mul_of_nonneg_left (show (1/3:ℝ)≤1-h by linarith) hprod
    nlinarith only [hm,hl]
  · have hb : 18*b h≤1-h := by unfold b; linarith
    have hqh : 18*q≤1 := by
      have hn : (18*q-1)*(1-h)≤0 := by nlinarith only [hqb',hb]
      nlinarith only [hn,hd]
    have hvq : (9-v)*q<9*q := mul_lt_mul_of_pos_right (by linarith) hqp
    linarith

end
end HTGeometry.ThetaCriticalBarrier
namespace HTGeometry.ThetaCriticalBarrier
noncomputable section

theorem failure_small_branch {h v q : ℝ} (hh0 : 0≤h) (hh : h≤4/5)
    (hv0 : 0<v) (hv : v≤9) (hq : 0≤q)
    (hy : quadraticError h v q≤0) (hg : (9-v)*q<h)
    (hk : 9-v≤(361/25)*h^2) : (9-v)*q<1/6 := by
  have hf := failure_factor_pos hh0 hh hv0 hv hq hy hg hk
  have hb0 := b_nonneg hh
  have hT : 0≤9-v := by linarith
  have hp : (9-v)*b h≤(361/25)*(4/441) := by
    calc
      _ ≤ ((361/25)*h^2)*b h := mul_le_mul_of_nonneg_right hk hb0
      _ = (361/25)*(h^2*b h) := by ring
      _ ≤ (361/25)*(4/441) := mul_le_mul_of_nonneg_left (cubic_barrier_max hh0) (by norm_num)
  have hmul := mul_nonpos_of_nonneg_of_nonpos hT hy
  unfold quadraticError at hmul
  by_contra hn
  have hlow : 1/6≤(9-v)*q := le_of_not_gt hn
  have hproduct := mul_nonneg (sub_nonneg.mpr hlow)
    (show 0≤(5/6:ℝ)-(9-v)*q by linarith)
  nlinarith only [hp,hmul,hproduct]

end
end HTGeometry.ThetaCriticalBarrier
