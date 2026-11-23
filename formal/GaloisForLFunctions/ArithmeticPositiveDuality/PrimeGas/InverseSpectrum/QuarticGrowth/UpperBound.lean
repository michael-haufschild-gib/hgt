import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.QuarticGrowth.ClockMasks

/-! # Sharp upper growth order for the fixed fourth-power estimate -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Finset Filter Topology

/-- The fourth-power coefficient changes from high-occupation to ground-state growth at five quarters. -/
def quarticClockOrder (σ : ℝ) : ℝ := max 1 (6-4*σ)

private theorem interpolated_weight {a T σ : ℝ} (ha : 0 < a) (hT : 0 < T) (hs : 1/2 ≤ σ) (hc : σ ≤ 5/4) :
    a^σ ≤ T^(1/2-σ)*a^(1/2:ℝ)+T^(5/4-σ)*a^(5/4:ℝ) := by
  have hx := mul_pos hT ha
  have he : (T*a)^σ ≤ (T*a)^(1/2:ℝ)+(T*a)^(5/4:ℝ) := by
    rcases le_total (T*a) 1 with hlo | hhi
    · exact (Real.rpow_le_rpow_of_exponent_ge hx hlo hs).trans (le_add_of_nonneg_right (Real.rpow_nonneg hx.le _))
    · exact (Real.rpow_le_rpow_of_exponent_le hhi hc).trans (le_add_of_nonneg_left (Real.rpow_nonneg hx.le _))
  have hf (q : ℝ) : T^σ*(T^(q-σ)*a^q) = T^q*a^q := by
    rw [← mul_assoc,← Real.rpow_add hT,show σ+(q-σ)=q by ring]
  apply le_of_mul_le_mul_left (a := T^σ) _ (Real.rpow_pos_of_pos hT _)
  rw [mul_add,hf,hf]
  simpa only [Real.mul_rpow hT.le ha.le] using he

private theorem warm_clock_moment (F : Finset ℕ) (b : SpectralBand 1) {z : ℂ} (hs : 1/2 ≤ z.re) (hc : z.re ≤ 5/4) :
    clockMoment F b z z.re ≤ 10*‖z‖^(3/2-z.re)*relativeReading quadraticResponse b^(1/4:ℝ) := by
  let T := ‖z‖
  let D := relativeReading quadraticResponse b
  have hz : 0 < z.re := (by norm_num : (0:ℝ)<1/2).trans_le hs
  have hT : 0 < T := lt_of_lt_of_le hz ((le_abs_self _).trans (Complex.abs_re_le_norm z))
  have hD : 0 ≤ D := (relativeReading_bounds _ b).1
  have hterm (k : ℕ) : occupationWeight k^z.re*clockMask b z k ≤
      T^(1/2-z.re)*(occupationWeight k^(1/2:ℝ)*clockMask b z k)+
      T^(5/4-z.re)*(occupationWeight k^(5/4:ℝ)*clockMask b z k) := by
    exact (mul_le_mul_of_nonneg_right (interpolated_weight (occupationWeight_pos k) hT hs hc)
      (clockMask_mem b hz.le k).1).trans_eq (by ring)
  have he := sum_le_sum (s := F) (fun k _ => hterm k)
  rw [sum_add_distrib,← mul_sum,← mul_sum] at he
  have h1 := mul_le_mul_of_nonneg_left (half_clock_moment F b hs) (Real.rpow_nonneg hT.le (1/2-z.re))
  have h2 := mul_le_mul_of_nonneg_left (five_quarters_clock_moment F b hs) (Real.rpow_nonneg hT.le (5/4-z.re))
  refine (he.trans (add_le_add h1 h2)).trans_eq ?_
  change T^(1/2-z.re)*(T*D^(1/4:ℝ))+T^(5/4-z.re)*(9*(T*D)^(1/4:ℝ)) = 10*T^(3/2-z.re)*D^(1/4:ℝ)
  have ha : T^(1/2-z.re)*T = T^(3/2-z.re) := by
    rw [← Real.rpow_add_one hT.ne',show 1/2-z.re+1=3/2-z.re by ring]
  have hb : T^(5/4-z.re)*T^(1/4:ℝ) = T^(3/2-z.re) := by
    rw [← Real.rpow_add hT,show 5/4-z.re+1/4=3/2-z.re by ring]
  rw [Real.mul_rpow hT.le hD]
  linear_combination D^(1/4:ℝ)*ha + 9*D^(1/4:ℝ)*hb

private theorem full_clock_moment (F : Finset ℕ) (b : SpectralBand 1) {z : ℂ} (hs : 1/2 ≤ z.re) :
    clockMoment F b z z.re ≤ 10*‖z‖^(quarticClockOrder z.re/4)*relativeReading quadraticResponse b^(1/4:ℝ) := by
  rcases le_total z.re (5/4) with hc | hc
  · have he : quarticClockOrder z.re/4 = 3/2-z.re := by
      rw [quarticClockOrder,max_eq_right (by linarith only [hc])]; ring
    rw [he]
    exact warm_clock_moment F b hs hc
  · have he : quarticClockOrder z.re = 1 := max_eq_left (by linarith only [hc])
    rw [he]
    have hm : clockMoment F b z z.re ≤ clockMoment F b z (5/4) := sum_le_sum (fun k _ =>
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge (occupationWeight_pos k) (occupation_in_unit k).2 hc)
        (clockMask_mem b ((by norm_num : (0:ℝ)≤1/2).trans hs) k).1)
    have h := hm.trans (five_quarters_clock_moment F b hs)
    rw [Real.mul_rpow (norm_nonneg _) (relativeReading_bounds _ b).1] at h
    have hx := Real.rpow_nonneg (norm_nonneg z) (1/4:ℝ)
    have hy := Real.rpow_nonneg (relativeReading_bounds quadraticResponse b).1 (1/4:ℝ)
    exact h.trans ((mul_le_mul_of_nonneg_right (by norm_num : (9:ℝ)≤10) (mul_nonneg hx hy)).trans_eq (mul_assoc _ _ _).symm)

/-- One coefficient gives the predicted height order throughout the closed critical half-plane, including both transition points. -/
theorem quartic_growth_upper {z : ℂ} (hs : 1/2 ≤ z.re) :
    traceControlsAt 1 z 4 (20^4*‖z‖^(quarticClockOrder z.re)) := by
  have hz : 0 < z.re := (by norm_num : (0:ℝ)<1/2).trans_le hs
  intro P hd hc
  let b := physicalSpectrum P hd hc
  let D := relativeReading quadraticResponse b
  let q := quarticClockOrder z.re
  have hD : 0 ≤ D := (relativeReading_bounds _ b).1
  have hfinite (N : ℕ) : ‖∑ k ∈ range N, complexDrop b k z‖ ≤ 20*‖z‖^(q/4)*D^(1/4:ℝ) := by
    have he := norm_sum_le (range N) (fun k => complexDrop b k z)
    simp only [clockMask_represents,← Finset.mul_sum] at he
    exact (he.trans (mul_le_mul_of_nonneg_left (full_clock_moment (range N) b hs) (by norm_num : (0:ℝ)≤2))).trans_eq (by dsimp only [D,q]; ring)
  have ht := ((summable_complexDrop b hz).hasSum.tendsto_sum_nat).norm
  have hb : ‖relativePartition b z‖ ≤ 20*‖z‖^(q/4)*D^(1/4:ℝ) := le_of_tendsto ht (Eventually.of_forall hfinite)
  have hp := pow_le_pow_left₀ (norm_nonneg _) hb 4
  have hr (x p : ℝ) (hx : 0 ≤ x) : (x^(p/4))^4 = x^p := by
    rw [← Real.rpow_mul_natCast hx,show (p/4)*(4:ℕ) = p by push_cast; ring]
  rw [mul_pow,mul_pow,hr _ q (norm_nonneg z),hr _ 1 hD,Real.rpow_one] at hp
  change ‖relativePartition b z‖^(4:ℝ) ≤ _
  rw [show ‖relativePartition b z‖^(4:ℝ) = ‖relativePartition b z‖^4 from Real.rpow_natCast _ 4,
    ← quadratic_physicalReading P hd hc]
  exact hp

#print axioms quartic_growth_upper

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
