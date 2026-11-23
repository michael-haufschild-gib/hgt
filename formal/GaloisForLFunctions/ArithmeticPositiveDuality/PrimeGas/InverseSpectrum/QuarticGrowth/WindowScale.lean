import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.QuarticGrowth.Window

/-! # Uniform lower bound at the height scale of an occupation block -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

private theorem floor_window {t w : ℝ} (hw : 0 < w) (ht : 8*w ≤ t) :
    ∃ N : ℕ, t/(8*w) ≤ (N:ℝ) ∧ (2*(N:ℝ)+1)*w ≤ t := by
  let N := ⌊t/(4*w)⌋₊
  have h4 : 0 < 4*w := by positivity
  have h8 : 0 < 8*w := by positivity
  have ht' := h8.trans_le ht
  have hu : (N:ℝ)*(4*w) ≤ t := (le_div_iff₀ h4).mp (Nat.floor_le (div_nonneg ht'.le h4.le))
  have hl : t < ((N:ℝ)+1)*(4*w) := (div_lt_iff₀ h4).mp (Nat.lt_floor_add_one _)
  refine ⟨N,(div_le_iff₀ h8).mpr ?_,?_⟩
  · nlinarith only [ht,hl]
  · nlinarith only [ht,hu,hw.le]

private theorem select_clock_window {σ t : ℝ} (hs : 0 < σ) (ht : 8*(1+Real.pi) ≤ t) :
    ∃ N : ℕ, 0 < N ∧ (2*(N:ℝ)+1)*Real.pi ≤ t ∧
      (t/(8*(1+Real.pi)))*t^(-σ) ≤ (N:ℝ)*occupationWeight (2*N)^σ ∧ occupationWeight N ≤ (8*(1+Real.pi))/t := by
  let C := 8*(1+Real.pi)
  have hw := add_pos zero_lt_one Real.pi_pos
  have hC : 0 < C := mul_pos (by norm_num) hw
  have ht' : 0 < t := hC.trans_le ht
  obtain ⟨N,hN,hsize⟩ := floor_window hw ht
  have hNp : 0 < (N:ℝ)+1 := by positivity
  have h2p : 0 < 2*(N:ℝ)+1 := by positivity
  have hS : 2*(N:ℝ)+1 ≤ t := (le_mul_of_one_le_right h2p.le (le_add_of_nonneg_right Real.pi_pos.le)).trans hsize
  have hπ : (2*(N:ℝ)+1)*Real.pi ≤ t := (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) h2p.le).trans hsize
  have ha : 1/t ≤ occupationWeight (2*N) := by
    simp only [occupationWeight_eq,Nat.cast_mul,Nat.cast_ofNat,← one_div]
    exact (div_le_div_iff₀ ht' h2p).mpr (by simpa only [one_mul] using hS)
  have hb : occupationWeight N ≤ C/t := by
    rw [occupationWeight_eq,← one_div]
    apply (div_le_div_iff₀ hNp ht').mpr
    have he := (div_le_iff₀ hC).mp hN
    linarith only [he,hC.le]
  have hneg : (1/t)^σ = t^(-σ) := by rw [one_div,Real.inv_rpow ht'.le,Real.rpow_neg ht'.le]
  have hp := Real.rpow_le_rpow (one_div_pos.mpr ht').le ha hs.le
  rw [hneg] at hp
  have hbase := mul_le_mul hN hp (Real.rpow_nonneg ht'.le _) (Nat.cast_nonneg N)
  exact ⟨N,Nat.cast_pos.mp ((div_pos ht' hC).trans_le hN),hπ,hbase,hb⟩

/-- A single actual omission can give an amplitude of order t^(1−σ) at a fourth-trace cost of order t⁻². -/
theorem clock_scale_physical_witness {σ t : ℝ} (hs : 0 < σ) (ht : 8*(1+Real.pi) ≤ t) :
    ∃ (P : Projection) (hd : MissingDimension P 1) (hc : Conserving (projected P)),
      t^(1-σ)/(8*(8*(1+Real.pi))) < ‖relativePartition (physicalSpectrum P hd hc) (⟨σ,t⟩:ℂ)‖ ∧
      traceLoss (projected P) < 2*((8*(1+Real.pi))/t)^2 := by
  let C := 8*(1+Real.pi)
  have hC : 0 < C := mul_pos (by norm_num) (add_pos zero_lt_one Real.pi_pos)
  have ht' : 0 < t := hC.trans_le ht
  obtain ⟨N,hN,hsize,hbase,hb⟩ := select_clock_window hs ht
  obtain ⟨P,hd,hc,hL,hD⟩ := physical_window_witness (z := ⟨σ,t⟩) hs ht' N hN hsize
  refine ⟨P,hd,hc,?_,hD.trans_le (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (occupationWeight_pos _).le hb 2) (by norm_num))⟩
  have he : t^(1-σ)/(8*C) = ((t/C)*t^(-σ))/8 := by
    rw [sub_eq_add_neg,Real.rpow_add ht',Real.rpow_one]
    field_simp [hC.ne']
  exact he.trans_lt ((div_le_div_of_nonneg_right hbase (by norm_num : (0:ℝ)≤8)).trans_lt hL)

/-- At large heights, clock-scale half turns force the power six minus four times the real temperature. -/
theorem window_growth_lower {σ t : ℝ} (hs : 0 < σ) (ht : 8*(1+Real.pi) ≤ t) {K : ℝ}
    (h : traceControlsAt 1 (⟨σ,t⟩:ℂ) 4 K) : t^(6-4*σ) ≤ K*(4^4*(8*(1+Real.pi))^6) := by
  let C := 8*(1+Real.pi)
  have hC : 0 < C := mul_pos (by norm_num) (add_pos zero_lt_one Real.pi_pos)
  have ht' : 0 < t := hC.trans_le ht
  obtain ⟨N,_,hπ,hbase,hb⟩ := select_clock_window hs ht
  have hK := trace_coefficient_nonneg 0 (z := ⟨σ,t⟩) hs (by norm_num : (0:ℝ)≤4) h
  have htest := window_quartic_test (z := ⟨σ,t⟩) hs ht' N hπ h
  have hl : ((t/C)*t^(-σ))^4 ≤ 4^4*(K*(C/t)^2) := by
    refine ((pow_le_pow_left₀ (mul_nonneg (div_pos ht' hC).le (Real.rpow_nonneg ht'.le _)) hbase 4).trans htest).trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (occupationWeight_pos _).le hb 2) hK) (by norm_num)
  have he : t^(6-4*σ) = t^6*(t^(-σ))^4 := by
    rw [← Real.rpow_mul_natCast ht'.le,← Real.rpow_natCast t 6,← Real.rpow_add ht']
    congr 1
    push_cast
    ring
  calc
    t^(6-4*σ) = (((t/C)*t^(-σ))^4*t^2)*C^4 := by rw [he,mul_pow,div_pow]; field_simp
    _ ≤ (4^4*(K*(C/t)^2)*t^2)*C^4 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hl (sq_nonneg t)) (pow_nonneg hC.le _)
    _ = K*(4^4*C^6) := by field_simp

#print axioms clock_scale_physical_witness
#print axioms window_growth_lower

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
