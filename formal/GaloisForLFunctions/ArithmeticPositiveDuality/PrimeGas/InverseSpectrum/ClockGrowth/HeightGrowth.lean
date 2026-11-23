import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockGrowth.FiniteVariation

/-! # The sharp rank-one coefficient has the full complex height growth order -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Finset Filter Topology

private theorem tail_power_tendsto (N : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun M => occupationWeight (N+M)^σ) atTop (𝓝 (0:ℝ)) := by
  have ht : Tendsto (fun M => occupationWeight (M+N)) atTop (𝓝 0) :=
    occupationWeight_tendsto.comp (tendsto_add_atTop_nat N)
  have hh := ((Real.continuous_rpow_const hσ.le).tendsto 0).comp ht
  simpa only [Function.comp_def,Real.zero_rpow hσ.ne',Nat.add_comm N] using hh

/-- Normalize the tail variation by its first real power; the matching exponent cancels the occupation scale. -/
theorem matched_variation_forces_height {z : ℂ} (hz : 0 < z.re) {p K : ℝ} (hp : 0 < p) (hm : z.re*p = 2)
    (h : traceControlsAt 1 z p K) : ‖z‖/z.re ≤ 4*K^p⁻¹ := by
  by_contra! hlt
  obtain ⟨c,hc,hz'⟩ := exists_between hlt
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((gap_variation_ratio_tendsto hz).eventually_const_lt hz')
  have he (M : ℕ) : c*(occupationWeight N^z.re-occupationWeight (N+M)^z.re) ≤
      4*(K^p⁻¹*occupationWeight N^z.re) := by
    have ht := sum_range_sub' (fun j => occupationWeight (N+j)^z.re) M
    simp only [Nat.add_zero,← Nat.add_assoc] at ht
    rw [← ht,mul_sum]
    refine (sum_le_sum (fun j _ => ?_)).trans (finite_gap_variation_le hz hp hm h N M)
    exact ((lt_div_iff₀ (gapPower_pos hz (N+j))).mp (hN (N+j) (Nat.le_add_right _ _))).le
  have ht := ((tendsto_const_nhds (x := occupationWeight N^z.re)).sub (tail_power_tendsto N hz)).const_mul c
  have hlim := le_of_tendsto ht (Eventually.of_forall he)
  rw [sub_zero,← mul_assoc] at hlim
  exact hc.not_ge (le_of_mul_le_mul_right hlim (Real.rpow_pos_of_pos (occupationWeight_pos N) _))

/-- A coherent subset of adjacent occupation gaps gives a height lower bound within a fixed factor of the uniform chord estimate. -/
theorem matched_height_factor_lower {z : ℂ} (hz : 0 < z.re) {p K : ℝ} (hp : 0 < p) (hm : z.re*p = 2)
    (h : traceControlsAt 1 z p K) : (‖z‖/(4*z.re))^p ≤ K := by
  have hK := zero_le_one.trans (matched_coefficient_one_le hz hp hm h)
  have hb := matched_variation_forces_height hz hp hm h
  have hr : ‖z‖/(4*z.re) ≤ K^p⁻¹ := by
    rw [mul_comm (4:ℝ),← div_div]
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    simpa only [mul_comm (4:ℝ)] using hb
  exact (Real.rpow_le_rpow (div_nonneg (norm_nonneg _) (mul_nonneg (by norm_num) hz.le)) hr hp.le).trans_eq
    (Real.rpow_inv_rpow hK hp.ne')

#print axioms matched_variation_forces_height
#print axioms matched_height_factor_lower

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
