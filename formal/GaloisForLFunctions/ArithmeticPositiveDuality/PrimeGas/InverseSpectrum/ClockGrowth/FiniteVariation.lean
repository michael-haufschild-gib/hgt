import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockGrowth.ComplexSubset
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockGrowth.GapVariation
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InterlacingConverse.FiniteTests

/-! # An ordinary trace bounds every finite stretch of complex gap variation -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Finset Set

private theorem shifted_mask_bound {z : ℂ} (hz : 0 < z.re) {p K : ℝ} (hp : 0 < p)
    (h : traceControlsAt 1 z p K) (N : ℕ) (S : Finset ℕ) :
    ‖∑ j ∈ S, gapAmplitude z (N+j)‖^p ≤ K*∑ j ∈ S, (occupationWeight (N+j)^2-occupationWeight (N+j+1)^2) := by
  have hinj : Function.Injective (fun j : ℕ => N+j) := fun _ _ h => Nat.add_left_cancel h
  have hf := (rank_one_trace_finite_iff hz hp).mp h (S.image (fun j => N+j)) (fun k => occupationWeight (k+1))
    (fun k _ => ⟨le_rfl,occupationWeight_antitone (Nat.le_succ k)⟩)
  simpa only [sum_image hinj.injOn,gapAmplitude] using hf

private theorem mask_deficit_le (N M : ℕ) {S : Finset ℕ} (hS : S ⊆ range M) :
    (∑ j ∈ S, (occupationWeight (N+j)^2-occupationWeight (N+j+1)^2)) ≤ occupationWeight N^2 := by
  have ht := sum_range_sub' (fun j => occupationWeight (N+j)^2) M
  simp only [Nat.add_zero,← Nat.add_assoc] at ht
  refine (sum_le_sum_of_subset_of_nonneg hS (fun j _ _ => sub_nonneg.mpr (pow_le_pow_left₀
    (occupationWeight_pos _).le (occupationWeight_antitone (Nat.le_succ (N+j))) 2))).trans ?_
  exact ht.trans_le (sub_le_self _ (sq_nonneg _))

theorem matched_coefficient_one_le {z : ℂ} (hz : 0 < z.re) {p K : ℝ} (hp : 0 < p) (hm : z.re*p = 2)
    (h : traceControlsAt 1 z p K) : 1 ≤ K := by
  simpa only [Nat.cast_one,Real.one_rpow,mul_one] using trace_control_forces_factor 1 hz ⟨p,hp⟩ hm h

/-- The contribution of every interval of consecutive gap lengths is controlled by its first occupation scale. -/
theorem finite_gap_variation_le {z : ℂ} (hz : 0 < z.re) {p K : ℝ} (hp : 0 < p) (hm : z.re*p = 2)
    (h : traceControlsAt 1 z p K) (N M : ℕ) :
    (∑ j ∈ range M, ‖gapAmplitude z (N+j)‖) ≤ 4*(K^p⁻¹*occupationWeight N^z.re) := by
  have hK := zero_le_one.trans (matched_coefficient_one_le hz hp hm h)
  obtain ⟨S,hS,hs⟩ := exists_complex_subset (range M) (fun j => gapAmplitude z (N+j))
  have hb := (shifted_mask_bound hz hp h N S).trans (mul_le_mul_of_nonneg_left (mask_deficit_le N M hS) hK)
  have hr := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) hb (inv_nonneg.mpr hp.le)
  have he : 2*p⁻¹ = z.re := by rw [← hm,mul_assoc,mul_inv_cancel₀ hp.ne',mul_one]
  rw [Real.rpow_rpow_inv (norm_nonneg _) hp.ne',Real.mul_rpow hK (sq_nonneg _),← Real.rpow_two,
    ← Real.rpow_mul (occupationWeight_pos N).le,he] at hr
  exact hs.trans (mul_le_mul_of_nonneg_left hr (by norm_num))

#print axioms finite_gap_variation_le

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
