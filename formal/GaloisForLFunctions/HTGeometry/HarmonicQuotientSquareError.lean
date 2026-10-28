import GaloisForLFunctions.RHTower.HarmonicQuotientToeplitz

/-!
# Vanishing squared errors at a harmonic quotient boundary

A row error dominated by a vanishing complementary-quotient profile divided
by the square root of its row index has negligible squared mass at logarithmic scale.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.HTGeometry

/-- Uniform quotient domination turns rowwise control into a normalized square-error limit. -/
theorem tendsto_harmonicQuotient_square_error {f : ℕ → ℝ}
    (hf : Tendsto f atTop (𝓝 0)) (R : ℕ → ℕ → ℝ)
    (hR : ∀ N n, n ∈ Icc 1 N → |R N n| ≤ f (N / n) / Real.sqrt n) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, R N n ^ 2) / Real.log N)
      atTop (𝓝 0) := by
  have hf2 : Tendsto (fun n => f n ^ 2) atTop (𝓝 0) := by
    simpa using hf.pow 2
  obtain ⟨C, hC⟩ := hf2.abs.bddAbove_range
  have hmean := _root_.RHTower.tendsto_harmonicQuotientMean_div_log
    (fun n => f n ^ 2) 0 C hf2 (fun n => hC ⟨n, rfl⟩)
  simp only [_root_.RHTower.harmonicQuotientMean] at hmean
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmean ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with N hN
    exact div_nonneg (sum_nonneg fun n _ => sq_nonneg (R N n))
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
  · filter_upwards [eventually_ge_atTop 2] with N hN
    apply div_le_div_of_nonneg_right ?_
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
    apply sum_le_sum
    intro n hn
    have h := hR N n hn
    have hs := mul_le_mul h h (abs_nonneg (R N n)) ((abs_nonneg (R N n)).trans h)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc
      R N n ^ 2 = |R N n| * |R N n| := by rw [← sq, sq_abs]
      _ ≤ (f (N / n) / Real.sqrt n) * (f (N / n) / Real.sqrt n) := hs
      _ = f (N / n) ^ 2 / (n : ℝ) := by
        rw [← sq, div_pow, Real.sq_sqrt hn0]

end GaloisForLFunctions.HTGeometry
