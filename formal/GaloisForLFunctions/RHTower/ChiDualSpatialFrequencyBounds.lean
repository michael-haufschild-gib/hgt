import GaloisForLFunctions.RHTower.ChiDualPairedEndpointCancellation

open Complex Set Filter Topology MeasureTheory
noncomputable section
namespace RHTower



/-- The complete half-integer expansion of the literal block stays in a
fixed positive spatial range, including both extra endpoint halves. -/
theorem chiDual_spatial_block_ratio_bounds {N t x : ℝ} (hN : 50 ≤ N)
    (ht : N ≤ t ∧ t ≤ 2 * N) (hx : N / 5 - 1 / 2 ≤ x ∧ x ≤ 6 * N / 25 + 1 / 2) :
    0 < x ∧ 2 * N / 11 ≤ x ∧ x ≤ N / 4 ∧ 4 ≤ t / x ∧ t / x ≤ 11 := by
  have hN0 : 0 < N := by linarith
  have hxlo : 2 * N / 11 ≤ x := by linarith [hx.1]
  have hxhi : x ≤ N / 4 := by linarith [hx.2]
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hxlo
  refine ⟨hx0, hxlo, hxhi, (le_div_iff₀ hx0).mpr ?_, (div_le_iff₀ hx0).mpr ?_⟩ <;>
    linarith [ht.1, ht.2]

/-- Every spatial Fourier mode k>=2 has a uniform derivative gap on the
entire literal half-integer block, with both signs retained. -/
theorem chiDual_spatial_fourier_frequency_gap {N t x : ℝ} (hN : 50 ≤ N)
    (ht : N ≤ t ∧ t ≤ 2 * N) (hx : N / 5 - 1 / 2 ≤ x ∧ x ≤ 6 * N / 25 + 1 / 2)
    {k : ℕ} (hk : 2 ≤ k) :
    t / x - 2 * Real.pi * k ≤ -(k : ℝ) / 2 ∧
      (k : ℝ) / 2 ≤ t / x + 2 * Real.pi * k := by
  obtain ⟨_, _, _, hlo, hhi⟩ := chiDual_spatial_block_ratio_bounds hN ht hx
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hω : 6 * (k : ℝ) ≤ 2 * Real.pi * k :=
    mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) (Nat.cast_nonneg k)
  constructor <;> linarith

/-- The second and third spatial log-phase derivatives have the required
inverse-height scales throughout the complete block. -/
theorem chiDual_spatial_phase_derivative_bounds {N t x : ℝ} (hN : 50 ≤ N)
    (ht : N ≤ t ∧ t ≤ 2 * N) (hx : N / 5 - 1 / 2 ≤ x ∧ x ≤ 6 * N / 25 + 1 / 2) :
    |-(t / x ^ 2)| ≤ 100 / N ∧ |2 * t / x ^ 3| ≤ 1000 / N ^ 2 := by
  obtain ⟨hx0, hxlo, _, hlo, hhi⟩ := chiDual_spatial_block_ratio_bounds hN ht hx
  have hN0 : 0 < N := by linarith
  have ht0 : 0 < t := hN0.trans_le ht.1
  have hi : 1 / x ≤ 11 / (2 * N) := by
    apply (div_le_div_iff₀ hx0 (by positivity : 0 < 2 * N)).mpr
    linarith
  have hi2 : (1 / x) ^ 2 ≤ (11 / (2 * N)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hi 2
  have h1 : t / x ^ 2 = (t / x) * (1 / x) := by ring
  have h2 : 2 * t / x ^ 3 = (2 * (t / x)) * (1 / x) ^ 2 := by ring
  constructor
  · rw [abs_neg, abs_of_pos (by positivity : 0 < t / x ^ 2), h1]
    calc
      _ ≤ 11 * (11 / (2 * N)) := mul_le_mul hhi hi (by positivity) (by norm_num)
      _ ≤ 100 / N := by
        field_simp
        linarith
  · rw [abs_of_pos (by positivity : 0 < 2 * t / x ^ 3), h2]
    calc
      _ ≤ 22 * (11 / (2 * N)) ^ 2 :=
        mul_le_mul (by linarith : 2 * (t / x) ≤ 22) hi2 (by positivity) (by norm_num)
      _ ≤ 1000 / N ^ 2 := by
        field_simp
        nlinarith only [sq_nonneg N]

end RHTower
