import GaloisForLFunctions.RHTower.SteinhausFullGaussianTruncation

open Complex Filter Topology
noncomputable section
namespace RHTower

/-- The literal normalized Gaussian tail has arbitrary power decay at the
square/cubic seam, uniformly throughout an entire left half-plane and all phases. -/
theorem exists_normalizedFullGaussian_cubic_tail_le
    {b q : ℝ} (hb : 0 ≤ b) (hq : 0 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ s : ℂ, s.re ≤ b →
      ∀ ω : SteinhausModel.Omega,
        ‖(((n ^ 2 : ℕ) : ℂ) ^ ((1 / 2 : ℂ) - s)) *
          (steinhausFullGaussianCofactor s (n ^ 2 : ℕ) ω -
            truncatedFullGaussianCofactor s (n ^ 2 : ℕ) (n ^ 3) ω)‖ ≤
              C * (n : ℝ) ^ (-q) := by
  let A : ℝ := q + b + 1
  have hA : 0 < A := by dsimp only [A]; linarith
  have hAb : 0 < A - b := by dsimp only [A]; linarith
  obtain ⟨K, hK, htail⟩ := exists_norm_steinhausFullGaussianCofactor_sub_head_le hA
  refine ⟨K / (A - b), div_nonneg hK hAb.le, ?_⟩
  intro n hn s hs ω
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (0 : ℝ) < ((n ^ 2 : ℕ) : ℝ) := by positivity
  have hsA : s.re < A := by linarith
  have hAs : 0 < A - s.re := sub_pos.mpr hsA
  have ht := htail s ((n ^ 2 : ℕ) : ℝ) hN hsA (n ^ 3)
    (by have hp : 0 < n ^ 3 := pow_pos hn 3; omega) ω
  change ‖steinhausFullGaussianCofactor s ((n ^ 2 : ℕ) : ℝ) ω -
    truncatedFullGaussianCofactor s ((n ^ 2 : ℕ) : ℝ) (n ^ 3) ω‖ ≤ _ at ht
  have hpower : (((n ^ 2 : ℕ) : ℝ) ^ (1 / 2 - s.re)) *
      (((n ^ 2 : ℕ) : ℝ) ^ A) * (((n ^ 3 : ℕ) : ℝ) ^ (s.re - A)) =
        (n : ℝ) ^ (1 + s.re - A) := by
    simp only [Nat.cast_pow]
    rw [← Real.rpow_natCast_mul hnR.le, ← Real.rpow_natCast_mul hnR.le,
      ← Real.rpow_natCast_mul hnR.le, ← Real.rpow_add hnR, ← Real.rpow_add hnR]
    congr 1
    norm_num
    ring
  have hnC : ((n ^ 2 : ℕ) : ℂ) = (((n ^ 2 : ℕ) : ℝ) : ℂ) := by norm_cast
  rw [norm_mul, hnC, Complex.norm_cpow_eq_rpow_re_of_pos hN]
  have hre : ((1 / 2 : ℂ) - s).re = 1 / 2 - s.re := by simp
  rw [hre]
  calc
    _ ≤ (((n ^ 2 : ℕ) : ℝ) ^ (1 / 2 - s.re)) *
        (K * (((n ^ 2 : ℕ) : ℝ) ^ A) *
          (((n ^ 3 : ℕ) : ℝ) ^ (s.re - A) / (A - s.re))) :=
      mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg hN.le _)
    _ = (K / (A - s.re)) * (n : ℝ) ^ (1 + s.re - A) := by
      rw [← hpower]
      ring
    _ ≤ (K / (A - b)) * (n : ℝ) ^ (-q) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_left hK hAb (by linarith)
      · apply Real.rpow_le_rpow_of_exponent_le hnR1
        dsimp only [A]
        linarith
      · exact Real.rpow_nonneg hnR.le _
      · exact div_nonneg hK hAb.le

end RHTower
