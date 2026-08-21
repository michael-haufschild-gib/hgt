import GaloisForLFunctions.RHTower.Sieve.PowerWindowSelect

namespace RHTower.Sieve

theorem scratch_exists_pow_mem_matomakiTeravainen_window
    {T M eps : ℝ} (hT : 1 < T) (hM : 1 < M)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 1000)
    (hMupper : M ≤ T ^ ((2 : ℝ) / 11 + eps)) :
    ∃ ell : ℕ, 1 ≤ ell ∧
      T ^ ((5 : ℝ) / 6 - eps) ≤ M ^ ell ∧
      M ^ ell ≤ T ^ (1 - eps / 2) := by
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hLowerExp : 0 < (5 : ℝ) / 6 - eps := by linarith
  by_cases hsmall : M ≤ T ^ ((1 : ℝ) / 6 + eps / 2)
  · have hA : 1 < T ^ ((5 : ℝ) / 6 - eps) :=
      Real.one_lt_rpow hT hLowerExp
    have hAB :
        T ^ ((5 : ℝ) / 6 - eps) * M ≤ T ^ (1 - eps / 2) := by
      calc
        T ^ ((5 : ℝ) / 6 - eps) * M ≤
            T ^ ((5 : ℝ) / 6 - eps) * T ^ ((1 : ℝ) / 6 + eps / 2) :=
          mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hT0.le _)
        _ = T ^ (((5 : ℝ) / 6 - eps) + ((1 : ℝ) / 6 + eps / 2)) := by
          rw [← Real.rpow_add hT0]
        _ = T ^ (1 - eps / 2) := by congr 1 <;> ring
    exact exists_pow_mem_window hM hA hAB
  · have hlarge : T ^ ((1 : ℝ) / 6 + eps / 2) < M := lt_of_not_ge hsmall
    refine ⟨5, by norm_num, ?_, ?_⟩
    · calc
        T ^ ((5 : ℝ) / 6 - eps) ≤
            T ^ (5 * ((1 : ℝ) / 6 + eps / 2)) :=
          Real.rpow_le_rpow_of_exponent_le hT.le (by linarith)
        _ = (T ^ ((1 : ℝ) / 6 + eps / 2)) ^ (5 : ℕ) := by
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul hT0.le]
          congr 1 <;> ring
        _ ≤ M ^ (5 : ℕ) := by gcongr
    · calc
        M ^ (5 : ℕ) ≤ (T ^ ((2 : ℝ) / 11 + eps)) ^ (5 : ℕ) := by gcongr
        _ = T ^ (5 * ((2 : ℝ) / 11 + eps)) := by
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul hT0.le]
          congr 1 <;> ring
        _ ≤ T ^ (1 - eps / 2) :=
          Real.rpow_le_rpow_of_exponent_le hT.le (by nlinarith)

end RHTower.Sieve
