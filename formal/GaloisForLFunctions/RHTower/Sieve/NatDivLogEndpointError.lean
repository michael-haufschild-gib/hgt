import GaloisForLFunctions.RHTower.Sieve.HarmonicLogWindowMoments

namespace RHTower.Sieve

/-- Replacing the continuous quotient `N / q` by the first integer above its
floor changes its logarithm by at most the reciprocal quotient scale. -/
theorem abs_log_natDiv_add_one_sub_log_div_le
    {N q : ℕ} (hN : 0 < N) (hq : 0 < q) :
    |Real.log ((N / q + 1 : ℕ) : ℝ) -
        Real.log ((N : ℝ) / (q : ℝ))| ≤
      (q : ℝ) / (N : ℝ) := by
  let x : ℝ := (N : ℝ) / (q : ℝ)
  let y : ℝ := ((N / q + 1 : ℕ) : ℝ)
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have hxy : x ≤ y := by
    have hdec := Nat.div_add_mod N q
    have hmod := Nat.mod_lt N hq
    have hdecR : (q : ℝ) * ((N / q : ℕ) : ℝ) + ((N % q : ℕ) : ℝ) = (N : ℝ) := by
      exact_mod_cast hdec
    have hmodR : ((N % q : ℕ) : ℝ) < (q : ℝ) := by exact_mod_cast hmod
    dsimp [x, y]
    push_cast
    apply (div_le_iff₀ hqR).2
    nlinarith
  have hyx : y ≤ x + 1 := by
    have hfloor : ((N / q : ℕ) : ℝ) ≤ x := by
      exact Nat.cast_div_le
    dsimp [y]
    push_cast
    linarith
  have hratio : y / x ≤ 1 + 1 / x := by
    apply (div_le_iff₀ hx).2
    have := mul_le_mul_of_nonneg_right hyx hx.le
    field_simp [hx.ne'] at this ⊢
    nlinarith
  have hratioPos : 0 < y / x := by positivity
  have hlogGap : Real.log y - Real.log x ≤ 1 / x := by
    rw [← Real.log_div hy.ne' hx.ne']
    exact (Real.log_le_sub_one_of_pos hratioPos).trans (by linarith)
  have hlogNonneg : 0 ≤ Real.log y - Real.log x := by
    exact sub_nonneg.mpr (Real.log_le_log hx hxy)
  rw [abs_of_nonneg hlogNonneg]
  change Real.log y - Real.log x ≤ (q : ℝ) / (N : ℝ)
  calc
    Real.log y - Real.log x ≤ 1 / x := hlogGap
    _ = (q : ℝ) / (N : ℝ) := by
      dsimp [x]
      field_simp [hqR.ne', hNR.ne']

end RHTower.Sieve
