import GaloisForLFunctions.RHTower.Sieve.PrimePowerDefectBound

namespace RHTower.Sieve

open ArithmeticFunction

/-- Proper prime powers have at least log 2 of von Mangoldt mass each;
the corpus's exact defect bound therefore controls their cardinality. -/
theorem properPrimePower_count_mul_log_two_le_defect (K : ℕ) :
    ((((Finset.range (K + 1)).filter
      (fun n => IsPrimePow n ∧ ¬ n.Prime)).card : ℕ) : ℝ) *
        Real.log 2 ≤ primePowerDefect K := by
  classical
  let S : Finset ℕ :=
    (Finset.range (K + 1)).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)
  have hterm : ∀ n ∈ S, Real.log 2 ≤ (vonMangoldt n : ℝ) := by
    intro n hn
    have hpow : IsPrimePow n := (Finset.mem_filter.mp hn).2.1
    have hmin : 2 ≤ Nat.minFac n :=
      (Nat.minFac_prime (IsPrimePow.ne_one hpow)).two_le
    rw [vonMangoldt_apply, if_pos hpow]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hmin)
  have hpoint : ∀ n : ℕ,
      (if IsPrimePow n ∧ ¬ n.Prime then (vonMangoldt n : ℝ) else 0) =
        (vonMangoldt n : ℝ) -
          if n.Prime then Real.log n else 0 := by
    intro n
    by_cases hp : n.Prime
    · simp [hp, vonMangoldt_apply_prime hp]
    · by_cases hpow : IsPrimePow n
      · simp [hp, hpow]
      · have hz : (vonMangoldt n : ℝ) = 0 :=
          (vonMangoldt_eq_zero_iff).2 hpow
        simp [hp, hpow, hz]
  change (S.card : ℝ) * Real.log 2 ≤ primePowerDefect K
  calc
    (S.card : ℝ) * Real.log 2 =
        ∑ _n ∈ S, Real.log 2 := by simp
    _ ≤ ∑ n ∈ S, (vonMangoldt n : ℝ) :=
      Finset.sum_le_sum hterm
    _ = ∑ n ∈ Finset.range (K + 1),
        ((vonMangoldt n : ℝ) -
          if n.Prime then Real.log n else 0) := by
            dsimp [S]
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro n _
            exact hpoint n
    _ = primePowerDefect K := rfl

theorem properPrimePower_count_mul_log_two_le_sqrt_log
    {K : ℕ} (hK : 1 ≤ K) :
    ((((Finset.range (K + 1)).filter
      (fun n => IsPrimePow n ∧ ¬ n.Prime)).card : ℕ) : ℝ) *
        Real.log 2 ≤
      2 * Real.sqrt (K : ℝ) * Real.log (K : ℝ) := by
  exact (properPrimePower_count_mul_log_two_le_defect K).trans
    (primePowerDefect_le hK)

end RHTower.Sieve
