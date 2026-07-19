import GaloisForLFunctions.HTGeometry.NevDenominatorFactor

/-!
# The leading coefficient survives at arbitrarily high levels

The trailing coefficient at level `n` is the negative of the leading coefficient at level `n+1`:
`βₙ = −α_{n+1}` directly from the definitions.  So the statement that `αₙ` and `βₙ` never vanish
together — the Wronskian argument of `nevAlpha_beta_ne_zero` — says exactly that **no two consecutive
leading coefficients vanish**.

Hence the levels where the denominator is a genuine quasi-orthogonal polynomial of full degree are
cofinal, and any limit taken along them sees every level of the construction.  No parameter has to be
excluded.
-/

open scoped BigOperators

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The trailing coefficient is the negative of the next leading coefficient. -/
theorem nevBeta_eq_neg_nevAlpha_succ (s : ℕ → ℝ) (n : ℕ) (tau : ℝ) :
    nevBeta s n tau = -nevAlpha s (n + 1) tau := by
  rw [nevBeta, nevAlpha]
  ring

/-- **No two consecutive leading coefficients vanish.** -/
theorem nevAlpha_succ_ne_zero_of_eq_zero (h : PositiveMomentForm s) (n : ℕ) (tau : ℝ)
    (hz : nevAlpha s n tau = 0) : nevAlpha s (n + 1) tau ≠ 0 := by
  intro hz2
  refine nevAlpha_beta_ne_zero h n tau ⟨hz, ?_⟩
  rw [nevBeta_eq_neg_nevAlpha_succ, hz2, neg_zero]

/-- **The good levels are cofinal.**  Above any level there is one whose denominator is a
quasi-orthogonal polynomial of full degree. -/
theorem exists_ge_nevAlpha_ne_zero (h : PositiveMomentForm s) (tau : ℝ) (N : ℕ) :
    ∃ n, N ≤ n ∧ nevAlpha s n tau ≠ 0 := by
  by_cases hN : nevAlpha s N tau = 0
  · exact ⟨N + 1, by omega, nevAlpha_succ_ne_zero_of_eq_zero h N tau hN⟩
  · exact ⟨N, le_rfl, hN⟩

/-- The good levels form an infinite set. -/
theorem infinite_setOf_nevAlpha_ne_zero (h : PositiveMomentForm s) (tau : ℝ) :
    {n : ℕ | nevAlpha s n tau ≠ 0}.Infinite := by
  refine Set.infinite_of_not_bddAbove ?_
  intro hbdd
  obtain ⟨N, hN⟩ := hbdd
  obtain ⟨n, hn, hne⟩ := exists_ge_nevAlpha_ne_zero h tau (N + 1)
  have : n ≤ N := hN hne
  omega

end HTGeometry
