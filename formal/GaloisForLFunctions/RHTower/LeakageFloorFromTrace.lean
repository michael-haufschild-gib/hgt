import Mathlib

/-!
# The leakage floor from the trace alone

`SecularTailSaturation` reduces the CCM transfer's tail control to a positive floor on the leakage
`d_n = 1 − λ_n`, where `λ_n` are the eigenvalues of the time–bandwidth (Slepian) operator.  That
floor needs no eigenvalue asymptotics: it follows from two soft facts,

* the eigenvalues are nonnegative and decreasing, and
* their sum is the trace, `∑_n λ_n(c) = 2c/π`.

A nonnegative antitone sequence with bounded partial sums satisfies `λ_n ≤ T/(n+1)`, because the
first `n+1` terms are each at least `λ_n`.  Hence `λ_n ≤ 1/2` — so the leakage is at least `1/2` —
as soon as `n + 1 ≥ 2T`, i.e. past `n ≈ 4c/π`.  This is the classical `2c/π` degrees-of-freedom
transition, obtained here from the trace rather than from Fuchs's asymptotic, and it is exactly the
regime in which the Fuchs expansion is *not* valid.
-/

namespace RHTower

/-- **Markov bound for an antitone nonnegative sequence with bounded partial sums.**  Each term is
at most the bound divided by its index. -/
theorem antitone_le_of_partialSum_le {lam : ℕ → ℝ} (_hnn : ∀ n, 0 ≤ lam n)
    (hanti : Antitone lam) {T : ℝ}
    (hsum : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), lam k ≤ T) (n : ℕ) :
    lam n ≤ T / (n + 1) := by
  have hlow : ((n : ℝ) + 1) * lam n ≤ ∑ k ∈ Finset.range (n + 1), lam k := by
    have hterm : ∀ k ∈ Finset.range (n + 1), lam n ≤ lam k := by
      intro k hk
      exact hanti (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    calc ((n : ℝ) + 1) * lam n = ∑ _k ∈ Finset.range (n + 1), lam n := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ ∑ k ∈ Finset.range (n + 1), lam k := Finset.sum_le_sum hterm
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [le_div_iff₀ hpos]
  calc lam n * ((n : ℝ) + 1) = ((n : ℝ) + 1) * lam n := by ring
    _ ≤ ∑ k ∈ Finset.range (n + 1), lam k := hlow
    _ ≤ T := hsum n

/-- **The leakage floor.**  Past `n + 1 ≥ 2T` the eigenvalue is at most `1/2`, so the leakage
`1 − λ_n` is at least `1/2`.  With `T = 2c/π` this is the transition at `n ≈ 4c/π`. -/
theorem half_le_leakage_of_trace {lam : ℕ → ℝ} (hnn : ∀ n, 0 ≤ lam n)
    (hanti : Antitone lam) {T : ℝ} (_hT : 0 ≤ T)
    (hsum : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), lam k ≤ T)
    {n : ℕ} (hn : 2 * T ≤ (n : ℝ) + 1) :
    (1 : ℝ) / 2 ≤ 1 - lam n := by
  have hbound := antitone_le_of_partialSum_le hnn hanti hsum n
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hhalf : lam n ≤ 1 / 2 := by
    refine le_trans hbound ?_
    rw [div_le_div_iff₀ hpos (by norm_num : (0:ℝ) < 2)]
    linarith
  linarith

/-- **The floor holds cofinally.**  For every bound `T` there is an index past which the leakage is
at least `1/2`; no asymptotic expansion of the eigenvalues is used. -/
theorem exists_leakage_floor {lam : ℕ → ℝ} (hnn : ∀ n, 0 ≤ lam n)
    (hanti : Antitone lam) {T : ℝ} (hT : 0 ≤ T)
    (hsum : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), lam k ≤ T) :
    ∃ N : ℕ, ∀ n ≥ N, (1 : ℝ) / 2 ≤ 1 - lam n := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * T)
  refine ⟨N, fun n hn => ?_⟩
  refine half_le_leakage_of_trace hnn hanti hT hsum ?_
  have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

end RHTower
