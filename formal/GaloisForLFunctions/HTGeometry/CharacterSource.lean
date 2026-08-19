import Mathlib

/-!
# The arithmetic source of a family of prime phases

For a family `u` of phases indexed by the primes, the completely multiplicative extension `χ` has
`χ(n) Λ(n) = u(p)^k log p` at `n = p^k` and vanishes elsewhere.  That value is written directly,
without constructing `χ`, since only the prime powers carry the source.

The point of the construction is locality: changing the phases at primes whose square exceeds `y`
changes the source only at those primes on `[1, y]`.
-/

noncomputable section

open ArithmeticFunction

namespace GaloisForLFunctions.HTGeometry

/-- The source `χ(n) Λ(n)` of a family of prime phases. -/
def characterSource (u : ℕ → ℂ) (n : ℕ) : ℂ :=
  (u n.minFac) ^ (n.factorization n.minFac) * ((Λ n : ℝ) : ℂ)

theorem characterSource_of_vonMangoldt_zero {u : ℕ → ℂ} {n : ℕ} (h : Λ n = 0) :
    characterSource u n = 0 := by
  rw [characterSource, h]
  simp

theorem characterSource_prime {u : ℕ → ℂ} {p : ℕ} (hp : Nat.Prime p) :
    characterSource u p = u p * ((Real.log p : ℝ) : ℂ) := by
  rw [characterSource, Nat.Prime.minFac_eq hp, hp.factorization_self, vonMangoldt_apply_prime hp]
  simp

theorem norm_characterSource_eq {u : ℕ → ℂ} (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1) (n : ℕ) :
    ‖characterSource u n‖ = Λ n := by
  by_cases h : IsPrimePow n
  · have hn0 : n ≠ 0 := by
      intro h0
      rw [h0] at h
      exact h.ne_zero rfl
    have hminfac : Nat.Prime n.minFac := Nat.minFac_prime (by
      intro h1
      rw [h1] at h
      exact h.ne_one rfl)
    rw [characterSource, norm_mul, norm_pow, hu _ hminfac, one_pow, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
  · have hΛ : Λ n = 0 := by
      rw [vonMangoldt_apply, if_neg h]
    rw [characterSource_of_vonMangoldt_zero hΛ, norm_zero, hΛ]

theorem norm_characterSource_le {u : ℕ → ℂ} (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1) (n : ℕ) :
    ‖characterSource u n‖ ≤ Real.log n := by
  rw [norm_characterSource_eq hu n, vonMangoldt_apply]
  by_cases h : IsPrimePow n
  · rw [if_pos h]
    have hn1 : 1 < n := h.one_lt
    have hle : (n.minFac : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.minFac_le (by omega : 0 < n)
    refine Real.log_le_log ?_ hle
    have : 0 < n.minFac := Nat.minFac_pos n
    exact_mod_cast this
  · rw [if_neg h]
    rcases Nat.lt_or_ge n 1 with hn | hn
    · interval_cases n
      · simp
    · refine Real.log_nonneg ?_
      exact_mod_cast hn

/-- **Locality of the source.**  Changing the phases at primes whose square exceeds `y` changes the
source only at those primes, as far as `y`. -/
theorem characterSource_update {u c : ℕ → ℂ} {S : Finset ℕ} {y : ℝ}
    (hS : ∀ q ∈ S, Nat.Prime q) (hSy : ∀ q ∈ S, y < (q : ℝ) ^ 2)
    {n : ℕ} (hn : (n : ℝ) ≤ y) :
    characterSource (fun m => if m ∈ S then c m else u m) n
      = if n ∈ S then c n * ((Real.log n : ℝ) : ℂ) else characterSource u n := by
  classical
  by_cases hmem : n ∈ S
  · rw [if_pos hmem, characterSource_prime (hS n hmem), if_pos hmem]
  · rw [if_neg hmem]
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have hΛ : Λ n = 0 := by
        interval_cases n
        · simp
        · simp
      rw [characterSource_of_vonMangoldt_zero hΛ, characterSource_of_vonMangoldt_zero hΛ]
    · have hnpos : 0 < n := by omega
      have hminfac : n.minFac ∉ S := by
        intro hmf
        by_cases hprime : Nat.Prime n
        · rw [Nat.Prime.minFac_eq hprime] at hmf
          exact hmem hmf
        · have hsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self hnpos hprime
          have hsqR : ((n.minFac : ℝ)) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hsq
          have := hSy _ hmf
          linarith
      rw [characterSource, characterSource, if_neg hminfac]

/-- The source at `n` only sees the phases at most `n`. -/
theorem characterSource_congr {u u' : ℕ → ℂ} {n : ℕ} (h : ∀ m ≤ n, u m = u' m) :
    characterSource u n = characterSource u' n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hΛ : Λ 0 = 0 := by simp
    rw [characterSource_of_vonMangoldt_zero hΛ, characterSource_of_vonMangoldt_zero hΛ]
  · rw [characterSource, characterSource, h n.minFac (Nat.minFac_le hn)]

end GaloisForLFunctions.HTGeometry

end
