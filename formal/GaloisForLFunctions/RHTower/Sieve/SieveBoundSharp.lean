import GaloisForLFunctions.RHTower.Sieve.MontgomerySharp

/-!
# The sieve bound at the classical constant

The usable forms of `SieveBound.lean` and `SquareSieve.lean`, restated with the sharp constant of
`MontgomerySharp.lean`:

`|A| ∑_{p ∈ P} w_p/(p - w_p) ≤ Q² + 4πN`,  `|A| ≤ (Q² + 4πN)/L`,

and, for a set omitting half the classes modulo each prime of `P`,

`|A| ≤ 3(Q² + 4πN)/|P|`.

Only the analytic input differs from the versions with the logarithmic constant; the deficiency
estimate `deficiency_ge` and the `1/3` of `third_le_ratio` are reused unchanged.
-/

namespace RHTower.Sieve

open Finset

/-- **The sieve in terms of omitted classes, at the classical constant.** -/
theorem card_mul_omitted_le_sharp (N : ℕ) (hN : 0 < N) {Q : ℕ} (hQ : 2 ≤ Q) (A : Finset ℕ)
    (hA : A ⊆ Finset.range N) (hAne : A.Nonempty)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Q)
    (w : ℕ → ℝ) (hwp : ∀ p ∈ P, w p < (p : ℝ))
    (hocc : ∀ p ∈ P, ((occupiedClasses p A).card : ℝ) + w p ≤ (p : ℝ)) :
    (A.card : ℝ) * ∑ p ∈ P, w p / ((p : ℝ) - w p)
      ≤ (Q : ℝ) ^ (2 : ℕ) + 4 * Real.pi * (N : ℝ) := by
  have hbase := montgomery_sieve_sharp N hN hQ A hA hAne P hP
  have hcard : (0 : ℝ) ≤ (A.card : ℝ) := by positivity
  have hmono : ∑ p ∈ P, w p / ((p : ℝ) - w p)
      ≤ ∑ p ∈ P, ((p : ℝ) - ((occupiedClasses p A).card : ℝ))
          / ((occupiedClasses p A).card : ℝ) := by
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨hprime, _⟩ := hP p hp
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    have hcpos : (0 : ℝ) < ((occupiedClasses p A).card : ℝ) := by
      exact_mod_cast occupiedClasses_card_pos hprime.pos hAne
    exact deficiency_ge hppos hcpos (hwp p hp) (hocc p hp)
  exact le_trans (mul_le_mul_of_nonneg_left hmono hcard) hbase

/-- **The sieve bound on the cardinality, at the classical constant.** -/
theorem card_le_of_sieve_sharp (N : ℕ) (hN : 0 < N) {Q : ℕ} (hQ : 2 ≤ Q) (A : Finset ℕ)
    (hA : A ⊆ Finset.range N) (hAne : A.Nonempty)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Q)
    (w : ℕ → ℝ) (hwp : ∀ p ∈ P, w p < (p : ℝ))
    (hocc : ∀ p ∈ P, ((occupiedClasses p A).card : ℝ) + w p ≤ (p : ℝ))
    {L : ℝ} (hL : 0 < L) (hLle : L ≤ ∑ p ∈ P, w p / ((p : ℝ) - w p)) :
    (A.card : ℝ) ≤ ((Q : ℝ) ^ (2 : ℕ) + 4 * Real.pi * (N : ℝ)) / L := by
  have hbase := card_mul_omitted_le_sharp N hN hQ A hA hAne P hP w hwp hocc
  have hcard : (0 : ℝ) ≤ (A.card : ℝ) := by positivity
  rw [le_div_iff₀ hL]
  exact le_trans (mul_le_mul_of_nonneg_left hLle hcard) hbase

/-- **A set omitting half the classes is small, at the classical constant.** -/
theorem card_le_of_half_omitted_sharp (N : ℕ) (hN : 0 < N) {Q : ℕ} (hQ : 2 ≤ Q) (A : Finset ℕ)
    (hA : A ⊆ Finset.range N) (hAne : A.Nonempty)
    (P : Finset ℕ) (hPne : P.Nonempty) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Q)
    (w : ℕ → ℝ) (hhalf : ∀ p ∈ P, ((p : ℝ) - 1) / 2 ≤ w p)
    (hwp : ∀ p ∈ P, w p < (p : ℝ))
    (hocc : ∀ p ∈ P, ((occupiedClasses p A).card : ℝ) + w p ≤ (p : ℝ)) :
    (A.card : ℝ)
      ≤ 3 * ((Q : ℝ) ^ (2 : ℕ) + 4 * Real.pi * (N : ℝ)) / (P.card : ℝ) := by
  have hPcard : (0 : ℝ) < (P.card : ℝ) := by
    have := Finset.card_pos.mpr hPne
    exact_mod_cast this
  have hratio : ∀ p ∈ P, (1 : ℝ) / 3 ≤ w p / ((p : ℝ) - w p) := by
    intro p hp
    obtain ⟨hprime, _⟩ := hP p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
    exact third_le_ratio hp2 (hhalf p hp) (hwp p hp)
  have hL : (P.card : ℝ) / 3 ≤ ∑ p ∈ P, w p / ((p : ℝ) - w p) := by
    have hconst : ∑ _p ∈ P, (1 : ℝ) / 3 = (P.card : ℝ) / 3 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    rw [← hconst]
    exact Finset.sum_le_sum hratio
  have hLpos : (0 : ℝ) < (P.card : ℝ) / 3 := by positivity
  have hbase := card_le_of_sieve_sharp N hN hQ A hA hAne P hP w hwp hocc hLpos hL
  have heq : ((Q : ℝ) ^ (2 : ℕ) + 4 * Real.pi * (N : ℝ)) / ((P.card : ℝ) / 3)
      = 3 * ((Q : ℝ) ^ (2 : ℕ) + 4 * Real.pi * (N : ℝ)) / (P.card : ℝ) := by
    rw [div_div_eq_mul_div, mul_comm]
  rw [heq] at hbase
  exact hbase

end RHTower.Sieve
