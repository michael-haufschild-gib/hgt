import GaloisForLFunctions.RHTower.Sieve.MontgomeryInequality

/-!
# The sieve bound in usable form

`MontgomeryInequality.lean` bounds `|A|` against the *occupancy* `c_p`.  Applications instead
specify how many classes are omitted: if `A` misses at least `w_p` residue classes modulo `p`, then

`(p - c_p) / c_p ≥ w_p / (p - w_p)`,

because the deficiency ratio decreases as occupancy grows.  Substituting gives the sieve in the form
it is quoted,

`|A| ∑_{p ∈ P} w_p / (p - w_p) ≤ N + Q²(1 + log(Q²/2 + 1))`,

and dividing by any positive lower bound for the sum bounds `|A|` outright.
-/

namespace RHTower.Sieve

open Finset

/-- The deficiency ratio decreases as occupancy grows. -/
theorem deficiency_ge {p w c : ℝ} (hp : 0 < p) (hc : 0 < c) (hwp : w < p)
    (hcw : c + w ≤ p) : w / (p - w) ≤ (p - c) / c := by
  rw [div_le_div_iff₀ (by linarith) hc]
  nlinarith [mul_nonneg hp.le (by linarith : (0 : ℝ) ≤ p - w - c)]

/-- **The sieve in terms of omitted classes.** -/
theorem card_mul_omitted_le (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (A : Finset ℕ)
    (hA : A ⊆ Finset.range N) (hAne : A.Nonempty)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Q)
    (w : ℕ → ℝ) (hwp : ∀ p ∈ P, w p < (p : ℝ))
    (hocc : ∀ p ∈ P, ((occupiedClasses p A).card : ℝ) + w p ≤ (p : ℝ)) :
    (A.card : ℝ) * ∑ p ∈ P, w p / ((p : ℝ) - w p)
      ≤ (N : ℝ) + (Q : ℝ) ^ (2 : ℕ) * (1 + Real.log ((Q : ℝ) ^ (2 : ℕ) / 2 + 1)) := by
  have hbase := montgomery_sieve N hQ A hA hAne P hP
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

/-- **The sieve bound on the cardinality.** -/
theorem card_le_of_sieve (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (A : Finset ℕ)
    (hA : A ⊆ Finset.range N) (hAne : A.Nonempty)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Q)
    (w : ℕ → ℝ) (hwp : ∀ p ∈ P, w p < (p : ℝ))
    (hocc : ∀ p ∈ P, ((occupiedClasses p A).card : ℝ) + w p ≤ (p : ℝ))
    {L : ℝ} (hL : 0 < L) (hLle : L ≤ ∑ p ∈ P, w p / ((p : ℝ) - w p)) :
    (A.card : ℝ)
      ≤ ((N : ℝ) + (Q : ℝ) ^ (2 : ℕ) * (1 + Real.log ((Q : ℝ) ^ (2 : ℕ) / 2 + 1))) / L := by
  have hbase := card_mul_omitted_le N hQ A hA hAne P hP w hwp hocc
  have hcard : (0 : ℝ) ≤ (A.card : ℝ) := by positivity
  rw [le_div_iff₀ hL]
  exact le_trans (mul_le_mul_of_nonneg_left hLle hcard) hbase

end RHTower.Sieve
