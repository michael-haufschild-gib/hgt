import GaloisForLFunctions.PrimeTorusTheory.TarryEscottWords
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteDifference.BinomialResidueSpread

/-!
# Residue escape for balanced words

A nonzero word with zero total mass has a nonzero coefficient of positive
index. Its binomial polynomial therefore cannot be constant modulo any
integer greater than one. Short-interval rigidity forces a residue outside
every interval below the degree-dependent threshold.
-/

namespace GaloisForLFunctions.PrimeTorusTheory
open Finset Function
open GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- A balanced nonzero word has a nonzero coefficient away from the origin. -/
theorem balanced_word_positive_letter {M : ℕ} {c : ℕ → ℤ}
    (hc : IsWord M c) (hbalance : binomMoment M c 0 = 0) :
    ∃ i, 1 ≤ i ∧ i ≤ M ∧ c i ≠ 0 := by
  by_contra hn
  have hz : ∀ i, 1 ≤ i → i ≤ M → c i = 0 := by
    intro i hi hiM
    by_contra hci
    exact hn ⟨i, hi, hiM, hci⟩
  have h0 : c 0 = 0 := by
    unfold binomMoment at hbalance
    simp only [Nat.choose_zero_right, Nat.cast_one, mul_one] at hbalance
    have he : (∑ i ∈ range (M + 1), c i) = c 0 := by
      apply sum_eq_single 0
      · intro i hi hne
        exact hz i (by omega) (by have := mem_range.mp hi; omega)
      · intro h
        exact False.elim (h (mem_range.mpr (Nat.zero_lt_succ M)))
    rwa [he] at hbalance
  obtain ⟨i, hi⟩ := hc.ne_zero
  by_cases hi0 : i = 0
  · exact hi (hi0 ▸ h0)
  · exact hi (hz i (by omega) (by
      by_contra hiM
      exact hi (hc.support i (by omega))))

/-- The binomial phase of a balanced word is nonconstant modulo every modulus above one. -/
theorem balanced_word_binomial_nonconstant {M : ℕ} {c : ℕ → ℤ}
    (hc : IsWord M c) (hbalance : binomMoment M c 0 = 0) (k : ℤ) (hk : 1 < k) :
    ¬ ∀ j, binomialSequence M c j ≡ c 0 [ZMOD k] := by
  intro he
  obtain ⟨i, hi, hiM, hci⟩ := balanced_word_positive_letter hc hbalance
  have hd := (binomialSequence_constant_mod_iff M c k).mp he i hi hiM
  obtain ⟨a, ha⟩ := hd
  have hb := abs_le.mp (hc.bound i)
  have ha0 : a = 0 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hn | hn
    · have hm := mul_le_mul_of_nonneg_left (show a ≤ -1 by omega) (show 0 ≤ k by omega)
      nlinarith only [ha, hm, hb.1, hk]
    · have hm := mul_le_mul_of_nonneg_left (show 1 ≤ a by omega) (show 0 ≤ k by omega)
      nlinarith only [ha, hm, hb.2, hk]
  exact hci (by simpa only [ha0, mul_zero] using ha)

/-- Balanced word phases must escape every sufficiently short residue interval. -/
theorem balanced_word_binomial_residue_escape {M : ℕ} {c : ℕ → ℤ}
    (hc : IsWord M c) (hbalance : binomMoment M c 0 = 0) (D k : ℤ)
    (hk : 1 < k) (hsize : 2 ^ M * D < k) :
    ∃ j, D < binomialSequence M c j % k := by
  by_contra hn
  have hb : ∀ j, binomialSequence M c j % k ≤ D := by
    intro j
    by_contra hj
    exact hn ⟨j, lt_of_not_ge hj⟩
  have hd := ((binomialSequence_short_residues_iff M c D k (by omega) hsize).mp hb).2
  exact balanced_word_binomial_nonconstant hc hbalance k hk
    ((binomialSequence_constant_mod_iff M c k).mpr hd)

end GaloisForLFunctions.PrimeTorusTheory

#print axioms GaloisForLFunctions.PrimeTorusTheory.balanced_word_positive_letter
#print axioms GaloisForLFunctions.PrimeTorusTheory.balanced_word_binomial_nonconstant
#print axioms GaloisForLFunctions.PrimeTorusTheory.balanced_word_binomial_residue_escape
