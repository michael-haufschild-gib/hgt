import GaloisForLFunctions.RHTower.Sieve.MertensProductLower

/-!
# The harmonic mass of the pair sieve

The truncation hypothesis of the bounding sum asks that the number of permitted prime factors exceed
`e·∑_p a_p + log 2`, where `a_p` is the local Selberg term.  Since `a_p ≤ 4/p` at every sifting
prime above `4`, that sum is at most four Mertens differences — so the hypothesis becomes a
comparison between `k` and `log(log hN / log P₁)`, which is where the parameters are chosen.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The local Selberg terms are at most `4/p`.** -/
theorem pairClassTerm_le {d p : ℕ} (hp : 4 ≤ p) :
    pairClassCount d p / ((p : ℝ) - pairClassCount d p) ≤ 4 / (p : ℝ) := by
  have hp4 : (4 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  rw [pairClassCount]
  split_ifs
  · rw [div_le_div_iff₀ (by linarith) hp0]
    linarith
  · rw [div_le_div_iff₀ (by linarith) hp0]
    linarith

/-- **The harmonic mass of the pair sieve is at most four Mertens differences.** -/
theorem sum_pairClassTerm_le {P₁ hN : ℕ} (hP₁ : 4 ≤ P₁) (hP₁h : P₁ ≤ hN) (d : ℕ) :
    (∑ p ∈ rangePrimes P₁ hN, pairClassCount d p / ((p : ℝ) - pairClassCount d p))
      ≤ 4 * (mertensS hN - mertensS P₁) := by
  classical
  have hterm : ∀ p ∈ rangePrimes P₁ hN,
      pairClassCount d p / ((p : ℝ) - pairClassCount d p) ≤ 4 * (1 / (p : ℝ)) := by
    intro p hp
    rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
    have hp4 : 4 ≤ p := by omega
    rw [show (4 : ℝ) * (1 / (p : ℝ)) = 4 / (p : ℝ) by ring]
    exact pairClassTerm_le hp4
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, rangePrimes_eq_primesRange, sum_inv_primesRange hP₁h]

end

end RHTower.Sieve
