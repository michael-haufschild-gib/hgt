import GaloisForLFunctions.RHTower.Sieve.RateBridge

/-!
# The two-sided deviation set of the distinct prime count

Combining the two tails bounds the set of integers of an interval whose distinct prime count
deviates from normal order on either side.  Both contributions carry the entropy rate
`I(w) = 1 - w + w log w` of `MobiusWoldBreadthTwoSidedDeviationRate.lean`, which is strictly
positive away from `w = 1`; so the deviation set is smaller than the interval by a genuine negative
power of `log z` on both sides.

Imposing squarefreeness only shrinks the set, so the bound applies verbatim to the squarefree
deviation set.
-/

namespace RHTower.Sieve

open Finset Nat
open scoped ArithmeticFunction.Moebius

/-- The two-sided deviation set of an interval. -/
def omegaDeviation (a b kLow kHigh : ℕ) : Finset ℕ :=
  {n ∈ Finset.Ioc a b | n.primeFactors.card ≤ kLow ∨ kHigh ≤ n.primeFactors.card}

/-- The deviation set is covered by the two one-sided sets. -/
theorem card_omegaDeviation_le_add (a b kLow kHigh : ℕ) :
    (omegaDeviation a b kLow kHigh).card
      ≤ (#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ kLow})
        + (#{n ∈ Finset.Ioc a b | kHigh ≤ n.primeFactors.card}) := by
  classical
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro n hn
  obtain ⟨hmem, hdev⟩ := Finset.mem_filter.1 hn
  rw [Finset.mem_union]
  rcases hdev with h | h
  · exact Or.inl (Finset.mem_filter.2 ⟨hmem, h⟩)
  · exact Or.inr (Finset.mem_filter.2 ⟨hmem, h⟩)

/-- **Two-sided deviation bound.**  Both contributions are the interval length times a negative
power of `log z` carrying the entropy rate, plus the explicit sieve errors. -/
theorem card_omegaDeviation_le (a b z kLow kHigh r k' J c D : ℕ) (hab : a ≤ b) (hz : 2 ≤ z)
    (hzb : z ≤ b) (hr : Even r) (hJ : 1 ≤ J) (hc : 1 ≤ c) (hD : b < (D + 1) ^ c)
    (hk : k' + c * J ≤ kHigh + 1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hkt : (kLow : ℝ) = t * logLog z)
    {u : ℝ} (hu1 : 1 ≤ u) (hu2 : u ≤ 2) (hku : (k' : ℝ) = u * logLog z)
    {lam : ℝ} (hlam : 1 ≤ lam) {v : ℝ} (hv : 1 ≤ v) :
    ((omegaDeviation a b kLow kHigh).card : ℝ)
      ≤ (((b : ℝ) - a) * (Real.exp ((1 - t) * mertensSecondLowerConst)
                * (Real.log z) ^ (-woldBreadthDeviationRate t)
              + Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam
                  / (lam ^ r * t ^ kLow))
            + ((truncDivisors (primorial z) r).card : ℝ) / t ^ kLow)
        + (((b : ℝ) - a) * (Real.exp ((u - 1) * mertensSecondUpperConst)
                * (Real.log z) ^ (-woldBreadthDeviationRate u))
            + ((truncDivisors (primorial z) k').card : ℝ) / u ^ k'
          + (((b : ℝ) - a) * (Real.exp (v * (mertensS b - mertensS z)) / v ^ J) + (D : ℝ))) := by
  have hsplit : ((omegaDeviation a b kLow kHigh).card : ℝ)
      ≤ ((#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ kLow} : ℕ) : ℝ)
        + ((#{n ∈ Finset.Ioc a b | kHigh ≤ n.primeFactors.card} : ℕ) : ℝ) := by
    exact_mod_cast card_omegaDeviation_le_add a b kLow kHigh
  have hlow := card_omega_le_le_rate a b z kLow r hab hz hr ht0 ht1 hkt hlam
  have hupp := card_omega_ge_le_rate a b z kHigh k' J c D hab hz hzb hJ hc hD hk hu1 hu2 hku hv
  linarith

/-- The squarefree deviation set of the card is contained in the deviation set, so the same bound
applies. -/
theorem card_squarefree_omegaDeviation_le (a b kLow kHigh : ℕ) :
    (#{n ∈ Finset.Ioc a b | (μ n ≠ 0)
          ∧ (n.primeFactors.card ≤ kLow ∨ kHigh ≤ n.primeFactors.card)})
      ≤ (omegaDeviation a b kLow kHigh).card := by
  classical
  refine Finset.card_le_card ?_
  intro n hn
  obtain ⟨hmem, -, hdev⟩ := Finset.mem_filter.1 hn
  exact Finset.mem_filter.2 ⟨hmem, hdev⟩

end RHTower.Sieve
