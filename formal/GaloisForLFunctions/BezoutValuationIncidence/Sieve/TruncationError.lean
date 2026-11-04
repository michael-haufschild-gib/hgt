import GaloisForLFunctions.RHTower.Sieve.IntervalSelberg

/-!
# A polynomial remainder bound for truncated Selberg weights

Unit weights and support below the square of the truncation give a sixth-power
bound for the absolute quadratic coefficient mass. The bound is uniform in
the squarefree sieve modulus and its local density.
-/

noncomputable section

namespace GaloisForLFunctions.BezoutValuationIncidence

open Finset Nat BoundingSieve
open _root_.RHTower.Sieve

/-- The quadratic Selberg coefficient mass is at most the sixth power of its truncation. -/
theorem sum_abs_selbergTruncSquared_le_pow_six (s : BoundingSieve) {Y : ℕ} (hY : 1 ≤ Y) :
    ∑ d ∈ s.prodPrimes.divisors,
      |lambdaSquared (selbergTruncWeight s Y) d| ≤ (Y : ℝ) ^ 6 := by
  classical
  have hw : ∀ n, |selbergTruncWeight s Y n| ≤ 1 := by
    intro n
    by_cases hn : n ∣ s.prodPrimes
    · exact abs_selbergTruncWeight_le_one s hn hY
    · have hz : selbergTruncWeight s Y n = 0 := by
        unfold selbergTruncWeight selbergW
        have hnum : ∀ l ∈ s.prodPrimes.divisors,
            (if n ∣ l then (ArithmeticFunction.moebius (l / n) : ℝ) *
              selbergTruncY s Y l else 0) = 0 := by
          intro l hl
          by_cases hnl : n ∣ l
          · exact absurd (hnl.trans (Nat.dvd_of_mem_divisors hl)) hn
          · rw [if_neg hnl]
        rw [sum_congr rfl hnum, sum_const_zero, zero_div]
      rw [hz, abs_zero]
      exact zero_le_one
  let T := s.prodPrimes.divisors.filter (fun d => d ≤ Y * Y)
  have hsub : T ⊆ Icc 1 (Y * Y) := by
    intro d hd
    obtain ⟨hd, hdY⟩ := mem_filter.mp hd
    exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, hdY⟩
  have hcard : (T.card : ℝ) ≤ (Y : ℝ) ^ 2 := by
    have h := card_le_card hsub
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at h
    exact_mod_cast (show T.card ≤ Y ^ 2 by simpa only [pow_two] using h)
  have hterm (d : ℕ) (hd : d ∈ T) :
      |lambdaSquared (selbergTruncWeight s Y) d| ≤ (Y : ℝ) ^ 4 := by
    have hdY : d ≤ Y * Y := (mem_filter.mp hd).2
    have hdcard : d.divisors.card ≤ d := by
      have hsubd : d.divisors ⊆ Icc 1 d := fun e he =>
        mem_Icc.mpr ⟨Nat.pos_of_mem_divisors he, Nat.divisor_le he⟩
      simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hsubd
    have hcardY : (d.divisors.card : ℝ) ≤ (Y : ℝ) ^ 2 := by
      exact_mod_cast (show d.divisors.card ≤ Y ^ 2 by
        simpa only [pow_two] using hdcard.trans hdY)
    refine (abs_lambdaSquared_le_card_sq hw d).trans ?_
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hcardY 2).trans_eq (by ring)
  have hrestrict : (∑ d ∈ s.prodPrimes.divisors,
      |lambdaSquared (selbergTruncWeight s Y) d|) =
      ∑ d ∈ T, |lambdaSquared (selbergTruncWeight s Y) d| := by
    apply (sum_subset (filter_subset _ _) ?_).symm
    intro d hd hnot
    have hlt : Y * Y < d := by
      by_contra h
      exact hnot (mem_filter.mpr ⟨hd, by omega⟩)
    rw [lambdaSquared_selbergTruncWeight_eq_zero s hlt, abs_zero]
  rw [hrestrict]
  calc
    _ ≤ ∑ _d ∈ T, (Y : ℝ) ^ 4 := sum_le_sum hterm
    _ = (T.card : ℝ) * (Y : ℝ) ^ 4 := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (Y : ℝ) ^ 2 * (Y : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

#print axioms sum_abs_selbergTruncSquared_le_pow_six

end GaloisForLFunctions.BezoutValuationIncidence
