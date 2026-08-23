import GaloisForLFunctions.RHTower.Sieve.WeightedTailDef

/-!
# The weighted tail, reduced to its inner sums

The triangle inequality over the `r`-sum reduces the card's `E_Λ(T)` to the harmonically weighted
total of the inner prime sums `S_r`, which is the form the exponent budget adds up.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction RHTower

noncomputable section

/-- **The tail is at most the harmonic total of its inner sums.** -/
theorem norm_weightedNearDiagonalTail_le (T ε : ℝ) (hε : 0 ≤ ε) (mLo mHi rLo : ℕ) :
    ‖weightedNearDiagonalTail T ε mLo mHi rLo‖
      ≤ ∑ r ∈ Finset.Icc rLo ⌊(mHi : ℝ) * ε⌋₊,
          ‖∑ m ∈ (Finset.Icc mLo mHi).filter
              (fun m : ℕ => r ≤ ⌊(m : ℝ) * ε⌋₊ ∧ r % 2 = m % 2),
              ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T r m‖ / (r : ℝ) := by
  classical
  rw [weightedNearDiagonalTail_swap T ε hε mLo mHi rLo]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun r _ => ?_
  have hfac : (∑ m ∈ (Finset.Icc mLo mHi).filter
      (fun m : ℕ => r ≤ ⌊(m : ℝ) * ε⌋₊ ∧ r % 2 = m % 2),
      ((vonMangoldt m : ℝ) : ℂ) * (ndPhaseExp T r m / (r : ℂ)))
      = (∑ m ∈ (Finset.Icc mLo mHi).filter
          (fun m : ℕ => r ≤ ⌊(m : ℝ) * ε⌋₊ ∧ r % 2 = m % 2),
          ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T r m) / (r : ℂ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hfac, norm_div, Complex.norm_natCast]

/-- **The parity class of a block sum.**  Whichever class `r` selects, the restricted sum differs
from the unrestricted one by at most `log B`. -/
theorem norm_sum_parity_le {T rr : ℝ} {A B r : ℕ} (hB : 1 ≤ B) :
    ‖∑ m ∈ (Finset.Ico A B).filter (fun m : ℕ => r % 2 = m % 2),
        ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T rr m‖
      ≤ ‖∑ m ∈ Finset.Ico A B, ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T rr m‖
        + Real.log (B : ℝ) := by
  classical
  rcases Nat.even_or_odd r with he | ho
  · have hr : r % 2 = 0 := Nat.even_iff.1 he
    have hfilter : (Finset.Ico A B).filter (fun m : ℕ => r % 2 = m % 2)
        = (Finset.Ico A B).filter (fun m : ℕ => 2 ∣ m) := by
      refine Finset.filter_congr fun m _ => ?_
      rw [hr]
      constructor
      · intro h
        omega
      · intro h
        omega
    rw [hfilter]
    have hnn : (0 : ℝ) ≤ ‖∑ m ∈ Finset.Ico A B,
        ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T rr m‖ := norm_nonneg _
    linarith [norm_sum_even_le (T := T) (r := rr) (A := A) hB]
  · have hr : r % 2 = 1 := Nat.odd_iff.1 ho
    have hfilter : (Finset.Ico A B).filter (fun m : ℕ => r % 2 = m % 2)
        = (Finset.Ico A B).filter (fun m : ℕ => ¬ 2 ∣ m) := by
      refine Finset.filter_congr fun m _ => ?_
      rw [hr]
      constructor
      · intro h
        omega
      · intro h
        omega
    rw [hfilter]
    exact norm_sum_odd_le hB

end

end RHTower.Sieve
