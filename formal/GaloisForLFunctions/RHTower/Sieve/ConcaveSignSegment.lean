import GaloisForLFunctions.RHTower.Sieve.ErrorShiftSum

/-!
# A concave sequence starting nonnegative is positive on an initial segment

The sign of the smooth kernel's increment is governed by

```text
P(n) = x(n+k)(n+1+k) − (x + h√x)·n(n+1) = −h√x·n² + (2kx − h√x)·n + xk(k+1) ,
```

a downward parabola with `P(0) = xk(k+1) > 0`.  So `P` is nonnegative on an initial segment and
negative after, which is exactly the statement that the smooth kernel increases and then decreases —
the bimonotonicity `variation_le_two_range_of_bimonotone` requires.

The argument needs nothing about parabolas, only concavity: the increments of a concave sequence are
nonincreasing, so once the sequence has dropped below its starting value it keeps dropping.
-/

namespace RHTower.Sieve

open Finset

/-- The increments of a concave sequence are nonincreasing. -/
theorem increment_antitone {P : ℕ → ℝ}
    (hconc : ∀ n, P (n + 2) - P (n + 1) ≤ P (n + 1) - P n) :
    Antitone (fun n => P (n + 1) - P n) :=
  antitone_nat_of_succ_le fun n => hconc n

/-- **A concave sequence starting nonnegative stays negative once it turns negative.** -/
theorem neg_of_concave_of_neg {P : ℕ → ℝ}
    (hconc : ∀ n, P (n + 2) - P (n + 1) ≤ P (n + 1) - P n) (h0 : 0 ≤ P 0)
    {n : ℕ} (hn : P n < 0) : ∀ m, n ≤ m → P m < 0 := by
  classical
  -- some increment before `n` is negative
  have hex : ∃ j, j < n ∧ P (j + 1) - P j < 0 := by
    by_contra hc
    simp only [not_exists, not_and, not_lt] at hc
    have hmono : ∀ i, i ≤ n → P 0 ≤ P i := by
      intro i hi
      induction i with
      | zero => exact le_rfl
      | succ j ih =>
          have hj : j ≤ n := by omega
          have := hc j (by omega)
          linarith [ih hj]
    linarith [hmono n le_rfl]
  obtain ⟨j, hjn, hjneg⟩ := hex
  have hanti := increment_antitone hconc
  have hdrop : ∀ m, j ≤ m → P (m + 1) - P m < 0 := by
    intro m hm
    have := hanti hm
    simp only at this
    linarith [hjneg]
  intro m hm
  induction m with
  | zero =>
      have : n = 0 := by omega
      rwa [← this]
  | succ i ih =>
      rcases Nat.lt_or_ge n (i + 1) with hlt | hge
      · have hni : n ≤ i := by omega
        have hPi := ih hni
        have := hdrop i (by omega)
        linarith
      · have : n = i + 1 := by omega
        rwa [← this]

end RHTower.Sieve
