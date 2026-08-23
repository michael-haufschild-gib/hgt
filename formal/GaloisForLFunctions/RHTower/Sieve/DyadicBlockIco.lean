import GaloisForLFunctions.RHTower.Sieve.AdicBlocks

/-!
# The dyadic blocks of an initial segment are intervals

The corpus's dyadic decomposition of `[1, M]` indexes blocks by `⌊log₂ n⌋`.  Identifying the
`j`-th block with the interval `[2^j, min(2^{j+1}, M+1))` is what lets the block estimates, which
are stated for `Finset.Ico`, be applied to it.
-/

namespace RHTower.Sieve

open Finset

/-- **The `j`-th dyadic block of `[1, M]` is an interval.** -/
theorem dyadic_block_eq_Ico (M j : ℕ) :
    (Finset.Icc 1 M).filter (fun n => Nat.log 2 n = j)
      = Finset.Ico (2 ^ j) (min (2 ^ (j + 1)) (M + 1)) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico, lt_min_iff]
  constructor
  · rintro ⟨⟨hn1, hnM⟩, hlog⟩
    have h1 : 2 ^ j ≤ n := by
      rw [← hlog]
      exact Nat.pow_log_le_self 2 (by omega)
    have h2 : n < 2 ^ (j + 1) := by
      rw [← hlog]
      exact Nat.lt_pow_succ_log_self (by norm_num) n
    exact ⟨h1, h2, by omega⟩
  · rintro ⟨h1, h2, h3⟩
    have hn1 : 1 ≤ n := le_trans (Nat.one_le_two_pow) h1
    refine ⟨⟨hn1, by omega⟩, ?_⟩
    have hge : j ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) h1
    have hlt : Nat.log 2 n < j + 1 :=
      (Nat.log_lt_iff_lt_pow (b := 2) (by norm_num) (by omega)).2 h2
    omega

end RHTower.Sieve
