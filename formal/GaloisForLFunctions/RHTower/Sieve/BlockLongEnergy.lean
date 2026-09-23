import GaloisForLFunctions.RHTower.Sieve.MaskedSymmetry

/-!
# The long-side coefficient energy of a dyadic block

On a block `[P, Q)` the long-side energy is at most `log L` times the Chebyshev mass of `[1, Q)`,
which the corpus's linear bound makes `≪ Q log L`.  For a dyadic block `Q ≍ 2P`, so this is
`≪ P log L` — the proportionality to the BLOCK length that makes the type-II estimate nontrivial.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction RHTower

noncomputable section

/-- **The long-side energy of a block.** -/
theorem exists_sum_typeIILong_sq_block_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (U P Q L : ℕ), 1 ≤ L → Q ≤ L + 1 →
      (∑ d ∈ Finset.Ico P Q, ‖((typeIILong U d : ℝ) : ℂ)‖ ^ (2 : ℕ))
        ≤ C * (Q : ℝ) * Real.log (L : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := exists_chebyshevPsiReal_le_linear
  refine ⟨C, hC0, ?_⟩
  intro U P Q L hL hQL
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hlogL : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_nonneg hL1
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · subst hQ
    simp only [Finset.Ico_eq_empty_of_le (Nat.zero_le P), Finset.sum_empty]
    positivity
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hstep : ∀ d ∈ Finset.Ico P Q,
      ‖((typeIILong U d : ℝ) : ℂ)‖ ^ (2 : ℕ) ≤ Real.log (L : ℝ) * vonMangoldt d := by
    intro d hd
    rw [Finset.mem_Ico] at hd
    have hnorm : ‖((typeIILong U d : ℝ) : ℂ)‖ = |typeIILong U d| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    have h1 : |typeIILong U d| ≤ vonMangoldt d := abs_vonMangoldt_sub_truncAF_le U d
    have h2 : vonMangoldt d ≤ Real.log (d : ℝ) := ArithmeticFunction.vonMangoldt_le_log
    have h3 : Real.log (d : ℝ) ≤ Real.log (L : ℝ) := by
      rcases Nat.eq_zero_or_pos d with hd0 | hd0
      · rw [hd0]
        simpa using hlogL
      · refine Real.log_le_log (by exact_mod_cast hd0) ?_
        have : d ≤ L := by omega
        exact_mod_cast this
    have h0 : (0 : ℝ) ≤ |typeIILong U d| := abs_nonneg _
    nlinarith [h1, h2, h3, h0, ArithmeticFunction.vonMangoldt_nonneg (n := d)]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  have hzero : (vonMangoldt 0 : ℝ) = 0 := by simp
  have hsub : (∑ d ∈ Finset.Ico P Q, vonMangoldt d) ≤ ∑ d ∈ Finset.Icc 1 Q, vonMangoldt d := by
    rw [← Finset.sum_erase (Finset.Ico P Q) hzero]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun d _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    intro d hd
    have hd0 : d ≠ 0 := Finset.ne_of_mem_erase hd
    have hdm := Finset.mem_of_mem_erase hd
    rw [Finset.mem_Ico] at hdm
    rw [Finset.mem_Icc]
    omega
  have hpsi : (∑ d ∈ Finset.Icc 1 Q, vonMangoldt d) = chebyshevPsiReal (Q : ℝ) := by
    rw [chebyshevPsiReal_eq_sum_range, Nat.floor_natCast, sum_range_succ_vonMangoldt_eq_sum_Icc]
  rw [hpsi] at hsub
  have hle := hC (Q : ℝ) hQ1
  nlinarith [hsub, hle, hlogL, chebyshevPsiReal_nonneg (Q : ℝ)]

end

end RHTower.Sieve
