import GaloisForLFunctions.RHTower.MobiusDivisorArityHeadSourcePairs
import GaloisForLFunctions.RHTower.MobiusDivisorAbelDiagonalBound

/-!
# Weighted cutoff transport for the literal Möbius-divisor diagonal

The completed arity-head entrance cost is positive at any fixed cutoff, but
its cutoff successor has an exact signed mixed source term.  This module keeps
both that term and its positive quadratic remainder, for arbitrary fixed
source-index weights and then for the literal squarefree-rank weight.
-/

noncomputable section
open Finset

namespace RHTower

/-- Every fixed source-index weighting obeys the exact literal cutoff successor
law.  The mixed term retains its Möbius sign; the second term is the complete
new-square remainder. -/
theorem sum_weighted_mobiusDivisorDilationChannel_sq_succ_sub
    (w : ℕ → ℝ) (M : ℕ) :
    (∑ d ∈ Icc 1 (M + 1), w d * mobiusDivisorDilationChannel (M + 1) d ^ (2 : ℕ)) -
      (∑ d ∈ Icc 1 M, w d * mobiusDivisorDilationChannel M d ^ (2 : ℕ)) =
    2 * (Real.sqrt (M + 1 : ℕ) - Real.sqrt M) *
      (∑ d ∈ Icc 1 M, w d * mobiusDivisorDilationChannel M d *
        (((ArithmeticFunction.moebius d : ℤ) : ℝ) * primeFreeDivisorDefect (M / d))) +
    (Real.sqrt (M + 1 : ℕ) - Real.sqrt M) ^ (2 : ℕ) *
      ∑ d ∈ Icc 1 M, w d *
        (((ArithmeticFunction.moebius d : ℤ) : ℝ) * primeFreeDivisorDefect (M / d)) ^ (2 : ℕ) := by
  have hzero : mobiusDivisorDilationChannel (M + 1) (M + 1) = 0 := by
    simp [mobiusDivisorDilationChannel]
  rw [Finset.sum_Icc_succ_top (show 1 ≤ M + 1 by omega), hzero]
  simp only [zero_pow (show 2 ≠ 0 by decide), mul_zero, add_zero]
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ d ∈ Icc 1 M, w d *
        (2 * (Real.sqrt (M + 1 : ℕ) - Real.sqrt M) *
          (mobiusDivisorDilationChannel M d *
            (((ArithmeticFunction.moebius d : ℤ) : ℝ) * primeFreeDivisorDefect (M / d))) +
        (Real.sqrt (M + 1 : ℕ) - Real.sqrt M) ^ (2 : ℕ) *
          (((ArithmeticFunction.moebius d : ℤ) : ℝ) * primeFreeDivisorDefect (M / d)) ^ (2 : ℕ)) := by
      apply sum_congr rfl
      intro d hd
      rw [mobiusDivisorDilationChannel_succ_of_le
        (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2]
      ring
    _ = _ := by
      simp_rw [mul_add]
      calc
        _ = (∑ d ∈ Icc 1 M, w d *
            (2 * (Real.sqrt (M + 1 : ℕ) - Real.sqrt M) *
              (mobiusDivisorDilationChannel M d *
                (((ArithmeticFunction.moebius d : ℤ) : ℝ) * primeFreeDivisorDefect (M / d)))) +
          ∑ d ∈ Icc 1 M, w d *
            ((Real.sqrt (M + 1 : ℕ) - Real.sqrt M) ^ (2 : ℕ) *
              (((ArithmeticFunction.moebius d : ℤ) : ℝ) * primeFreeDivisorDefect (M / d)) ^ (2 : ℕ))) := by
              rw [Finset.sum_add_distrib]
        _ = _ := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply congrArg₂ (· + ·)
          · apply sum_congr rfl
            intro d _
            ring
          · apply sum_congr rfl
            intro d _
            ring

/-- Literal rank weight of a squarefree source channel, completed by the empty
label boundary. -/
def mobiusDivisorArityHeadCutoffWeight (d : ℕ) : ℝ :=
  (d.primeFactors.card : ℝ) + if d.primeFactors = ∅ then 1 else 0

/-- The weighted source diagonal is unchanged by extending selection support to
the full cutoff: nonsquarefree channels and the terminal channel vanish. -/
theorem sum_mobiusDivisorSelectionIndices_weighted_sq_eq_full
    (w : ℕ → ℝ) (M : ℕ) :
    (∑ d ∈ mobiusDivisorSelectionIndices M,
      w d * mobiusDivisorDilationChannel M d ^ (2 : ℕ)) =
    ∑ d ∈ Icc 1 M, w d * mobiusDivisorDilationChannel M d ^ (2 : ℕ) := by
  apply sum_subset
  · intro d hd
    obtain ⟨hdI, _⟩ := mem_filter.mp hd
    obtain ⟨hdl, hdu⟩ := mem_Icc.mp hdI
    exact mem_Icc.mpr ⟨hdl, hdu.trans (Nat.sub_le _ _)⟩
  · intro d hd hnot
    by_cases hM : d = M
    · subst d
      have hMpos : 1 ≤ M := (mem_Icc.mp hd).1
      have hI : Icc M (M - 1) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro n hn
        have h := mem_Icc.mp hn
        omega
      simp [mobiusDivisorDilationChannel, hI]
    · have hdu : d ≤ M - 1 := by
        obtain ⟨_, hdu⟩ := mem_Icc.mp hd
        omega
      have hdI : d ∈ Icc 1 (M - 1) :=
        mem_Icc.mpr ⟨(mem_Icc.mp hd).1, hdu⟩
      have hns : ¬ Squarefree d := by
        intro hs
        exact hnot (mem_filter.mpr ⟨hdI, hs⟩)
      simp [mobiusDivisorDilationChannel_eq_moebius_unsigned,
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns]

/-- The actual completed entrance energy is exactly its full-cutoff weighted
source diagonal. -/
theorem mobiusDivisorArityHeadEnergy_empty_eq_cutoffDiagonal (M : ℕ) :
    mobiusDivisorArityHeadEnergy M ∅ =
      ∑ d ∈ Icc 1 M,
        mobiusDivisorArityHeadCutoffWeight d * mobiusDivisorDilationChannel M d ^ (2 : ℕ) := by
  rw [mobiusDivisorArityHeadEnergy_empty_eq_diagonal]
  exact sum_mobiusDivisorSelectionIndices_weighted_sq_eq_full
    mobiusDivisorArityHeadCutoffWeight M

/-- The positive completed entrance energy evolves through one literal signed
rank-weighted source correlation and its exact nonnegative quadratic remainder. -/
theorem mobiusDivisorArityHeadEnergy_empty_succ_sub (M : ℕ) :
    mobiusDivisorArityHeadEnergy (M + 1) ∅ - mobiusDivisorArityHeadEnergy M ∅ =
    2 * (Real.sqrt (M + 1 : ℕ) - Real.sqrt M) *
      (∑ d ∈ Icc 1 M, mobiusDivisorArityHeadCutoffWeight d *
        mobiusDivisorDilationChannel M d *
        (((ArithmeticFunction.moebius d : ℤ) : ℝ) * primeFreeDivisorDefect (M / d))) +
    (Real.sqrt (M + 1 : ℕ) - Real.sqrt M) ^ (2 : ℕ) *
      ∑ d ∈ Icc 1 M, mobiusDivisorArityHeadCutoffWeight d *
        (((ArithmeticFunction.moebius d : ℤ) : ℝ) * primeFreeDivisorDefect (M / d)) ^ (2 : ℕ) := by
  rw [mobiusDivisorArityHeadEnergy_empty_eq_cutoffDiagonal,
    mobiusDivisorArityHeadEnergy_empty_eq_cutoffDiagonal]
  exact sum_weighted_mobiusDivisorDilationChannel_sq_succ_sub
    mobiusDivisorArityHeadCutoffWeight M

end RHTower
