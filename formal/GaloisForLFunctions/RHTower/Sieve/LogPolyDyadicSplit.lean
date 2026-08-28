import GaloisForLFunctions.RHTower.Sieve.AdicBlocks
import GaloisForLFunctions.RHTower.Sieve.GallagherLemma

/-!
# An initial-segment Dirichlet polynomial, split into dyadic blocks

The corpus's Halász–Montgomery estimates are stated for coefficients supported on a *dyadic* range
`[N, 2N)`, while the Ramaré cofactor of the Möbius bilinear form is supported on an initial segment
`[1, M]`.  The bridge is the dyadic decomposition of the segment, whose cost is one Cauchy–Schwarz
factor `⌊log₂ M⌋ + 1`.

The decomposition itself is `Sieve/AdicBlocks.sum_Icc_eq_sum_dyadic_blocks`; what is added here is
its Dirichlet-polynomial form, the pointwise Cauchy–Schwarz bound, and the version summed over a
finite family of frequencies — the shape a per-block large-values estimate is consumed in.

* `logPoly_Icc_eq_sum_dyadicBlocks`;
* `normSq_logPoly_Icc_le_card_mul_sum_blocks`;
* `sum_normSq_logPoly_Icc_le_card_mul_sum_blocks`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The `j`-th dyadic block of the initial segment `[1, M]`. -/
def dyadicSegmentBlock (M j : ℕ) : Finset ℕ :=
  (Finset.Icc 1 M).filter (fun n => Nat.log 2 n = j)

theorem mem_dyadicSegmentBlock {M j n : ℕ} (hn : n ∈ dyadicSegmentBlock M j) :
    2 ^ j ≤ n ∧ n < 2 ^ (j + 1) := mem_dyadic_block hn

/-- **A Dirichlet polynomial on an initial segment is the sum of its dyadic blocks.** -/
theorem logPoly_Icc_eq_sum_dyadicBlocks (a : ℕ → ℂ) (M : ℕ) (w : ℝ) :
    logPoly a (Finset.Icc 1 M) w
      = ∑ j ∈ Finset.range (Nat.log 2 M + 1), logPoly a (dyadicSegmentBlock M j) w := by
  classical
  simp only [logPoly, dyadicSegmentBlock]
  exact (sum_Icc_eq_sum_dyadic_blocks
    (fun n => a n * Complex.exp (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I))).symm

/-- **The Cauchy–Schwarz cost of the dyadic split**, pointwise in the frequency. -/
theorem normSq_logPoly_Icc_le_card_mul_sum_blocks (a : ℕ → ℂ) (M : ℕ) (w : ℝ) :
    ‖logPoly a (Finset.Icc 1 M) w‖ ^ 2
      ≤ ((Nat.log 2 M + 1 : ℕ) : ℝ) *
          ∑ j ∈ Finset.range (Nat.log 2 M + 1), ‖logPoly a (dyadicSegmentBlock M j) w‖ ^ 2 := by
  classical
  have htri : ‖logPoly a (Finset.Icc 1 M) w‖
      ≤ ∑ j ∈ Finset.range (Nat.log 2 M + 1), ‖logPoly a (dyadicSegmentBlock M j) w‖ := by
    rw [logPoly_Icc_eq_sum_dyadicBlocks a M w]
    exact norm_sum_le _ _
  have hcs : (∑ j ∈ Finset.range (Nat.log 2 M + 1), ‖logPoly a (dyadicSegmentBlock M j) w‖) ^ 2
      ≤ (((Finset.range (Nat.log 2 M + 1)).card : ℕ) : ℝ) *
          ∑ j ∈ Finset.range (Nat.log 2 M + 1), ‖logPoly a (dyadicSegmentBlock M j) w‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [Finset.card_range] at hcs
  have hsq : ‖logPoly a (Finset.Icc 1 M) w‖ ^ 2
      ≤ (∑ j ∈ Finset.range (Nat.log 2 M + 1), ‖logPoly a (dyadicSegmentBlock M j) w‖) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖logPoly a (Finset.Icc 1 M) w‖ := norm_nonneg _
    nlinarith [htri, h0]
  exact hsq.trans hcs

/-- **The dyadic split, summed over a finite family of frequencies.**  This is the form in which a
per-block large-values estimate is applied: each dyadic block is a genuine dyadic Dirichlet
polynomial, and the whole cost of the reduction is the factor `⌊log₂ M⌋ + 1`. -/
theorem sum_normSq_logPoly_Icc_le_card_mul_sum_blocks (a : ℕ → ℂ) (M : ℕ) (P : Finset ℝ) :
    ∑ w ∈ P, ‖logPoly a (Finset.Icc 1 M) w‖ ^ 2
      ≤ ((Nat.log 2 M + 1 : ℕ) : ℝ) *
          ∑ j ∈ Finset.range (Nat.log 2 M + 1),
            ∑ w ∈ P, ‖logPoly a (dyadicSegmentBlock M j) w‖ ^ 2 := by
  classical
  have hstep : ∑ w ∈ P, ‖logPoly a (Finset.Icc 1 M) w‖ ^ 2
      ≤ ∑ w ∈ P, ((Nat.log 2 M + 1 : ℕ) : ℝ) *
          ∑ j ∈ Finset.range (Nat.log 2 M + 1), ‖logPoly a (dyadicSegmentBlock M j) w‖ ^ 2 :=
    Finset.sum_le_sum fun w _ => normSq_logPoly_Icc_le_card_mul_sum_blocks a M w
  refine hstep.trans (le_of_eq ?_)
  rw [← Finset.mul_sum]
  congr 1
  exact Finset.sum_comm

end

end RHTower.Sieve
