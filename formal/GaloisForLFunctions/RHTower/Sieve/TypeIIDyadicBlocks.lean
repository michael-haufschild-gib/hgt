import GaloisForLFunctions.RHTower.Sieve.TypeIICoefficientEnergy
import GaloisForLFunctions.RHTower.Sieve.DyadicBlockIco

/-!
# The type-II piece, split over dyadic blocks of the long variable

Cauchy--Schwarz on the whole long range is lossy: the coefficient energy is proportional to the
length of that range while the diagonal is proportional to the length of the block.  Splitting the
long variable dyadically first is what makes the type-II estimate nontrivial.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction RHTower

noncomputable section

/-- The type-II energy of one dyadic block of the long variable. -/
def blockTypeIIEnergy (T r : ℝ) (A B L U V j : ℕ) : ℝ :=
  (∑ d ∈ Finset.Ico (2 ^ j) (min (2 ^ (j + 1)) (L + 1)),
      ‖((typeIILong U d : ℝ) : ℂ)‖ ^ (2 : ℕ))
    * ∑ m₁ ∈ Finset.Icc 1 L, ∑ m₂ ∈ Finset.Icc 1 L,
        ‖((typeIIShort V m₁ : ℝ) : ℂ)‖ * ‖((typeIIShort V m₂ : ℝ) : ℂ)‖
          * ‖∑ d ∈ Finset.Ico (2 ^ j) (min (2 ^ (j + 1)) (L + 1)),
              maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖

theorem blockTypeIIEnergy_nonneg (T r : ℝ) (A B L U V j : ℕ) :
    0 ≤ blockTypeIIEnergy T r A B L U V j := by
  rw [blockTypeIIEnergy]
  refine mul_nonneg (Finset.sum_nonneg fun d _ => sq_nonneg _) ?_
  refine Finset.sum_nonneg fun m₁ _ => Finset.sum_nonneg fun m₂ _ => ?_
  positivity

/-- **The type-II piece, over dyadic blocks.** -/
theorem norm_typeII_piece_le_sum_blocks {A B L : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L)
    (T r : ℝ) (U V : ℕ) :
    ‖∑ n ∈ Finset.Ico A B, (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) * ndPhaseExp T r n‖
      ≤ ∑ j ∈ Finset.range (Nat.log 2 L + 1),
          Real.sqrt (blockTypeIIEnergy T r A B L U V j) := by
  rw [sum_typeII_piece_eq hA hB hBL T r U V]
  refine le_trans (norm_sum_Icc_le_sum_dyadic_blocks
    (fun d => ((typeIILong U d : ℝ) : ℂ)
      * ∑ m ∈ Finset.Icc 1 L, ((typeIIShort V m : ℝ) : ℂ) * maskedNdExp T r A B d m)) ?_
  refine Finset.sum_le_sum fun j _ => ?_
  rw [dyadic_block_eq_Ico]
  have hsq := norm_typeII_masked_sq_le T r A B (2 ^ j) (min (2 ^ (j + 1)) (L + 1))
    (Finset.Icc 1 L) (fun d => ((typeIILong U d : ℝ) : ℂ))
    (fun m => ((typeIIShort V m : ℝ) : ℂ))
  have hnn : (0 : ℝ) ≤ ‖∑ d ∈ Finset.Ico (2 ^ j) (min (2 ^ (j + 1)) (L + 1)),
      ((typeIILong U d : ℝ) : ℂ)
        * ∑ m ∈ Finset.Icc 1 L, ((typeIIShort V m : ℝ) : ℂ) * maskedNdExp T r A B d m‖ :=
    norm_nonneg _
  have hmono := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq hnn] at hmono
  exact hmono

end

end RHTower.Sieve
