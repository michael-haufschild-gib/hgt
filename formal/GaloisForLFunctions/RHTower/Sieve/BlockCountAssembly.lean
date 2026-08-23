import GaloisForLFunctions.RHTower.Sieve.BlockEnergyBound

/-!
# Summing over the dyadic blocks

There are `⌊log₂ L⌋ + 1` blocks, so a uniform bound on the per-block energy costs only a
logarithmic factor — exactly the `L^C` the card allows.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The block count costs one logarithm.** -/
theorem sum_sqrt_blocks_le {T r : ℝ} {A B L U V : ℕ} {Mb : ℝ}
    (hbound : ∀ j ∈ Finset.range (Nat.log 2 L + 1), blockTypeIIEnergy T r A B L U V j ≤ Mb) :
    (∑ j ∈ Finset.range (Nat.log 2 L + 1), Real.sqrt (blockTypeIIEnergy T r A B L U V j))
      ≤ ((Nat.log 2 L : ℝ) + 1) * Real.sqrt Mb := by
  have hstep : ∀ j ∈ Finset.range (Nat.log 2 L + 1),
      Real.sqrt (blockTypeIIEnergy T r A B L U V j) ≤ Real.sqrt Mb :=
    fun j hj => Real.sqrt_le_sqrt (hbound j hj)
  refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- **The type-II piece from a uniform per-block bound.** -/
theorem norm_typeII_piece_le_of_uniform {T r : ℝ} {A B L U V : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hBL : B - 1 ≤ L) {Mb : ℝ}
    (hbound : ∀ j ∈ Finset.range (Nat.log 2 L + 1), blockTypeIIEnergy T r A B L U V j ≤ Mb) :
    ‖∑ n ∈ Finset.Ico A B,
        (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) * ndPhaseExp T r n‖
      ≤ ((Nat.log 2 L : ℝ) + 1) * Real.sqrt Mb :=
  le_trans (norm_typeII_piece_le_sum_blocks hA hB hBL T r U V) (sum_sqrt_blocks_le hbound)

end

end RHTower.Sieve
