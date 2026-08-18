import GaloisForLFunctions.RHTower.Sieve.FibreRoughShiftBound

/-!
# The discarded set over the fibres, diagonal and off-diagonal

The shifted counts split into the diagonal shift `d = 0`, which is the size of the set itself, and
the nonzero shifts, which the two-dimensional sieve bounds.  This file performs that split, leaving
both pieces as inputs.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The fibre second moment, split into diagonal and off-diagonal shifts.** -/
theorem sum_sq_card_fibre_roughSet_le {x h : ℝ} (hx : 4 ≤ x) (hh0 : 0 ≤ h) (T : Finset ℕ)
    {B0 B1 : ℝ}
    (hzero : ((((T ∩ fibreDyadicIndex x h).card : ℕ)) : ℝ) ≤ B0)
    (hpos : (∑ d ∈ Finset.Ico 1 (⌊h⌋₊ + 1),
        ((((T ∩ fibreDyadicIndex x h).filter
          (fun m => m + d ∈ T ∩ fibreDyadicIndex x h)).card : ℕ) : ℝ)) ≤ B1) :
    ∑ a ∈ outerBlock x h, (((innerFibre x h a ∩ T).card : ℝ)) ^ 2
      ≤ (2 * h + 1) * (2 * (B0 + B1)) := by
  classical
  set A : Finset ℕ := T ∩ fibreDyadicIndex x h with hA
  refine (sum_sq_card_fibre_inter_le_shifts hx hh0 T).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hsplit : Finset.range (⌊h⌋₊ + 1) = insert 0 (Finset.Ico 1 (⌊h⌋₊ + 1)) := by
    ext d
    rw [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  have hnotmem : (0 : ℕ) ∉ Finset.Ico 1 (⌊h⌋₊ + 1) := by
    rw [Finset.mem_Ico]
    omega
  rw [hsplit, Finset.sum_insert hnotmem]
  have hzeroterm : (((A.filter (fun m => m + 0 ∈ A)).card : ℕ) : ℝ) = ((A.card : ℕ) : ℝ) := by
    congr 2
    refine Finset.filter_true_of_mem fun m hm => ?_
    rwa [Nat.add_zero]
  rw [hzeroterm]
  linarith [hzero, hpos]

end

end RHTower.Sieve
