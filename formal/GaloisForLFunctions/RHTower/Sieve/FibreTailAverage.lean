import GaloisForLFunctions.RHTower.Sieve.FibreSquarefreeIngredients
import GaloisForLFunctions.RHTower.Sieve.FibreStartSeparation
import GaloisForLFunctions.RHTower.Sieve.AveragedSquarefreeTail

/-!
# The fibre truncation tail, averaged over the outer block
-/

namespace RHTower.Sieve

open Finset

/-- **The fibre tails aggregate over the start range.**  Every fibre is shorter than `⌈h⌉+1` and at
most four fibres share a start, so the per-fibre tails are dominated by four copies of the tail at
the uniform length. -/
theorem sum_fibre_windowTail_le {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) (R M : ℕ) :
    ∑ a ∈ outerBlock x h, windowTail (fibreStartIdx x a) (fibreLen x h a) R M
      ≤ 4 * ∑ y ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊,
          windowTail (y - 1) (⌈h⌉₊ + 1) R M := by
  classical
  have hstep : ∑ a ∈ outerBlock x h, windowTail (fibreStartIdx x a) (fibreLen x h a) R M
      ≤ ∑ a ∈ outerBlock x h, windowTail (⌈x / (a : ℝ)⌉₊ - 1) (⌈h⌉₊ + 1) R M := by
    refine Finset.sum_le_sum fun a ha => ?_
    have hle := fibreLen_le hx hh ha
    have := windowTail_mono (t := fibreStartIdx x a) (R := R) (M := M) hle
    simpa [fibreStartIdx] using this
  refine hstep.trans ?_
  exact sum_block_comp_start_le hx (G := fun y => windowTail (y - 1) (⌈h⌉₊ + 1) R M)
    (fun y => windowTail_nonneg _ _ _ _)

/-- **The shifted start range, bounded by the averaged tail.** -/
theorem sum_shift_windowTail_le {A B : ℕ} (L R M : ℕ) (hA : 1 ≤ A) (hR : 1 ≤ R)
    (hAB : A - 1 ≤ B + L) :
    ∑ y ∈ Finset.Icc A B, windowTail (y - 1) L R M
      ≤ (L : ℝ) * (((B : ℝ) + L - ((A - 1 : ℕ) : ℝ)) / (R : ℝ) + (M : ℝ)) := by
  classical
  have hinj : ∀ y ∈ Finset.Icc A B, ∀ y' ∈ Finset.Icc A B, y - 1 = y' - 1 → y = y' := by
    intro y hy y' hy' he
    rw [Finset.mem_Icc] at hy hy'
    omega
  have himg : (Finset.Icc A B).image (fun y => y - 1) ⊆ Finset.Ico (A - 1) B := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨y, hy, rfl⟩ := ht
    rw [Finset.mem_Icc] at hy
    rw [Finset.mem_Ico]
    omega
  have hreindex : ∑ t ∈ (Finset.Icc A B).image (fun y => y - 1), windowTail t L R M
      = ∑ y ∈ Finset.Icc A B, windowTail (y - 1) L R M := Finset.sum_image hinj
  have hgrow : ∑ t ∈ (Finset.Icc A B).image (fun y => y - 1), windowTail t L R M
      ≤ ∑ t ∈ Finset.Ico (A - 1) B, windowTail t L R M :=
    Finset.sum_le_sum_of_subset_of_nonneg himg
      (fun t _ _ => windowTail_nonneg _ _ _ _)
  have hbase := sum_tail_divisor_count_le (A - 1) B L R M hR hAB
  rw [← hreindex]
  refine hgrow.trans ?_
  simpa [windowTail] using hbase

end RHTower.Sieve
