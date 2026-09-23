import GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock
import GaloisForLFunctions.HTGeometry.SupercriticalSharpnessMechanisms

/-!
# Supercritical sharpness mechanisms in finite simplex blocks

The finite-family density step from supercritical sharpness selects an average-heavy coordinate
in the Markushevich simplex block.  Combining that selection with the block's energy inequalities
turns global average, deviation, and reconstruction energy into one-coordinate certificates.
-/

open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock

open Classical

variable (ι : Type*) [Fintype ι] [Nonempty ι]

/-- Some coefficient carries at least the average coefficient energy. -/
theorem exists_coefficient_totalEnergy_le_card_mul (d : ι → ℂ) :
    ∃ i, (∑ j : ι, ‖d j‖ ^ (2 : ℕ)) ≤ (Fintype.card ι : ℝ) * ‖d i‖ ^ (2 : ℕ) := by
  rcases GaloisForLFunctions.HTGeometry.finiteFamilySum_empty_or_le_card_mul
      (fun j : ι ↦ ‖d j‖ ^ (2 : ℕ)) with hzero | hi
  · have hcard := card_pos ι
    omega
  · exact hi

/-- Some coefficient is at least as large as the block average in squared norm. -/
theorem exists_norm_average_sq_le_norm_sq (d : ι → ℂ) :
    ∃ i, ‖average ι d‖ ^ (2 : ℕ) ≤ ‖d i‖ ^ (2 : ℕ) := by
  obtain ⟨i, hi⟩ := exists_coefficient_totalEnergy_le_card_mul ι d
  have havg := card_mul_norm_average_sq_le_sum ι d
  have hcard : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast card_pos ι
  refine ⟨i, ?_⟩
  nlinarith [havg.trans hi]

/-- Some coordinate deviation carries at least the average deviation energy. -/
theorem exists_deviationEnergy_le_card_mul_coordinate (d : ι → ℂ) :
    ∃ i, ‖deviation ι d‖ ^ (2 : ℕ) ≤
      (Fintype.card ι : ℝ) * ‖d i - average ι d‖ ^ (2 : ℕ) := by
  rcases GaloisForLFunctions.HTGeometry.finiteFamilySum_empty_or_le_card_mul
      (fun i : ι ↦ ‖d i - average ι d‖ ^ (2 : ℕ)) with hzero | ⟨i, hi⟩
  · have hcard := card_pos ι
    omega
  · refine ⟨i, ?_⟩
    rw [norm_deviation_sq]
    exact hi

/-- One coefficient controls the whole simplex-block reconstruction energy, up to the explicit
dimension factor. -/
theorem exists_norm_solution_sq_le_twenty_card_mul_coordinate (d : ι → ℂ) :
    ∃ i, ‖solution ι d‖ ^ (2 : ℕ) ≤
      (20 * Fintype.card ι : ℝ) * ‖d i‖ ^ (2 : ℕ) := by
  obtain ⟨i, hi⟩ := exists_coefficient_totalEnergy_le_card_mul ι d
  refine ⟨i, ?_⟩
  calc
    ‖solution ι d‖ ^ (2 : ℕ) ≤ 20 * ∑ j : ι, ‖d j‖ ^ (2 : ℕ) := norm_solution_sq_le ι d
    _ ≤ 20 * ((Fintype.card ι : ℝ) * ‖d i‖ ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hi (by norm_num)
    _ = (20 * Fintype.card ι : ℝ) * ‖d i‖ ^ (2 : ℕ) := by ring

end GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock
