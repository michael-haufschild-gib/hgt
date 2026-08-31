import GaloisForLFunctions.HTGeometry.CompactAddGroupMetricReturnLaw
import GaloisForLFunctions.HTGeometry.FormationStokesFolnerSelection

/-!
# Compact observer-closed Følner boxes and fixed-rank escape

Compact recurrence simultaneously closes every fixed finite phase palette at cofinally large common
widths. The formation Stokes rank-width law then annihilates any real bulk character carried by
fixed-rank boxes with uniformly bounded local current. Quantitatively, a nonzero character forces
local edge capacity to grow at least linearly along cofinally large observer-closed widths.
-/

open Set
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [AddCommGroup K]
variable [PseudoEMetricSpace K] [IsIsometricVAdd Kᵃᵒᵖ K] [CompactSpace K]

/-- **Simultaneous cofinal compact return.** Beyond every threshold, one common natural multiple
returns every coordinate of a fixed finite phase palette to the same identity ball. -/
theorem exists_large_simultaneous_nsmul_return_le_two_mul
    {d : ℕ} (α : Fin d → K) (r : ℝ≥0) (hr : r ≠ 0) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ ∀ j : Fin d, edist (n • α j) 0 ≤ 2 * r := by
  obtain ⟨n, hnN, hnreturn⟩ :=
    exists_large_nsmul_return_le_two_mul α r hr N
  refine ⟨n, hnN, ?_⟩
  intro j
  have hj := (edist_le_pi_edist (n • α) 0 j).trans hnreturn
  simpa using hj

/-- A width-`w`, rank-`d` bulk-current bound gives the exact inverse-rank lower bound on local
edge-current capacity. -/
theorem boxCurrent_capacity_lowerBound
    (chi M w : ℝ) (d : ℕ) (hd : 0 < d)
    (hbound : w * |chi| ≤ 2 * M * (d : ℝ)) :
    w * |chi| / (2 * (d : ℝ)) ≤ M := by
  rw [div_le_iff₀ (mul_pos (by norm_num) (by exact_mod_cast hd))]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hbound

/-- **Cofinal capacity escape.** If observer-closed fixed-rank boxes carry bulk character `chi`,
then beyond every width threshold one closed box has capacity at least `n * |chi| / (2*d)`. -/
theorem exists_large_closedBox_with_capacity_lowerBound
    {d : ℕ} (α : Fin d → K) (r : ℝ≥0) (hr : r ≠ 0)
    (chi : ℝ) (capacity : ℕ → ℝ) (hd : 0 < d)
    (hbox : ∀ n : ℕ, 0 < n →
      (∀ j : Fin d, edist (n • α j) 0 ≤ 2 * r) →
      (n : ℝ) ^ d * |chi| ≤
        2 * capacity n * (d : ℝ) * (n : ℝ) ^ (d - 1))
    (N : ℕ) :
    ∃ n : ℕ, N < n ∧
      (∀ j : Fin d, edist (n • α j) 0 ≤ 2 * r) ∧
      (n : ℝ) * |chi| / (2 * (d : ℝ)) ≤ capacity n := by
  obtain ⟨n, hnN, hnreturn⟩ :=
    exists_large_simultaneous_nsmul_return_le_two_mul α r hr N
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le N) hnN
  have hcurrent := hbox n hnpos hnreturn
  have hbound : (n : ℝ) * |chi| ≤ 2 * capacity n * (d : ℝ) :=
    boxRankWidth_current_le chi (capacity n) n d (by exact_mod_cast hnpos) hd hcurrent
  exact ⟨n, hnN, hnreturn,
    boxCurrent_capacity_lowerBound chi (capacity n) n d hd hbound⟩

/-- **Fixed-rank compact-phase selection.** Simultaneous compact return plus local Stokes box
formation with one fixed edge-current capacity forces the real bulk character to vanish. -/
theorem bulkCurrent_eq_zero_of_fixedRank_compactPhase_closedBoxes
    {d : ℕ} (α : Fin d → K) (r : ℝ≥0) (hr : r ≠ 0)
    (chi M : ℝ) (hd : 0 < d)
    (hbox : ∀ n : ℕ, 0 < n →
      (∀ j : Fin d, edist (n • α j) 0 ≤ 2 * r) →
      (n : ℝ) ^ d * |chi| ≤ 2 * M * (d : ℝ) * (n : ℝ) ^ (d - 1)) :
    chi = 0 := by
  by_contra hchi
  have habs : 0 < |chi| := abs_pos.mpr hchi
  obtain ⟨N, hN⟩ := exists_nat_gt ((2 * M * (d : ℝ)) / |chi|)
  obtain ⟨n, hnN, hnreturn⟩ :=
    exists_large_simultaneous_nsmul_return_le_two_mul α r hr N
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le N) hnN
  have hcurrent := hbox n hnpos hnreturn
  have hbound : (n : ℝ) * |chi| ≤ 2 * M * (d : ℝ) :=
    boxRankWidth_current_le chi M n d (by exact_mod_cast hnpos) hd hcurrent
  have hstrict : 2 * M * (d : ℝ) < (n : ℝ) * |chi| := by
    calc
      2 * M * (d : ℝ) < (N : ℝ) * |chi| := (div_lt_iff₀ habs).mp hN
      _ ≤ (n : ℝ) * |chi| :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.le_of_lt hnN)) (abs_nonneg _)
  exact (not_lt_of_ge hbound) hstrict

end GaloisForLFunctions.HTGeometry
