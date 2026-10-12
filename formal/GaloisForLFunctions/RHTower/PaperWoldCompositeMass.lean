import GaloisForLFunctions.RHTower.PaperWoldHilbertSchmidtStability

/-! # Persistent unsquared mass on the actual composite coordinates

The obstruction to compactness is stronger than divergent squared energy:
normalized finite composite squares retain a fixed positive signed mass.
-/

namespace RHTower
noncomputable section
open scoped BigOperators

def paperWoldCompositeEntry (t : ℝ) (n j : ℕ) : ℂ :=
  paperWoldDirectedKernel t (2 * n + 2, 2 * j + 2)

theorem paperWoldCompositeEntry_im (t : ℝ) (n j : ℕ) :
    (paperWoldCompositeEntry t n j).im = 0 := by
  unfold paperWoldCompositeEntry paperWoldDirectedKernel
  split_ifs <;> rfl

theorem paperWoldCompositeEntry_re_nonneg (t : ℝ) (n j : ℕ) :
    0 ≤ (paperWoldCompositeEntry t n j).re := by
  unfold paperWoldCompositeEntry paperWoldDirectedKernel
  split_ifs
  · simp only [Complex.ofReal_re]
    exact mul_nonneg_of_nonpos_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by positivity) _)
        (paperWold_even_composite_increment_neg n).le)
      (paperWold_even_composite_increment_neg j).le
  · exact le_rfl

theorem paperWoldCompositeEntry_norm_eq_re (t : ℝ) (n j : ℕ) :
    ‖paperWoldCompositeEntry t n j‖ = (paperWoldCompositeEntry t n j).re := by
  have he : ((paperWoldCompositeEntry t n j).re : ℂ) = paperWoldCompositeEntry t n j := by
    apply Complex.ext
    · rfl
    · exact (paperWoldCompositeEntry_im t n j).symm
  calc
    _ = ‖((paperWoldCompositeEntry t n j).re : ℂ)‖ := congrArg norm he.symm
    _ = _ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (paperWoldCompositeEntry_re_nonneg t n j)]

/-- Each successive composite column retains at least a fixed signed mass. -/
theorem paperWoldCompositeEntry_column_mass (t : {t : ℝ // 1 / 2 ≤ t}) (m : ℕ) :
    (1 / 12 : ℝ) ≤ ∑ k ∈ Finset.range (m + 1), (paperWoldCompositeEntry t k (m + 1)).re := by
  have hsum : ((m : ℝ) + 1) * (1 / (4 * (m : ℝ) + 12)) ≤
      ∑ k ∈ Finset.range (m + 1), (paperWoldCompositeEntry t k (m + 1)).re := by
    calc
      _ = ∑ _k ∈ Finset.range (m + 1), 1 / (4 * (m : ℝ) + 12) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        rw [← paperWoldCompositeEntry_norm_eq_re]
        simpa only [paperWoldCompositeEntry, show 2 * (m + 1) + 2 = 2 * m + 4 by omega] using
          paperWoldDirectedKernel_composite_lower t m ⟨k, Finset.mem_range.mp hk⟩
  apply le_trans _ hsum
  rw [mul_one_div]
  apply (le_div_iff₀ (by positivity : 0 < 4 * (m : ℝ) + 12)).mpr
  linarith [Nat.cast_nonneg (α := ℝ) m]

/-- The full signed composite square contains linearly growing positive mass. -/
theorem paperWoldCompositeEntry_square_mass (t : {t : ℝ // 1 / 2 ≤ t}) (N : ℕ) :
    (N : ℝ) / 12 ≤ ∑ n ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
      (paperWoldCompositeEntry t n j).re := by
  have ht : (N : ℝ) / 12 ≤ ∑ m ∈ Finset.range N,
      ∑ k ∈ Finset.range (m + 1), (paperWoldCompositeEntry t k (m + 1)).re := by
    calc
      _ = ∑ _m ∈ Finset.range N, (1 / 12 : ℝ) := by simp [div_eq_mul_inv]
      _ ≤ _ := Finset.sum_le_sum fun m _ => paperWoldCompositeEntry_column_mass t m
  have he : (∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range j,
      (paperWoldCompositeEntry t k j).re) = ∑ m ∈ Finset.range N,
      ∑ k ∈ Finset.range (m + 1), (paperWoldCompositeEntry t k (m + 1)).re := by
    rw [Finset.sum_range_succ']
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
  rw [← he] at ht
  rw [Finset.sum_comm]
  apply ht.trans
  apply Finset.sum_le_sum
  intro j hj
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Finset.mem_range.mp hj).le)
  intro k hk hkj
  exact paperWoldCompositeEntry_re_nonneg t k j

/-- Normalization by the number of coordinates cannot erase the composite mass. -/
theorem paperWoldCompositeEntry_normalized_mass
    (t : {t : ℝ // 1 / 2 ≤ t}) (N : ℕ) :
    (1 / 24 : ℝ) ≤ ((N : ℝ) + 2)⁻¹ *
      ∑ n ∈ Finset.range (N + 2), ∑ j ∈ Finset.range (N + 2),
        (paperWoldCompositeEntry t n j).re := by
  have h := paperWoldCompositeEntry_square_mass t (N + 1)
  have hd : 0 < (N : ℝ) + 2 := by positivity
  have hb : (1 / 24 : ℝ) ≤ ((N : ℝ) + 2)⁻¹ * (((N : ℝ) + 1) / 12) := by
    rw [mul_comm, ← div_eq_mul_inv]
    apply (le_div_iff₀ hd).mpr
    linarith [Nat.cast_nonneg (α := ℝ) N]
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hd.le)
  simpa only [Nat.cast_add, Nat.cast_one, Nat.add_assoc] using h

end
end RHTower
