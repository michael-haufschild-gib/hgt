import GaloisForLFunctions.HTGeometry.FiniteReversedAbelBounds
import GaloisForLFunctions.HTGeometry.FiniteHarmonicRows
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheSurvivalConeOfAPeriodicGermIsItsModuleOfRelations

/-!
# Harmonic rows against bounded interval sums

Abel summation controls reciprocal weights on translated and reflected finite
intervals. Splitting at the diagonal bounds an inverse-distance row uniformly.
Mean-zero periodic sequences supply the required interval bound.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- A mean-zero periodic sequence has uniformly bounded sums on all intervals. -/
theorem abs_sum_Ico_le_of_periodic {a : ℕ → ℝ} {q : ℕ}
    (hq : 0 < q) (hper : Function.Periodic a q)
    (hzero : ∑ i ∈ range q, a i = 0) (l r : ℕ) (hlr : l ≤ r) :
    |∑ j ∈ Ico l r, a j| ≤ 2 * ∑ i ∈ range q, |a i| := by
  rw [sum_Ico_eq_sub _ hlr]
  exact (abs_sub _ _).trans (by
    have h := RenormalizedBiarithmeticGeometry.abs_sum_range_le_of_periodic hq hper hzero
    linarith only [h r, h l])

/-- A translated reciprocal interval is bounded by its first weight. -/
theorem abs_sum_Ico_div_add_le {a : ℕ → ℝ} {B r : ℝ}
    (hB : ∀ l k : ℕ, l ≤ k → |∑ j ∈ Ico l k, a j| ≤ B)
    (l k : ℕ) (hr : 0 < r + l) :
    |∑ j ∈ Ico l k, a j / (r + j)| ≤ B / (r + l) := by
  rw [sum_Ico_eq_sum_range]
  have hpartial (t : ℕ) (_ : t ≤ k - l) :
      |∑ j ∈ range t, a (l + j)| ≤ B := by
    have h := hB l (l + t) (Nat.le_add_right _ _)
    rwa [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left] at h
  have h := abs_sum_mul_le_of_finite_partial (g := fun i => a (l + i))
    (w := fun i => 1 / (r + (l + i : ℕ))) (k - l) hpartial
    (fun i => by
      apply one_div_nonneg.mpr
      push_cast
      linarith only [hr, Nat.cast_nonneg (α := ℝ) i])
    (fun i => by
      apply one_div_le_one_div_of_le
      · push_cast; linarith only [hr, Nat.cast_nonneg (α := ℝ) i]
      · push_cast; linarith)
  simpa only [Nat.add_zero, div_eq_mul_inv, one_mul, mul_one, mul_comm] using h

/-- Reflecting the lower half of a distance row preserves its Abel bound. -/
theorem abs_sum_Icc_div_sub_le {a : ℕ → ℝ} {B : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hB : ∀ l k : ℕ, l ≤ k → |∑ j ∈ Ico l k, a j| ≤ B) :
    |∑ j ∈ Icc 1 (n - 1), a j / ((n : ℝ) - j)| ≤ B := by
  have hpartial (k : ℕ) (hk : k ≤ n - 1) :
      |∑ i ∈ range k, a (n - 1 - i)| ≤ B := by
    rw [← Nat.Ico_zero_eq_range,
      sum_Ico_reflect a 0 (show k ≤ n - 1 + 1 by omega),
      Nat.sub_add_cancel hn, Nat.sub_zero]
    exact hB (n - k) n (Nat.sub_le _ _)
  have h := abs_sum_mul_le_of_finite_partial
    (g := fun i => a (n - 1 - i)) (w := fun i => 1 / ((i : ℝ) + 1))
    (n - 1) hpartial (fun i => by positivity)
    (fun i => by apply one_div_le_one_div_of_le (by positivity); push_cast; linarith)
  have heq : (∑ i ∈ range (n - 1), 1 / ((i : ℝ) + 1) * a (n - 1 - i)) =
      ∑ j ∈ Icc 1 (n - 1), a j / ((n : ℝ) - j) := by
    refine sum_bij (fun i _ => n - 1 - i) ?_ ?_ ?_ ?_
    · intro i hi
      have hi' := mem_range.mp hi
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro i hi j hj hij
      have hi' := mem_range.mp hi
      have hj' := mem_range.mp hj
      change n - 1 - i = n - 1 - j at hij
      omega
    · intro j hj
      have hj' := mem_Icc.mp hj
      refine ⟨n - 1 - j, mem_range.mpr (by omega), ?_⟩
      omega
    · intro i hi
      have hi' := mem_range.mp hi
      have hsub : (n : ℝ) - (n - 1 - i : ℕ) = (i : ℝ) + 1 := by
        rw [Nat.cast_sub (show i ≤ n - 1 by omega), Nat.cast_sub hn]
        push_cast
        ring
      rw [hsub]
      ring
  simpa only [heq, Nat.cast_zero, zero_add, div_one, mul_one] using h

/-- Both halves of an inverse-distance row have bounded signed harmonic mass. -/
theorem abs_sum_erase_div_abs_sub_le {a : ℕ → ℝ} {B : ℝ} {n N : ℕ}
    (hn : n ∈ Icc 1 N)
    (hB : ∀ l k : ℕ, l ≤ k → |∑ j ∈ Ico l k, a j| ≤ B) :
    |∑ j ∈ (Icc 1 N).erase n, a j / (|(n : ℝ) - j|)| ≤ 2 * B := by
  have hparts : (Icc 1 N).erase n = Icc 1 (n - 1) ∪ Icc (n + 1) N := by
    ext j
    have hn' := mem_Icc.mp hn
    simp only [mem_erase, mem_Icc, mem_union]
    omega
  have hdisj : Disjoint (Icc 1 (n - 1)) (Icc (n + 1) N) := by
    apply disjoint_left.mpr
    intro j hj hk
    have hj' := mem_Icc.mp hj
    have hk' := mem_Icc.mp hk
    omega
  have hlo : |∑ j ∈ Icc 1 (n - 1), a j / (|(n : ℝ) - j|)| ≤ B := by
    convert abs_sum_Icc_div_sub_le (mem_Icc.mp hn).1 hB using 1
    congr 1
    refine sum_congr rfl fun j hj => ?_
    rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast
      (show j ≤ n by have hj' := mem_Icc.mp hj; omega)))]
  have hhi : |∑ j ∈ Icc (n + 1) N, a j / (|(n : ℝ) - j|)| ≤ B := by
    have h := abs_sum_Ico_div_add_le (r := -(n : ℝ)) hB (n + 1) (N + 1)
      (by push_cast; linarith)
    have heq : (∑ j ∈ Ico (n + 1) (N + 1), a j / (-(n : ℝ) + j)) =
        ∑ j ∈ Icc (n + 1) N, a j / |(n : ℝ) - j| := by
      rw [Ico_add_one_right_eq_Icc]
      refine sum_congr rfl fun j hj => ?_
      rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast
        (show n ≤ j by have hj' := mem_Icc.mp hj; omega)))]
      congr 2
      ring
    rw [heq] at h
    have hd : -(n : ℝ) + (n + 1 : ℕ) = 1 := by push_cast; ring
    simpa only [hd, div_one] using h
  rw [hparts, sum_union hdisj]
  exact (abs_add_le _ _).trans (by linarith only [hlo, hhi])

end GaloisForLFunctions.HTGeometry
