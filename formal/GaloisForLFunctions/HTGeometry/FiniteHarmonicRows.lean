import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Exact harmonic rows on a finite integer interval

Difference denominators split at the row index; sum denominators telescope
between two harmonic numbers. The omitted diagonal is retained explicitly.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.HTGeometry

private theorem sum_Icc_one_div_eq_harmonic (N : ℕ) :
    (∑ j ∈ Icc 1 N, 1 / (j : ℝ)) = harmonic N := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

/-- Summing a translated reciprocal row gives a harmonic increment. -/
theorem sum_Icc_one_div_add (n N : ℕ) :
    (∑ j ∈ Icc 1 N, 1 / ((n : ℝ) + j)) =
      (harmonic (n + N) : ℝ) - harmonic n := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    rw [show n + N.succ = (n + N) + 1 by omega, harmonic_succ]
    push_cast
    ring

/-- The lower half of an inverse-distance row is a reversed harmonic sum. -/
theorem sum_Icc_one_div_abs_sub_lower {n : ℕ} (hn : 1 ≤ n) :
    (∑ j ∈ Icc 1 (n - 1), 1 / |(n : ℝ) - j|) = harmonic (n - 1) := by
  rw [← sum_Icc_one_div_eq_harmonic]
  refine sum_bij (fun j _ => n - j) ?_ ?_ ?_ ?_
  · intro j hj
    rcases mem_Icc.mp hj with ⟨hj1, hjn⟩
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i hi j hj hij
    have hi' := mem_Icc.mp hi
    have hj' := mem_Icc.mp hj
    omega
  · intro k hk
    have hk' := mem_Icc.mp hk
    refine ⟨n - k, mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    omega
  · intro j hj
    have hjn : j ≤ n := by have h := mem_Icc.mp hj; omega
    rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hjn)), Nat.cast_sub hjn]

/-- The upper half of an inverse-distance row is a translated harmonic sum. -/
theorem sum_Icc_one_div_abs_sub_upper {n N : ℕ} (hnN : n ≤ N) :
    (∑ j ∈ Icc (n + 1) N, 1 / |(n : ℝ) - j|) = harmonic (N - n) := by
  rw [← sum_Icc_one_div_eq_harmonic]
  refine sum_bij (fun j _ => j - n) ?_ ?_ ?_ ?_
  · intro j hj
    have hj' := mem_Icc.mp hj
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i hi j hj hij
    have hi' := mem_Icc.mp hi
    have hj' := mem_Icc.mp hj
    omega
  · intro k hk
    have hk' := mem_Icc.mp hk
    refine ⟨n + k, mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    omega
  · intro j hj
    have hnj : n ≤ j := by have h := mem_Icc.mp hj; omega
    rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hnj)), neg_sub,
      Nat.cast_sub hnj]

/-- Both sides of a finite inverse-distance row are kept exactly. -/
theorem sum_erase_one_div_abs_sub {n N : ℕ} (hn : n ∈ Icc 1 N) :
    (∑ j ∈ (Icc 1 N).erase n, 1 / |(n : ℝ) - j|) =
      (harmonic (n - 1) : ℝ) + harmonic (N - n) := by
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
  rw [hparts, sum_union hdisj,
    sum_Icc_one_div_abs_sub_lower (mem_Icc.mp hn).1,
    sum_Icc_one_div_abs_sub_upper (mem_Icc.mp hn).2]

/-- Deleting the diagonal from an inverse-sum row costs precisely `1/(2n)`. -/
theorem sum_erase_one_div_add {n N : ℕ} (hn : n ∈ Icc 1 N) :
    (∑ j ∈ (Icc 1 N).erase n, 1 / ((n : ℝ) + j)) =
      (harmonic (n + N) : ℝ) - harmonic n - 1 / (2 * (n : ℝ)) := by
  have h := sum_erase_add (Icc 1 N) (fun j => 1 / ((n : ℝ) + j)) hn
  rw [sum_Icc_one_div_add] at h
  have htwo : (n : ℝ) + n = 2 * n := by ring
  rw [htwo] at h
  linarith only [h]

/-- The symmetric half-sum kernel has a closed harmonic boundary row. -/
theorem sum_erase_harmonic_kernel {n N : ℕ} (hn : n ∈ Icc 1 N) :
    (∑ j ∈ (Icc 1 N).erase n,
      (1 / 2 : ℝ) * (1 / |(n : ℝ) - j| + 1 / ((n : ℝ) + j))) =
      ((harmonic (N - n) : ℝ) + harmonic (N + n)) / 2 - 3 / (4 * (n : ℝ)) := by
  rw [← mul_sum, sum_add_distrib, sum_erase_one_div_abs_sub hn,
    sum_erase_one_div_add hn]
  have hn1 := (mem_Icc.mp hn).1
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hH : (harmonic n : ℝ) = harmonic (n - 1) + (n : ℝ)⁻¹ := by
    have heq : n = (n - 1) + 1 := by omega
    conv_lhs => rw [heq, harmonic_succ]
    push_cast
    have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      exact_mod_cast (show n - 1 + 1 = n by omega)
    rw [hcast]
  rw [hH, Nat.add_comm n N]
  field_simp [hn0]
  ring

end GaloisForLFunctions.HTGeometry

