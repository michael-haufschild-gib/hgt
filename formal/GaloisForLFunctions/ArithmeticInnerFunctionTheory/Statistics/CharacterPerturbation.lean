import GaloisForLFunctions.ArithmeticInnerFunctionTheory.Statistics.CharacterMoments
import GaloisForLFunctions.HTGeometry.CentralizerBudgetSplit

/-!
# Stability of normalized torus characters

A character divided by its dimension is a contraction. Product telescoping
makes errors additive, while the trigonometric expansion bounds the phase
sensitivity of each factor by its degree.
-/

open Finset
open GaloisForLFunctions.CompletedArithmeticForms (cosSum)

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

noncomputable section

/-- A character divided by its dimension. -/
def normalizedCosSum (θ : ℝ) (m : ℕ) : ℝ := cosSum θ m / ((m : ℝ) + 1)

theorem abs_normalizedCosSum_le_one (θ : ℝ) (m : ℕ) :
    |normalizedCosSum θ m| ≤ 1 := by
  rw [normalizedCosSum, abs_div, abs_of_pos (by positivity : (0 : ℝ) < m + 1)]
  exact (div_le_one (by positivity)).mpr (abs_cosSum_le θ m)

/-- Phase sensitivity of a normalized degree-`m` character is at most `m`. -/
theorem abs_normalizedCosSum_sub_le (θ φ : ℝ) (m : ℕ) :
    |normalizedCosSum θ m - normalizedCosSum φ m| ≤ (m : ℝ) * |θ - φ| := by
  have hsum : |cosSum θ m - cosSum φ m| ≤
      ((m : ℝ) + 1) * ((m : ℝ) * |θ - φ|) := by
    unfold cosSum
    rw [← sum_sub_distrib]
    calc
      _ ≤ ∑ j ∈ range (m + 1),
          |Real.cos (((2 * j : ℝ) - m) * θ) -
            Real.cos (((2 * j : ℝ) - m) * φ)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ range (m + 1), (m : ℝ) * |θ - φ| := by
        apply sum_le_sum
        intro j hj
        have hjm : (j : ℝ) ≤ m := by exact_mod_cast (Nat.le_of_lt_succ (mem_range.mp hj))
        have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        have hcoeff : |(2 * j : ℝ) - m| ≤ m := abs_le.mpr ⟨by linarith, by linarith⟩
        calc
          _ ≤ |((2 * j : ℝ) - m) * θ - ((2 * j : ℝ) - m) * φ| :=
            Real.abs_cos_sub_cos_le _ _
          _ = |(2 * j : ℝ) - m| * |θ - φ| := by rw [← mul_sub, abs_mul]
          _ ≤ (m : ℝ) * |θ - φ| := mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _)
      _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [normalizedCosSum, normalizedCosSum, ← sub_div, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < m + 1)]
  exact (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hsum)

/-- Tensor character errors add after dimension normalization. -/
theorem abs_prod_normalizedCosSum_sub_prod_le {n : ℕ} (S : Finset (Fin n))
    (θ φ : Fin n → ℝ) (m : Fin n → ℕ) :
    |(∏ i ∈ S, normalizedCosSum (θ i) (m i)) -
      (∏ i ∈ S, normalizedCosSum (φ i) (m i))| ≤
        ∑ i ∈ S, |normalizedCosSum (θ i) (m i) - normalizedCosSum (φ i) (m i)| := by
  have h := HTGeometry.norm_listProd_sub_le
    (S.toList.map fun i => normalizedCosSum (θ i) (m i))
    (S.toList.map fun i => normalizedCosSum (φ i) (m i))
    (by
      intro a ha
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
      simpa only [Real.norm_eq_abs] using abs_normalizedCosSum_le_one (θ i) (m i))
    (by
      intro a ha
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
      simpa only [Real.norm_eq_abs] using abs_normalizedCosSum_le_one (φ i) (m i))
    (by simp only [List.length_map])
  have hzip (l : List (Fin n)) :
      List.zipWith (fun a b : ℝ => ‖a - b‖)
        (l.map fun i => normalizedCosSum (θ i) (m i))
        (l.map fun i => normalizedCosSum (φ i) (m i)) =
      l.map (fun i => ‖normalizedCosSum (θ i) (m i) - normalizedCosSum (φ i) (m i)‖) := by
    induction l with
    | nil => rfl
    | cons i l ih => simp only [List.map_cons, List.zipWith_cons_cons, ih]
  rw [hzip] at h
  simpa only [Finset.prod_map_toList, Finset.sum_map_toList, Real.norm_eq_abs] using h

/-- An explicit dimension-weighted phase perturbation bound for tensor characters. -/
theorem abs_prod_normalizedCosSum_phase_le {n : ℕ} (S : Finset (Fin n))
    (θ φ : Fin n → ℝ) (m : Fin n → ℕ) :
    |(∏ i ∈ S, normalizedCosSum (θ i) (m i)) -
      (∏ i ∈ S, normalizedCosSum (φ i) (m i))| ≤
        ∑ i ∈ S, (m i : ℝ) * |θ i - φ i| :=
  (abs_prod_normalizedCosSum_sub_prod_le S θ φ m).trans
    (sum_le_sum fun i _ => abs_normalizedCosSum_sub_le (θ i) (φ i) (m i))

#print axioms abs_prod_normalizedCosSum_phase_le

/-- The normalized torus characters have degree-weighted phase sensitivity. -/
theorem abs_normalized_chiProd_sub_le {n : ℕ} (θ φ : Fin n → ℝ) (m : Fin n → ℕ) :
    |chiProd θ m / chiSize m - chiProd φ m / chiSize m| ≤
      ∑ i, (m i : ℝ) * |θ i - φ i| := by
  simpa only [normalizedCosSum, prod_div_distrib, chiProd, chiSize] using
    abs_prod_normalizedCosSum_phase_le univ θ φ m

#print axioms abs_normalized_chiProd_sub_le

end
end GaloisForLFunctions.ArithmeticInnerFunctionTheory
