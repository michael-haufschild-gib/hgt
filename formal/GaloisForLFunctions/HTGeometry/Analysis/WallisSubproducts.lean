import GaloisForLFunctions.HTGeometry.Analysis.ReciprocalPowerProducts
import Mathlib.Analysis.Real.Pi.Wallis

/-!
# Reciprocal-square subproducts on the even integers

The factor-deletion argument for reciprocal-power products becomes sharper on
even denominators: Wallis' product bounds every finite subproduct by `π/2`.
-/

namespace GaloisForLFunctions.HTGeometry.ReciprocalPowerProducts

open Finset

theorem even_factor_pos (n : ℕ) :
    0 < 1 - 1 / (2 * (n : ℝ) + 2) ^ 2 := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using factor_pos 0 (2 * n)

private theorem even_factor_eq_wallis (n : ℕ) :
    (1 - 1 / (2 * (n : ℝ) + 2) ^ 2)⁻¹ =
      (2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 1) *
        ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 3)) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : (2 * (n : ℝ) + 2) ^ 2 - 1 ≠ 0 := by
    nlinarith only [hn, sq_nonneg (n : ℝ)]
  have hf : 1 - 1 / (2 * (n : ℝ) + 2) ^ 2 =
      ((2 * (n : ℝ) + 2) ^ 2 - 1) / (2 * (n : ℝ) + 2) ^ 2 := by
    field_simp
  rw [hf, inv_div, div_mul_div_comm]
  apply (div_eq_div_iff hd (by positivity)).mpr
  ring

/-- Every finite reciprocal-square product over even denominators is at most `π/2`. -/
theorem wallis_subproduct_le (S : Finset ℕ) :
    (∏ n ∈ S, (1 - 1 / (2 * (n : ℝ) + 2) ^ 2)⁻¹) ≤ Real.pi / 2 := by
  have hsub : S ⊆ range (S.sup id + 1) := by
    intro n hn
    exact mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))
  calc
    _ ≤ ∏ n ∈ range (S.sup id + 1), (1 - 1 / (2 * (n : ℝ) + 2) ^ 2)⁻¹ := by
      apply prod_le_prod_of_subset_of_one_le hsub
      · intro n _
        exact (inv_pos.mpr (even_factor_pos n)).le
      · intro n _ _
        exact (one_le_inv₀ (even_factor_pos n)).mpr
          (sub_le_self _ (by positivity))
    _ = Real.Wallis.W (S.sup id + 1) := by
      simp only [even_factor_eq_wallis, Real.Wallis.W]
    _ ≤ Real.pi / 2 := Real.Wallis.W_le _

#print axioms wallis_subproduct_le

end GaloisForLFunctions.HTGeometry.ReciprocalPowerProducts
