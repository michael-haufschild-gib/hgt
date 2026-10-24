import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.BinomialMultipliers
import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.DivisorTransitions

/-!
# Exact multiplicity costs in geometric coordinates

The squared spectral distance `u² + δ²` rescales an off-center pair to the normalized
binomial repair family. The zero-distance case is a central monomial and needs no division.
-/

open Polynomial
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry

noncomputable section

/-- Adjoin `n` real divisor factors at squared distance `u² + δ²`. -/
def geometricRepair (u δ : ℝ) (n : ℕ) : ℝ[X] :=
  pairFactor u δ * (X + C (u ^ 2 + δ ^ 2)) ^ n

/-- The pair rescales homogeneously once its signed ratio is fixed. -/
theorem pairFactor_rescale (u δ α : ℝ) (hα : (u ^ 2 + δ ^ 2) * α = δ ^ 2 - u ^ 2) :
    (pairFactor u δ).comp (C (u ^ 2 + δ ^ 2) * X) =
      C ((u ^ 2 + δ ^ 2) ^ 2) * (X ^ 2 - C (2 * α) * X + 1) := by
  have hC := congrArg (C : ℝ → ℝ[X]) hα
  simp only [map_mul, map_add, map_sub, map_pow] at hC
  simp only [pairFactor, add_comp, mul_comp, pow_comp, X_comp, C_comp]
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat]
  linear_combination 2 * (C u ^ 2 + C δ ^ 2) * X * hC

/-- Rescaling the whole block retains the exact multiplier degree. -/
theorem geometricRepair_rescale (u δ α : ℝ) (n : ℕ)
    (hα : (u ^ 2 + δ ^ 2) * α = δ ^ 2 - u ^ 2) :
    (geometricRepair u δ n).comp (C (u ^ 2 + δ ^ 2) * X) =
      C ((u ^ 2 + δ ^ 2) ^ (n + 2)) * binomialRepair α n := by
  have hlin : (X + C (u ^ 2 + δ ^ 2)).comp (C (u ^ 2 + δ ^ 2) * X) =
      C (u ^ 2 + δ ^ 2) * (X + 1) := by
    simp only [add_comp, X_comp, C_comp]
    ring
  have hpow : (C ((u ^ 2 + δ ^ 2) ^ (n + 2)) : ℝ[X]) =
      C (u ^ 2 + δ ^ 2) ^ n * C (u ^ 2 + δ ^ 2) ^ 2 := by
    rw [map_pow, pow_add]
  rw [geometricRepair, mul_comp, pow_comp, pairFactor_rescale u δ α hα, hlin, mul_pow]
  rw [hpow, map_pow]
  simp only [binomialRepair]
  ring

theorem coeffNonneg_geometricRepair_iff (u δ : ℝ) (n : ℕ) (hr : 0 < u ^ 2 + δ ^ 2) :
    CoeffNonneg (geometricRepair u δ n) ↔
      CoeffNonneg (binomialRepair ((δ ^ 2 - u ^ 2) / (u ^ 2 + δ ^ 2)) n) := by
  have hα : (u ^ 2 + δ ^ 2) * ((δ ^ 2 - u ^ 2) / (u ^ 2 + δ ^ 2)) =
      δ ^ 2 - u ^ 2 := by field_simp
  rw [← coeffNonneg_positive_rescale_iff (geometricRepair u δ n) hr,
    geometricRepair_rescale u δ _ n hα,
    coeffNonneg_C_mul_iff _ (pow_pos hr _)]

theorem coeffNonneg_geometricRepair_zero (n : ℕ) :
    CoeffNonneg (geometricRepair 0 0 n) := by
  have h : CoeffNonneg ((X : ℝ[X]) ^ (n + 2)) := by
    intro k
    simp only [coeff_X_pow]
    split_ifs <;> norm_num
  simpa [geometricRepair, pairFactor, pow_add, mul_comm] using h

/-- Exact geometric cost for even multiplier multiplicity, including a central zero pair. -/
theorem coeffNonneg_geometricRepair_even_iff (u δ : ℝ) (m : ℕ) :
    CoeffNonneg (geometricRepair u δ (2 * m)) ↔ δ ^ 2 ≤ (2 * m + 1 : ℝ) * u ^ 2 := by
  by_cases hr : 0 < u ^ 2 + δ ^ 2
  · rw [coeffNonneg_geometricRepair_iff u δ _ hr, coeffNonneg_binomialRepair_even_iff]
    have hcross : (δ ^ 2 - u ^ 2) / (u ^ 2 + δ ^ 2) * (m + 1 : ℝ) *
        (u ^ 2 + δ ^ 2) = (δ ^ 2 - u ^ 2) * (m + 1 : ℝ) := by field_simp
    constructor
    · intro h
      have hm := mul_le_mul_of_nonneg_right h hr.le
      rw [hcross] at hm
      nlinarith only [hm]
    · intro h
      apply (mul_le_mul_iff_of_pos_right hr).mp
      rw [hcross]
      nlinarith only [h]
  · have hu : u = 0 := by nlinarith only [le_of_not_gt hr, sq_nonneg δ]
    have hδ : δ = 0 := by nlinarith only [le_of_not_gt hr, sq_nonneg u]
    subst u
    subst δ
    simpa using (iff_true_intro (coeffNonneg_geometricRepair_zero (2 * m)))

/-- Odd multiplier multiplicity reaches the same region as the next even multiplicity. -/
theorem coeffNonneg_geometricRepair_odd_iff (u δ : ℝ) (m : ℕ) :
    CoeffNonneg (geometricRepair u δ (2 * m + 1)) ↔ δ ^ 2 ≤ (2 * m + 3 : ℝ) * u ^ 2 := by
  by_cases hr : 0 < u ^ 2 + δ ^ 2
  · rw [coeffNonneg_geometricRepair_iff u δ _ hr, coeffNonneg_binomialRepair_odd_iff]
    have hcross : (δ ^ 2 - u ^ 2) / (u ^ 2 + δ ^ 2) * (m + 2 : ℝ) *
        (u ^ 2 + δ ^ 2) = (δ ^ 2 - u ^ 2) * (m + 2 : ℝ) := by field_simp
    constructor
    · intro h
      have hm := mul_le_mul_of_nonneg_right h hr.le
      rw [hcross] at hm
      nlinarith only [hm]
    · intro h
      apply (mul_le_mul_iff_of_pos_right hr).mp
      rw [hcross]
      nlinarith only [h]
  · have hu : u = 0 := by nlinarith only [le_of_not_gt hr, sq_nonneg δ]
    have hδ : δ = 0 := by nlinarith only [le_of_not_gt hr, sq_nonneg u]
    subst u
    subst δ
    simpa using (iff_true_intro (coeffNonneg_geometricRepair_zero (2 * m + 1)))

end

end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
