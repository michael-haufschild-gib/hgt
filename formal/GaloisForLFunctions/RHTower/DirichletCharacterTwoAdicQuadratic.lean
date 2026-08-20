/-
# Closed two-adic quadratic-character local factors

Mathlib supplies the three integral quadratic characters at the two-adic
levels `4` and `8`.  This module lifts them to complex-valued Dirichlet
characters and closes their finite complete-correlation estimates.
The result is a local factor for the even fundamental-discriminant cases; it
does not yet identify products with the source paper's discriminant family.
-/
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.Analysis.Complex.Norm

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Complex-valued quadratic character at level `4`. -/
def quadraticCharacterFour : MulChar (ZMod 4) ℂ :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

/-- First complex-valued quadratic character at level `8`. -/
def quadraticCharacterEight : MulChar (ZMod 8) ℂ :=
  ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)

/-- Second complex-valued quadratic character at level `8`. -/
def quadraticCharacterEightPrime : MulChar (ZMod 8) ℂ :=
  ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ)

/-- The conductor-four character remains quadratic after the integral-to-complex lift. -/
theorem quadraticCharacterFour_isQuadratic : quadraticCharacterFour.IsQuadratic :=
  ZMod.isQuadratic_χ₄.comp _

/-- The first conductor-eight character remains quadratic after the integral-to-complex lift. -/
theorem quadraticCharacterEight_isQuadratic : quadraticCharacterEight.IsQuadratic :=
  ZMod.isQuadratic_χ₈.comp _

/-- The second conductor-eight character remains quadratic after the integral-to-complex lift. -/
theorem quadraticCharacterEightPrime_isQuadratic : quadraticCharacterEightPrime.IsQuadratic :=
  ZMod.isQuadratic_χ₈'.comp _

private theorem complex_norm_one : ‖(1 : ℂ)‖ = 1 := by
  calc
    ‖(1 : ℂ)‖ = ‖((1 : ℝ) : ℂ)‖ := by norm_num
    _ = ‖(1 : ℝ)‖ := Complex.norm_real 1
    _ = 1 := abs_of_nonneg zero_le_one

private theorem complex_norm_neg_one : ‖(-1 : ℂ)‖ = 1 := by
  calc
    ‖(-1 : ℂ)‖ = ‖((-1 : ℝ) : ℂ)‖ := by norm_num
    _ = ‖(-1 : ℝ)‖ := Complex.norm_real (-1)
    _ = 1 := by
      rw [Real.norm_eq_abs]
      norm_num

/-- Every conductor-four quadratic-character value has norm at most one. -/
theorem quadraticCharacterFour_norm_le_one (x : ZMod 4) :
    ‖quadraticCharacterFour x‖ ≤ 1 := by
  fin_cases x <;>
    norm_num [quadraticCharacterFour, ZMod.χ₄, complex_norm_one, complex_norm_neg_one]

/-- Every first conductor-eight quadratic-character value has norm at most one. -/
theorem quadraticCharacterEight_norm_le_one (x : ZMod 8) :
    ‖quadraticCharacterEight x‖ ≤ 1 := by
  fin_cases x <;>
    norm_num [quadraticCharacterEight, ZMod.χ₈, complex_norm_one, complex_norm_neg_one]

/-- Every second conductor-eight quadratic-character value has norm at most one. -/
theorem quadraticCharacterEightPrime_norm_le_one (x : ZMod 8) :
    ‖quadraticCharacterEightPrime x‖ ≤ 1 := by
  fin_cases x <;>
    norm_num [quadraticCharacterEightPrime, ZMod.χ₈', complex_norm_one, complex_norm_neg_one]

/-- Closed complete shifted-correlation envelope at the conductor-four local factor. -/
theorem quadraticCharacterFour_correlation_norm_le (k l : ZMod 4) :
    ‖∑ x : ZMod 4,
      quadraticCharacterFour (x + k) * quadraticCharacterFour (x + l)‖ ≤ 4 := by
  calc
    _ ≤ ∑ x : ZMod 4,
        ‖quadraticCharacterFour (x + k) * quadraticCharacterFour (x + l)‖ :=
      norm_sum_le Finset.univ _
    _ = ∑ x : ZMod 4,
        ‖quadraticCharacterFour (x + k)‖ * ‖quadraticCharacterFour (x + l)‖ := by
      simp_rw [Complex.norm_mul]
    _ ≤ ∑ _x : ZMod 4, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_one₀ (quadraticCharacterFour_norm_le_one _) (norm_nonneg _)
        (quadraticCharacterFour_norm_le_one _)
    _ = 4 := by norm_num

/-- Closed complete shifted-correlation envelope at the first conductor-eight local factor. -/
theorem quadraticCharacterEight_correlation_norm_le (k l : ZMod 8) :
    ‖∑ x : ZMod 8,
      quadraticCharacterEight (x + k) * quadraticCharacterEight (x + l)‖ ≤ 8 := by
  calc
    _ ≤ ∑ x : ZMod 8,
        ‖quadraticCharacterEight (x + k) * quadraticCharacterEight (x + l)‖ :=
      norm_sum_le Finset.univ _
    _ = ∑ x : ZMod 8,
        ‖quadraticCharacterEight (x + k)‖ * ‖quadraticCharacterEight (x + l)‖ := by
      simp_rw [Complex.norm_mul]
    _ ≤ ∑ _x : ZMod 8, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_one₀ (quadraticCharacterEight_norm_le_one _) (norm_nonneg _)
        (quadraticCharacterEight_norm_le_one _)
    _ = 8 := by norm_num

/-- Closed complete shifted-correlation envelope at the second conductor-eight local factor. -/
theorem quadraticCharacterEightPrime_correlation_norm_le (k l : ZMod 8) :
    ‖∑ x : ZMod 8,
      quadraticCharacterEightPrime (x + k) * quadraticCharacterEightPrime (x + l)‖ ≤ 8 := by
  calc
    _ ≤ ∑ x : ZMod 8,
        ‖quadraticCharacterEightPrime (x + k) * quadraticCharacterEightPrime (x + l)‖ :=
      norm_sum_le Finset.univ _
    _ = ∑ x : ZMod 8,
        ‖quadraticCharacterEightPrime (x + k)‖ * ‖quadraticCharacterEightPrime (x + l)‖ := by
      simp_rw [Complex.norm_mul]
    _ ≤ ∑ _x : ZMod 8, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_one₀ (quadraticCharacterEightPrime_norm_le_one _) (norm_nonneg _)
        (quadraticCharacterEightPrime_norm_le_one _)
    _ = 8 := by norm_num

end RHTower
