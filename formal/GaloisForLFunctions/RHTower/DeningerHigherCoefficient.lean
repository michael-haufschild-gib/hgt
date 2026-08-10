import GaloisForLFunctions.RHTower.DeningerAbelCoefficient
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The higher-order Abel coefficients

Weighting the dilation integral by `x^r` replaces the window length `u/(i(i+1))` by the moment
`(u^{r+1}/(r+1)) (i^{-(r+1)} - (i+1)^{-(r+1)})`.  The bracket is at most `i^{-(r+1)}`, which for
`r ≥ 1` is at most `i^{-2}`, so the unconditional Möbius saving controls every order at once.

* `deningerWindowPow_integral` : the `r`-th moment of the dilation window.
* `deningerHigherCoefficient_summable` : **the order-`r` coefficients are summable.**
-/

namespace RHTower

open MeasureTheory

noncomputable section

/-- **The `r`-th moment of the dilation window.** -/
theorem deningerWindowPow_integral {i : ℕ} (hi : 0 < i) (r : ℕ) {u : ℝ} (hu : 0 < u) :
    (∫ x in (u / ((i : ℝ) + 1))..(u / (i : ℝ)), x ^ r)
      = u ^ (r + 1) / ((r : ℝ) + 1) *
        (1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1)) := by
  have hir : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  have hi1 : (0 : ℝ) < (i : ℝ) + 1 := by linarith
  rw [integral_pow]
  have hpow1 : (u / (i : ℝ)) ^ (r + 1) = u ^ (r + 1) / (i : ℝ) ^ (r + 1) := div_pow _ _ _
  have hpow2 : (u / ((i : ℝ) + 1)) ^ (r + 1) = u ^ (r + 1) / ((i : ℝ) + 1) ^ (r + 1) :=
    div_pow _ _ _
  rw [hpow1, hpow2]
  have hne1 : ((i : ℝ)) ^ (r + 1) ≠ 0 := by positivity
  have hne2 : (((i : ℝ) + 1)) ^ (r + 1) ≠ 0 := by positivity
  have hrne : ((r : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- The order-`r` bracket is nonnegative and dominated by an inverse square. -/
theorem deningerHigherBracket_le {i : ℕ} (hi : 0 < i) {r : ℕ} (hr : 1 ≤ r) :
    0 ≤ 1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1) ∧
      1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1) ≤ 1 / (i : ℝ) ^ 2 := by
  have hir : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hirpos : (0 : ℝ) < (i : ℝ) := lt_of_lt_of_le zero_lt_one hir
  have hi1 : (0 : ℝ) < (i : ℝ) + 1 := by linarith
  have hmono : (i : ℝ) ^ (r + 1) ≤ ((i : ℝ) + 1) ^ (r + 1) :=
    pow_le_pow_left₀ hirpos.le (by linarith) _
  have hnn : 1 / ((i : ℝ) + 1) ^ (r + 1) ≤ 1 / (i : ℝ) ^ (r + 1) :=
    one_div_le_one_div_of_le (by positivity) hmono
  refine ⟨by linarith, ?_⟩
  have hsq : (i : ℝ) ^ 2 ≤ (i : ℝ) ^ (r + 1) :=
    pow_le_pow_right₀ hir (by omega)
  have hle : 1 / (i : ℝ) ^ (r + 1) ≤ 1 / (i : ℝ) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) hsq
  have hpos : 0 ≤ 1 / ((i : ℝ) + 1) ^ (r + 1) := by positivity
  linarith

/-- **The order-`r` Abel coefficients are summable**, for every `r ≥ 1`, by comparison with the
inverse-square series that the unconditional Möbius saving already controls. -/
theorem deningerHigherCoefficient_summable {r : ℕ} (hr : 1 ≤ r) :
    Summable fun i : ℕ => |Sieve.mertensM i| *
      (1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1)) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
    deningerMertensM_invSq_summable
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · have hz : Sieve.mertensM 0 = 0 := by
        rw [Sieve.mertensM]
        simp
      simp [hz]
    · exact mul_nonneg (abs_nonneg _) (deningerHigherBracket_le hi hr).1
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · have hz : Sieve.mertensM 0 = 0 := by
        rw [Sieve.mertensM]
        simp
      simp [hz]
    · have hb := deningerHigherBracket_le hi hr
      have hstep : |Sieve.mertensM i| *
          (1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1))
          ≤ |Sieve.mertensM i| * (1 / (i : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hb.2 (abs_nonneg _)
      refine le_trans hstep (le_of_eq ?_)
      rw [mul_one_div]

end

end RHTower
