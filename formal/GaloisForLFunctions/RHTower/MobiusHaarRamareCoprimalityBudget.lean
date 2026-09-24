import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Haar–Ramaré coprimality correction

When a prime–cofactor fibre is extended from primes coprime to the cofactor to all
primes, the added terms are indexed by prime divisors of that cofactor.  Ramaré's
normalization by one plus the number of distinct prime divisors absorbs the whole
added fibre.  Restricting cofactors to `1 ≤ m ≤ R` therefore costs at most `R`,
with no assumption about cancellation in Möbius sums or prime-counting errors.
-/

open Finset

namespace RHTower

/-- Any normalized fibre of bounded coefficients has an error budget of one per cofactor. -/
theorem normalized_fibre_budget (P : ℕ → Finset ℕ) (a : ℕ → ℝ) (w : ℕ → ℕ → ℝ)
    (ha : ∀ m, |a m| ≤ 1) (hw : ∀ m p, |w m p| ≤ 1) (R : ℕ) :
    |∑ m ∈ Finset.Icc 1 R,
        a m / ((P m).card + 1 : ℝ) * ∑ p ∈ P m, w m p| ≤ (R : ℝ) := by
  classical
  have hfibre (m : ℕ) :
      |∑ p ∈ P m, w m p| ≤ ((P m).card : ℝ) := by
    calc
      _ ≤ ∑ p ∈ P m, |w m p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ P m, (1 : ℝ) := Finset.sum_le_sum (by
        intro p hp
        exact hw m p)
      _ = ((P m).card : ℝ) := by simp
  have hterm (m : ℕ) :
      |a m / ((P m).card + 1 : ℝ) * ∑ p ∈ P m, w m p| ≤ 1 := by
    have hden : (0 : ℝ) < ((P m).card + 1 : ℝ) := by positivity
    rw [abs_mul, abs_div, abs_of_pos hden]
    rw [div_mul_eq_mul_div]
    have hprod : |a m| * |∑ p ∈ P m, w m p| ≤ ((P m).card : ℝ) := by
      calc
        _ ≤ 1 * |∑ p ∈ P m, w m p| :=
          mul_le_mul_of_nonneg_right (ha m) (abs_nonneg _)
        _ = |∑ p ∈ P m, w m p| := one_mul _
        _ ≤ _ := hfibre m
    apply (div_le_iff₀ hden).2
    nlinarith [hprod]
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 R,
        |a m / ((P m).card + 1 : ℝ) * ∑ p ∈ P m, w m p| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ Finset.Icc 1 R, (1 : ℝ) :=
      Finset.sum_le_sum (by intro m hm; exact hterm m)
    _ = (R : ℝ) := by simp [Nat.card_Icc]

/-- Adjacent-half Haar sign, supported up to `Y`. -/
def haarWeight (Y n : ℕ) : ℝ :=
  if n ≤ Y / 2 then -1 else if n ≤ Y then 1 else 0

theorem haarWeight_abs_le_one (Y n : ℕ) : |haarWeight Y n| ≤ 1 := by
  unfold haarWeight
  split_ifs <;> norm_num

/-- Prime-divisor correction from odd cofactors through `R` in the Haar–Ramaré split. -/
noncomputable def mobiusHaarCorrection (Y R : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 R,
    (if Odd m ∧ m ≤ Y / 3 then (((ArithmeticFunction.moebius m : ℤ) : ℝ)) else 0) /
      ((m.primeFactors.card : ℝ) + 1) *
        ∑ p ∈ m.primeFactors,
          if p ≤ Y / m then haarWeight Y (p * m) else 0

/-- The literal odd-Möbius coprimality correction costs at most the cofactor cutoff. -/
theorem abs_mobiusHaarCorrection_le (Y R : ℕ) :
    |mobiusHaarCorrection Y R| ≤ (R : ℝ) := by
  unfold mobiusHaarCorrection
  apply normalized_fibre_budget
    (fun m => m.primeFactors)
    (fun m => if Odd m ∧ m ≤ Y / 3 then (((ArithmeticFunction.moebius m : ℤ) : ℝ)) else 0)
    (fun m p => if p ≤ Y / m then haarWeight Y (p * m) else 0)
  · intro m
    by_cases h : Odd m ∧ m ≤ Y / 3
    · simp only [if_pos h]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := m))
    · simp [h]
  · intro m p
    split_ifs
    · exact haarWeight_abs_le_one Y (p * m)
    · simp

end RHTower
