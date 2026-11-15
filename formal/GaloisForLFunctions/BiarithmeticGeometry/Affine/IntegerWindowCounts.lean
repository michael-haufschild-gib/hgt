import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact integer windows and finite intersection counts

An absolute-distance bound on an integer index is exactly membership in
the interval with endpoints obtained by rounding the radius down. The
interval contains at most `2 * R + 1` integers when its radius is nonnegative.
Filtering this window enumerates every predicate satisfying that bound.
-/

namespace GaloisForLFunctions.BiarithmeticGeometry.IntegerWindowCounts
noncomputable section

/-- The full integer interval within a real radius of an integer center. -/
def integerWindow (i : ℤ) (R : ℝ) : Finset ℤ := Finset.Icc (i - ⌊R⌋) (i + ⌊R⌋)

/-- Rounding down loses no integer satisfying the real absolute-distance constraint. -/
theorem mem_integerWindow_iff (i j : ℤ) (R : ℝ) :
    j ∈ integerWindow i R ↔ |(i : ℝ) - (j : ℝ)| ≤ R := by
  rw [integerWindow, Finset.mem_Icc]
  constructor
  · rintro ⟨hl, hu⟩
    have hi : |i - j| ≤ ⌊R⌋ := abs_le.mpr ⟨by omega, by omega⟩
    have hr : ((|i - j| : ℤ) : ℝ) ≤ R := Int.le_floor.mp hi
    simpa only [Int.cast_abs, Int.cast_sub] using hr
  · intro h
    have hi : |i - j| ≤ ⌊R⌋ := Int.le_floor.mpr (by
      simpa only [Int.cast_abs, Int.cast_sub] using h)
    obtain ⟨hl, hu⟩ := abs_le.mp hi
    constructor <;> omega

/-- The cardinality bound retains the exact additive constant one. -/
theorem card_integerWindow_le (i : ℤ) (R : ℝ) (hR : 0 ≤ R) :
    ((integerWindow i R).card : ℝ) ≤ 2 * R + 1 := by
  have hf : 0 ≤ ⌊R⌋ := Int.floor_nonneg.mpr hR
  rw [integerWindow, Int.card_Icc,
    show i + ⌊R⌋ + 1 - (i - ⌊R⌋) = 2 * ⌊R⌋ + 1 by ring]
  have hn : 0 ≤ 2 * ⌊R⌋ + 1 := by omega
  have hcast : (((2 * ⌊R⌋ + 1).toNat : ℕ) : ℝ) = ((2 * ⌊R⌋ + 1 : ℤ) : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hn)
  rw [hcast]
  push_cast
  linarith only [Int.floor_le R]

/-- A predicate with a uniform integer-distance bound has a complete finite enumeration of bounded size. -/
theorem exists_finset_of_abs_sub_le (i : ℤ) (R : ℝ) (hR : 0 ≤ R) (P : ℤ → Prop)
    (hP : ∀ j, P j → |(i : ℝ) - (j : ℝ)| ≤ R) :
    ∃ S : Finset ℤ, (∀ j, j ∈ S ↔ P j) ∧ (S.card : ℝ) ≤ 2 * R + 1 := by
  classical
  refine ⟨(integerWindow i R).filter P, ?_, ?_⟩
  · intro j
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨(mem_integerWindow_iff i j R).mpr (hP j h), h⟩⟩
  · calc
      _ ≤ ((integerWindow i R).card : ℝ) := by
        exact_mod_cast Finset.card_filter_le (integerWindow i R) P
      _ ≤ _ := card_integerWindow_le i R hR

#print axioms mem_integerWindow_iff
#print axioms card_integerWindow_le
#print axioms exists_finset_of_abs_sub_le

end
end GaloisForLFunctions.BiarithmeticGeometry.IntegerWindowCounts
