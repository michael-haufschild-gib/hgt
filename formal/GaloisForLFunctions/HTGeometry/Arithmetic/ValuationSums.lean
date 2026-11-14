import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Valuation bounds on finite sums

Zero terms satisfy every divisibility precision, although the totalized
rational valuation assigns zero to zero. Keeping this alternative explicit
makes finite-sum estimates valid at arbitrary, including positive, precision.
-/

namespace GaloisForLFunctions.HTGeometry.Arithmetic

open Finset

variable {p : ℕ} [Fact p.Prime]

/-- A nonzero sum of terms divisible to precision `k` is divisible to that
precision; zero summands cause no loss. -/
theorem val_finset_sum_ge {ι : Type*} (s : Finset ι) (f : ι → ℚ) (k : ℤ)
    (h : ∀ i ∈ s, f i = 0 ∨ k ≤ padicValRat p (f i))
    (hs : ∑ i ∈ s, f i ≠ 0) : k ≤ padicValRat p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact False.elim (hs (by simp))
  | @insert a s ha ih =>
    rw [sum_insert ha] at hs ⊢
    have ht : ∀ i ∈ s, f i = 0 ∨ k ≤ padicValRat p (f i) :=
      fun i hi => h i (mem_insert_of_mem hi)
    rcases h a (mem_insert_self _ _) with hz | hk
    · rw [hz, zero_add] at hs ⊢
      exact ih ht hs
    · by_cases hz : ∑ i ∈ s, f i = 0
      · simpa only [hz, add_zero] using hk
      · exact (le_min hk (ih ht hz)).trans (padicValRat.min_le_padicValRat_add hs)

/-- The sum of integral rationals is integral, even when it vanishes. -/
theorem val_finset_sum_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, 0 ≤ padicValRat p (f i)) :
    0 ≤ padicValRat p (∑ i ∈ s, f i) := by
  by_cases hs : ∑ i ∈ s, f i = 0
  · simp [hs]
  · exact val_finset_sum_ge s f 0 (fun i hi => Or.inr (h i hi)) hs

end GaloisForLFunctions.HTGeometry.Arithmetic
