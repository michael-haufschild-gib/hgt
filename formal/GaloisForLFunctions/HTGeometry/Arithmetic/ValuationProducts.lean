import GaloisForLFunctions.HTGeometry.Arithmetic.ValuationParity

/-!
# Valuations of finite products and split polynomials

A point with negative valuation is farther from every integral root than
the roots are from zero. Every linear factor therefore has the valuation
of the point, and a split polynomial records its degree exactly.
-/

namespace GaloisForLFunctions.HTGeometry.Arithmetic

open Finset

variable {p : ℕ} [Fact p.Prime]

/-- Additivity of the rational valuation on a nonvanishing finite product. -/
theorem val_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, f i ≠ 0 := fun i hi => h i (mem_insert_of_mem hi)
    rw [prod_insert ha, sum_insert ha,
      padicValRat.mul (h a (mem_insert_self _ _)) (prod_ne_zero_iff.mpr hs), ih hs]

/-- Subtracting an integral rational from a nonintegral rational preserves
the latter's valuation. The integral rational may be zero. -/
theorem val_sub_integral_of_neg {x a : ℚ} (hx : padicValRat p x < 0)
    (ha : 0 ≤ padicValRat p a) : padicValRat p (x - a) = padicValRat p x := by
  by_cases ha0 : a = 0
  · simp [ha0]
  have hx0 : x ≠ 0 := by
    intro h
    simp [h] at hx
  rw [val_sub_eq_min hx0 ha0 (by omega), min_eq_left (by omega)]

/-- A split monic polynomial of degree `|s|` has valuation `|s| v(x)` at
every nonintegral rational, provided its roots are integral at the prime. -/
theorem val_split_product_of_neg {ι : Type*} (s : Finset ι) (a : ι → ℚ) {x : ℚ}
    (hx : padicValRat p x < 0) (ha : ∀ i ∈ s, 0 ≤ padicValRat p (a i)) :
    padicValRat p (∏ i ∈ s, (x - a i)) = (s.card : ℤ) * padicValRat p x := by
  rw [val_finset_prod s (fun i => x - a i) (fun i hi =>
    sub_ne_zero_of_val_ne (p := p) (by have h := ha i hi; omega))]
  calc
    ∑ i ∈ s, padicValRat p (x - a i) = ∑ _i ∈ s, padicValRat p x :=
      sum_congr rfl (fun i hi => val_sub_integral_of_neg hx (ha i hi))
    _ = _ := by simp

end GaloisForLFunctions.HTGeometry.Arithmetic
