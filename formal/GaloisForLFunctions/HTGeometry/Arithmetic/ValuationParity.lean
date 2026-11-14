import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.Ring

/-!
# Odd valuation prevents cancellation

Terms of different valuations cannot cancel. Consequently an odd-valuation
parameter times a square cannot cancel a unit. This gives unit-valued
Möbius transforms and integral reciprocal factors for local selectors.
-/

namespace GaloisForLFunctions.HTGeometry.Arithmetic

variable {p : ℕ}

theorem add_ne_zero_of_val_ne {a b : ℚ}
    (h : padicValRat p a ≠ padicValRat p b) : a + b ≠ 0 := by
  intro heq
  exact h (by rw [eq_neg_of_add_eq_zero_left heq, padicValRat.neg])

theorem sub_ne_zero_of_val_ne {a b : ℚ}
    (h : padicValRat p a ≠ padicValRat p b) : a - b ≠ 0 := by
  intro heq
  exact h (congrArg (padicValRat p) (sub_eq_zero.mp heq))

variable [Fact p.Prime]

/-- Distinct nonzero terms have no valuation cancellation under subtraction. -/
theorem val_sub_eq_min {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : padicValRat p a ≠ padicValRat p b) :
    padicValRat p (a - b) = min (padicValRat p a) (padicValRat p b) := by
  rw [sub_eq_add_neg, padicValRat.add_eq_min
    (by simpa only [sub_eq_add_neg] using sub_ne_zero_of_val_ne h)
    ha (neg_ne_zero.mpr hb) (by simpa only [padicValRat.neg] using h), padicValRat.neg]

/-- A nonunit parameter makes the two Möbius factors have the same valuation. -/
theorem mobius_val_zero {s : ℚ} (hs : padicValRat p s ≠ 0) :
    padicValRat p ((1 - s) / (1 + s)) = 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    exact hs (by rw [h, padicValRat.zero])
  have hval : padicValRat p (1 : ℚ) ≠ padicValRat p s := by
    simpa only [padicValRat.one] using hs.symm
  have hsub := sub_ne_zero_of_val_ne hval
  have hadd := add_ne_zero_of_val_ne hval
  rw [padicValRat.div hsub hadd, val_sub_eq_min one_ne_zero hs0 hval,
    padicValRat.add_eq_min hadd one_ne_zero hs0 hval, sub_self]

/-- Multiplying by a nonzero square preserves odd valuation. -/
theorem not_even_val_mul_sq {R d : ℚ} (hR : ¬ Even (padicValRat p R))
    (hd : d ≠ 0) : ¬ Even (padicValRat p (R * d ^ 2)) := by
  have hR0 : R ≠ 0 := by
    intro h
    exact hR (by simp [h])
  rw [padicValRat.mul hR0 (pow_ne_zero 2 hd), padicValRat.pow]
  rw [Int.even_iff] at hR ⊢
  norm_cast
  omega

/-- Every factor used by an odd-valuation selector is nonzero. -/
theorem odd_factor_ne_zero {R : ℚ} (hR : ¬ Even (padicValRat p R)) (d : ℚ) :
    1 + R * d ^ 2 ≠ 0 := by
  by_cases hd : d = 0
  · simp [hd]
  apply add_ne_zero_of_val_ne (p := p)
  rw [padicValRat.one]
  intro heq
  exact not_even_val_mul_sq hR hd (heq ▸ Even.zero)

/-- The factor valuation is exactly the smaller of zero and the weighted
test valuation. There is no cancellation term. -/
theorem odd_factor_val {R d : ℚ} (hR : ¬ Even (padicValRat p R)) (hd : d ≠ 0) :
    padicValRat p (1 + R * d ^ 2) =
      min 0 (padicValRat p R + 2 * padicValRat p d) := by
  have hR0 : R ≠ 0 := by
    intro h
    exact hR (by simp [h])
  have hval : padicValRat p 1 ≠ padicValRat p (R * d ^ 2) := by
    rw [padicValRat.one]
    intro heq
    exact not_even_val_mul_sq hR hd (heq ▸ Even.zero)
  rw [padicValRat.add_eq_min (odd_factor_ne_zero hR d) one_ne_zero
    (mul_ne_zero hR0 (pow_ne_zero 2 hd)) hval, padicValRat.one,
    padicValRat.mul hR0 (pow_ne_zero 2 hd), padicValRat.pow]
  rfl

/-- Reciprocal selector factors are integral even when the tests are not. -/
theorem odd_factor_inv_integral {R : ℚ} (hR : ¬ Even (padicValRat p R)) (d : ℚ) :
    0 ≤ padicValRat p (1 + R * d ^ 2)⁻¹ := by
  by_cases hd : d = 0
  · simp [hd]
  rw [padicValRat.inv, odd_factor_val hR hd]
  exact neg_nonneg.mpr (min_le_left _ _)

end GaloisForLFunctions.HTGeometry.Arithmetic
