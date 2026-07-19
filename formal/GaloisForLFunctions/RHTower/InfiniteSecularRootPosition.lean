import GaloisForLFunctions.RHTower.ConstrainedProlateInfiniteSecular

/-!
# Locating the constrained root by the sign of the secular function

Inside the first gap the secular function is strictly increasing and vanishes exactly at the
constrained root.  So the position of any point of the gap relative to the root is decided by the
*sign* of the secular function there: the point lies below the root precisely when the secular
function is negative.

This converts statements of the form "the root clears a given threshold" — which is how the
depth-`k` bracket hypothesis is phrased — into an explicit inequality between the coordinate
weights and the scales, with no reference to the root itself.
-/

open Set

namespace RHTower

variable {d ℓ : ℕ → ℝ}

/-- **The root is located by the sign of the secular function.** -/
theorem lt_infiniteSecularRoot_iff (h01 : d 0 < d 1) (h12 : d 1 < d 2)
    (hd2 : ∀ j, d 2 ≤ d (j + 2)) (hsum : Summable fun j => ℓ j ^ 2)
    (hℓ0 : ℓ 0 ≠ 0) (hℓ1 : ℓ 1 ≠ 0) {x : ℝ} (hx : x ∈ Ioo (d 0) (d 1)) :
    x < infiniteSecularRoot d ℓ ↔ infiniteSecular d ℓ x < 0 := by
  obtain ⟨hrmem, hr0, _⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsum hℓ0 hℓ1
  have hmono := infiniteSecular_strictMonoOn h12 hd2 hsum hℓ0
  constructor
  · intro hlt
    have := hmono hx hrmem hlt
    rw [hr0] at this
    exact this
  · intro hneg
    by_contra hle
    rcases eq_or_lt_of_le (not_lt.mp hle) with heq | hgt
    · rw [← heq, hr0] at hneg
      exact absurd hneg (lt_irrefl 0)
    · have := hmono hrmem hx hgt
      rw [hr0] at this
      linarith

/-- The threshold form: the root clears `x` exactly when the secular function is negative at
`x`. -/
theorem lt_infiniteSecularRoot_of_infiniteSecular_neg (h01 : d 0 < d 1) (h12 : d 1 < d 2)
    (hd2 : ∀ j, d 2 ≤ d (j + 2)) (hsum : Summable fun j => ℓ j ^ 2)
    (hℓ0 : ℓ 0 ≠ 0) (hℓ1 : ℓ 1 ≠ 0) {x : ℝ} (hx : x ∈ Ioo (d 0) (d 1))
    (hneg : infiniteSecular d ℓ x < 0) :
    x < infiniteSecularRoot d ℓ :=
  (lt_infiniteSecularRoot_iff h01 h12 hd2 hsum hℓ0 hℓ1 hx).mpr hneg

end RHTower
