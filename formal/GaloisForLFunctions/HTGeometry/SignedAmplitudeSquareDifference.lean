import Mathlib

/-!
# Signed kernels as differences of squared amplitudes

The finite measurement protocol of `wigner-smith-finite-resolution-law-escape` (equation `(17a)`)
needs every real signed smooth differentiation kernel `w` to be a difference of two squared smooth
amplitudes, so that the physical squared-amplitude measurement `(6)` recovers the jet `(17)` from
finitely many packet preparations.  This file formalizes that elementary algebraic identity: with a
cutoff `χ` equal to `1` on `supp w` and a majorant `m > ‖w‖∞`,
`w = (χ√(m+w))² − (√m·χ)²`.
-/

open Real

namespace GaloisForLFunctions.HTGeometry

/-- **Signed value as a difference of two squares.**  If `a² c = c` (e.g. `a = ±1` wherever `c ≠ 0`)
and `0 ≤ m`, `0 ≤ m + c`, then `c = (a√(m+c))² − (√m·a)²`. -/
theorem signed_eq_sq_amplitude_difference {a m c : ℝ} (hm : 0 ≤ m) (hmc : 0 ≤ m + c)
    (ha : a ^ 2 * c = c) :
    c = (a * Real.sqrt (m + c)) ^ 2 - (Real.sqrt m * a) ^ 2 := by
  rw [mul_pow, mul_pow, Real.sq_sqrt hmc, Real.sq_sqrt hm]
  have h : a ^ 2 * (m + c) - m * a ^ 2 = a ^ 2 * c := by ring
  rw [h, ha]

/-- **Signed smooth kernel as a difference of two squared amplitudes** `(17a)`.  A real kernel `w`
with a cutoff `χ` satisfying `χ² w = w` (i.e. `χ = 1` on `supp w`) and majorant `m > ‖w‖∞` is exactly
`w = (χ√(m+w))² − (√m·χ)²`, so it is measured by two squared-amplitude packet preparations. -/
theorem signedKernel_eq_sq_amplitude_difference {w χ : ℝ → ℝ} {m : ℝ} (hm : 0 ≤ m)
    (hmc : ∀ x, 0 ≤ m + w x) (hχ : ∀ x, (χ x) ^ 2 * w x = w x) (x : ℝ) :
    w x = (χ x * Real.sqrt (m + w x)) ^ 2 - (Real.sqrt m * χ x) ^ 2 :=
  signed_eq_sq_amplitude_difference hm (hmc x) (hχ x)

end GaloisForLFunctions.HTGeometry
