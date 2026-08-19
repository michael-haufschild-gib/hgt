import GaloisForLFunctions.RHTower.Sieve.DampedCorrExp

/-!
# The correction is invariant under a vertical shift

`dampedCorrBound P c` depends only on the abscissa, and `Re (s + iτ) = Re s`, so the bound
`‖dampedInvZeta‖ ≤ ‖invZeta‖ · dampedCorrBound` holds at every point of a vertically shifted contour
with the same constant.

This is the fact that makes the twisted chain factor exactly as the untwisted one does: the twisted
damped series at `s` is `dampedInvZeta P t (s + iτ)`, so each of its edge bounds is the corresponding
`invZeta` bound times the same `dampedCorrBound P c`.
-/

namespace RHTower.Sieve

open Complex

noncomputable section

/-- **The factorisation at a vertically shifted point.** -/
theorem norm_dampedInvZeta_shift_le {P : Finset ℕ} (hP : ∀ q ∈ P, 2 ≤ q) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) {c : ℝ} (hc : 1 / 2 ≤ c) {s : ℂ} (hcs : c ≤ s.re) (τ : ℝ) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ‖invZeta (s + (τ : ℂ) * Complex.I)‖ ≤ M) :
    ‖dampedInvZeta P t (s + (τ : ℂ) * Complex.I)‖ ≤ M * dampedCorrBound P c := by
  refine norm_dampedInvZeta_le hP ht0 ht1 hc ?_ hM0 hM
  have hre : (s + (τ : ℂ) * Complex.I).re = s.re := by simp
  rw [hre]
  exact hcs

end

end RHTower.Sieve
