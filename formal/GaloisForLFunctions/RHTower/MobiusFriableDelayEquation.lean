import GaloisForLFunctions.RHTower.MobiusFriableIntegerSeamProfile
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The Möbius delay equation and its first two branches

The friable profile for the Möbius function solves the delay equation

`v φ'(v) = φ(v-1)`  for `v > 1`,   `φ = 1` on `(0,1]`.

On the first branch `1 < v < 2` the argument `v-1` lies in the initial range, so the equation reads
`v φ'(v) = 1`; with `φ(1) = 1` this determines `φ(v) = 1 + log v` uniquely — the uniqueness is a
mean-value argument, not a convention.  On the second branch `2 < v < 3` the argument `v-1` lies in
the first branch, so the equation *propagates* the closed form and gives
`φ'(v) = (1 + log(v-1))/v`.

Together with the second derivatives already recorded, these are the two branches whose one-sided
limits at `v = 2` produce the seam jump.
-/

noncomputable section

namespace RHTower

open Set

/-- The delay equation on the first branch: `φ'(v) = φ(v-1)/v = 1/v`. -/
theorem hasDerivAt_mobiusFriableDelayBelowTwo {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt mobiusFriableDelayBelowTwo (1 / v) v := by
  have h := mobiusFriableDelayBelowTwo_formula_hasDerivAt v hv
  rw [one_div]
  exact h

/-- **Uniqueness of the first branch.**  Any continuous solution of the delay equation on `[1,2]`
with the initial value `1` is `1 + log v`. -/
theorem eq_mobiusFriableDelayBelowTwo_of_delayEquation
    {g : ℝ → ℝ} (hcont : ContinuousOn g (Icc 1 2))
    (hderiv : ∀ v ∈ Ico (1 : ℝ) 2, HasDerivWithinAt g (1 / v) (Ici v) v)
    (hinit : g 1 = 1) :
    ∀ v ∈ Icc (1 : ℝ) 2, g v = mobiusFriableDelayBelowTwo v := by
  set h : ℝ → ℝ := fun v => g v - mobiusFriableDelayBelowTwo v with hh
  have hlogcont : ContinuousOn mobiusFriableDelayBelowTwo (Icc 1 2) := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := hv
    have hvne : v ≠ 0 := by intro hcon; rw [hcon] at hv1; linarith
    exact ((hasDerivAt_mobiusFriableDelayBelowTwo hvne).continuousAt).continuousWithinAt
  have hcont' : ContinuousOn h (Icc 1 2) := hcont.sub hlogcont
  have hderiv' : ∀ v ∈ Ico (1 : ℝ) 2, HasDerivWithinAt h 0 (Ici v) v := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := hv
    have hvne : v ≠ 0 := by intro hcon; rw [hcon] at hv1; linarith
    have hd := (hasDerivAt_mobiusFriableDelayBelowTwo hvne).hasDerivWithinAt (s := Ici v)
    have hsub := (hderiv v ⟨hv1, hv2⟩).sub hd
    have hzero : (1 : ℝ) / v - 1 / v = 0 := by ring
    rw [hzero] at hsub
    exact hsub
  have hconst := constant_of_has_deriv_right_zero hcont' hderiv'
  intro v hv
  have hv0 := hconst v hv
  rw [hh] at hv0
  simp only at hv0
  have h1 : mobiusFriableDelayBelowTwo 1 = 1 := by
    rw [mobiusFriableDelayBelowTwo, Real.log_one]
    ring
  rw [hinit, h1] at hv0
  linarith

/-- **The delay equation propagates to the second branch.**  For `v` in the second branch the
argument `v-1` sits in the first, so the recorded derivative is exactly `φ(v-1)/v`. -/
theorem mobiusFriableDelayDerivativeAboveTwo_eq (v : ℝ) :
    mobiusFriableDelayDerivativeAboveTwo v = mobiusFriableDelayBelowTwo (v - 1) / v := by
  rw [mobiusFriableDelayDerivativeAboveTwo, mobiusFriableDelayBelowTwo]

end RHTower
