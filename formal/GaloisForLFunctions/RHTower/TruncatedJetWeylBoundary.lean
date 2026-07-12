import GaloisForLFunctions.RHTower.WeldWeylMultiplicity
import Mathlib.Data.Matrix.Basic

/-!
# Truncated-jet Weyl boundary holonomy

The natural finite local model for the prime dyadic Weyl relation is a truncated divisor jet.
On the coefficient basis `1, X, ..., X^n`, the clock is diagonal with entries
`1, zeta, ..., zeta^n`.  The one-sided jet shift is nilpotent.  Completing its missing top-to-bottom
arrow by a boundary holonomy `h` makes the shift cyclic, but the Weyl equation then has one and
only one possible boundary obstruction:

`h * (1 - zeta^(n+1))`.

Consequently a nonzero wrap satisfies the depth-`k` dyadic Weyl law only if `2^k` divides the jet
dimension `n+1`.  This is a positive form of the cutoff-completion no-go: an arbitrary invertible
wrap cannot manufacture the multiplicity ladder.  A source construction must prove that its own
boundary holonomy annihilates this exact scalar anomaly.

This is standard finite clock--shift algebra, used here as a bridge and obstruction theorem rather
than as new scientific knowledge.
-/

open Complex Matrix

noncomputable section

namespace RHTower

/-- The geometric clock on the truncated coefficient basis `1, X, ..., X^n`. -/
def truncatedJetClock (n : ℕ) (zeta : ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.diagonal fun i => zeta ^ (i : ℕ)

/-- The forward truncated-jet shift with a top-to-bottom boundary holonomy `h`.

The interior entries send the `j`-th coefficient to the `(j+1)`-st coefficient.  The only added
boundary entry sends the top coefficient back to the constant coefficient with weight `h`.
-/
def boundaryCompletedJetShift (n : ℕ) (h : ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j =>
    if (j : ℕ) + 1 = (i : ℕ) then 1
    else if (i : ℕ) = 0 ∧ (j : ℕ) = n then h else 0

@[simp]
theorem boundaryCompletedJetShift_zero_last (n : ℕ) (h : ℂ) :
    boundaryCompletedJetShift n h 0 (Fin.last n) = h := by
  simp [boundaryCompletedJetShift]

/-- **Exact top-jet anomaly.** The entire obstruction visible at the missing wrap entry is
`h * (1 - zeta^(n+1))`. -/
theorem boundaryCompletedJetWeylDefect_zero_last
    (n : ℕ) (zeta h : ℂ) :
    (truncatedJetClock n zeta * boundaryCompletedJetShift n h -
      zeta • (boundaryCompletedJetShift n h * truncatedJetClock n zeta))
        0 (Fin.last n) = h * (1 - zeta ^ (n + 1)) := by
  simp [truncatedJetClock, boundaryCompletedJetShift]
  rw [pow_succ]
  ring

/-- If the phase closes after `n+1` steps, every boundary holonomy gives an exact Weyl pair. -/
theorem boundaryCompletedJetWeyl_of_phase_pow_card
    (n : ℕ) (zeta h : ℂ) (hzeta : zeta ^ (n + 1) = 1) :
    truncatedJetClock n zeta * boundaryCompletedJetShift n h =
      zeta • (boundaryCompletedJetShift n h * truncatedJetClock n zeta) := by
  ext i j
  simp only [truncatedJetClock, Matrix.diagonal_mul, Matrix.mul_diagonal,
    smul_eq_mul, smul_apply]
  by_cases hstep : (j : ℕ) + 1 = (i : ℕ)
  · simp only [boundaryCompletedJetShift, hstep, if_pos]
    rw [← hstep, pow_succ]
    ring
  · by_cases hwrap : (i : ℕ) = 0 ∧ (j : ℕ) = n
    · simp only [boundaryCompletedJetShift]
      simp [hwrap]
      calc
        h = h * 1 := by ring
        _ = h * zeta ^ (n + 1) := by rw [hzeta]
        _ = zeta * h * zeta ^ n := by rw [pow_succ]; ring
        _ = zeta * (h * zeta ^ n) := by ring
    · have hwrap' : ¬ (i = 0 ∧ (j : ℕ) = n) := by
        simpa only [Fin.ext_iff, Fin.val_zero] using hwrap
      simp [boundaryCompletedJetShift, hstep, hwrap']

/-- Conversely, a nonzero boundary holonomy can satisfy the Weyl equation only when the phase
closes after exactly the dimension of the truncated jet. -/
theorem phase_pow_card_of_boundaryCompletedJetWeyl
    (n : ℕ) (zeta h : ℂ) (hh : h ≠ 0)
    (hweyl : truncatedJetClock n zeta * boundaryCompletedJetShift n h =
      zeta • (boundaryCompletedJetShift n h * truncatedJetClock n zeta)) :
    zeta ^ (n + 1) = 1 := by
  have hw := congrFun (congrFun hweyl (0 : Fin (n + 1))) (Fin.last n)
  simp [truncatedJetClock, boundaryCompletedJetShift] at hw
  apply mul_left_cancel₀ hh
  calc
    h * zeta ^ (n + 1) = zeta * (h * zeta ^ n) := by
      rw [pow_succ]
      ring
    _ = h := hw.symm
    _ = h * 1 := by ring

/-- The boundary-completed clock--shift law is exactly the scalar holonomy-closing equation. -/
theorem boundaryCompletedJetWeyl_iff_phase_pow_card
    (n : ℕ) (zeta h : ℂ) (hh : h ≠ 0) :
    (truncatedJetClock n zeta * boundaryCompletedJetShift n h =
      zeta • (boundaryCompletedJetShift n h * truncatedJetClock n zeta)) ↔
      zeta ^ (n + 1) = 1 := by
  exact ⟨phase_pow_card_of_boundaryCompletedJetWeyl n zeta h hh,
    boundaryCompletedJetWeyl_of_phase_pow_card n zeta h⟩

/-- At dyadic depth `k`, a nonzero boundary wrap forces `2^k` to divide the jet dimension. -/
theorem pow_dvd_card_of_dyadic_boundaryCompletedJetWeyl
    (n k : ℕ) (h : ℂ) (hh : h ≠ 0)
    (hweyl : truncatedJetClock n (Bottcher.dyadicRoot k) *
        boundaryCompletedJetShift n h =
      Bottcher.dyadicRoot k •
        (boundaryCompletedJetShift n h * truncatedJetClock n (Bottcher.dyadicRoot k))) :
    2 ^ k ∣ n + 1 := by
  exact ((dyadicWeylPhase_isPrimitiveRoot k).pow_eq_one_iff_dvd (n + 1)).mp
    (phase_pow_card_of_boundaryCompletedJetWeyl n (Bottcher.dyadicRoot k) h hh hweyl)

/-- **Positive no-go.** A nonzero boundary wrap cannot obey the Weyl law when its phase holonomy
does not close. -/
theorem not_boundaryCompletedJetWeyl_of_phase_pow_card_ne_one
    (n : ℕ) (zeta h : ℂ) (hh : h ≠ 0) (hzeta : zeta ^ (n + 1) ≠ 1) :
    truncatedJetClock n zeta * boundaryCompletedJetShift n h ≠
      zeta • (boundaryCompletedJetShift n h * truncatedJetClock n zeta) := by
  intro hweyl
  exact hzeta (phase_pow_card_of_boundaryCompletedJetWeyl n zeta h hh hweyl)

end RHTower
