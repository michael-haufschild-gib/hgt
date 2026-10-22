import GaloisForLFunctions.ScaleSignedIncidenceCriticality.ThePrimeWindowLadderConverges
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheHeightFaceUnitIsTheFirstOffLineHorizon

/-!
# The two ladders match under the explicit-formula dictionary

The field now has a convergent ladder on each side of the critical form: the truncated divisor in
the horizon unit, with exact limit `(1+T)⁻¹`, and the prime window in the defect-scale unit, with
exact limit `1/m₀(R)`. Compared naively in their own parameters the second looks exponentially
better, since `m₀(R) ≥ e^{2R}` (`exp_le_leastOutsideWindow`). That comparison is an artefact: the
parameters are not the same kind of quantity.

The explicit formula fixes the dictionary. A test of aperture `a` reaches the prime indices with
`log m < 2a`, so a window of radius `R` reaches up to `e^{2R}`; and that is also the height at which
the zero side has to be read, because the resolution a bounded reading achieves is the reciprocal of
its own parameter. Setting

`T + 1 = e^{2R}`

the two limits coincide (`theTwoLaddersMatch`): the height ladder gives exactly `e^{−2R}` and the
window ladder gives at most `e^{−2R}`. Neither side is more efficient; they are the same ladder
written in two variables related by an exponential.

This is the first quantitative bridge between the faces' *progress measures*, as
`TheTwoFacesReadOneScaleDatum` is between their criteria. Its practical content is a conversion
rate: one unit of prime-window radius is worth an exponential amount of height, and a mechanism that
spends its resources on one side can price them on the other.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The window reaches `e^{2R}` -/

/-- **The first index outside the window is at least `e^{2R}`.** -/
theorem exp_le_leastOutsideWindow (R : ℝ) :
    Real.exp (2 * R) ≤ (leastOutsideWindow R : ℝ) := by
  obtain ⟨hm0, hlog0⟩ := leastOutsideWindow_spec R
  have hpos : (0 : ℝ) < (leastOutsideWindow R : ℝ) := by
    have h2 : (2 : ℝ) ≤ (leastOutsideWindow R : ℝ) := by exact_mod_cast hm0
    linarith
  calc Real.exp (2 * R) ≤ Real.exp (Real.log (leastOutsideWindow R)) :=
        Real.exp_le_exp.mpr hlog0
    _ = (leastOutsideWindow R : ℝ) := Real.exp_log hpos

/-- Hence the window ladder's limit is at most `e^{−2R}`. -/
theorem resolutionLimit_windowReading_le_exp (R : ℝ) :
    resolutionLimit weightDefectScale (windowReading R)
        (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) ≤ Real.exp (-(2 * R)) := by
  rw [resolutionLimit_weightDefectScale_windowReading]
  have hexp : (0 : ℝ) < Real.exp (2 * R) := Real.exp_pos _
  have hle := exp_le_leastOutsideWindow R
  have hpos : (0 : ℝ) < (leastOutsideWindow R : ℝ) := lt_of_lt_of_le hexp hle
  rw [Real.exp_neg]
  exact (inv_le_inv₀ hpos hexp).mpr hle

/-! ### 2. The matched height -/

/-- The height the dictionary assigns to a window of radius `R`. -/
noncomputable def matchedHeight (R : ℝ) : ℝ := Real.exp (2 * R) - 1

theorem matchedHeight_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ matchedHeight R := by
  have h1 : (1 : ℝ) ≤ Real.exp (2 * R) := Real.one_le_exp (by positivity)
  simp only [matchedHeight]; linarith

/-- **At the matched height the horizon ladder's limit is exactly `e^{−2R}`.** -/
theorem resolutionLimit_horizonFrequency_matchedHeight {L : ℝ} (hL : 0 < L) {R : ℝ}
    (hR : 0 ≤ R) :
    resolutionLimit horizonFrequency (heightReading (matchedHeight R)) (onLineLattice hL) =
      Real.exp (-(2 * R)) := by
  rw [resolutionLimit_horizonFrequency_heightReading hL (matchedHeight_nonneg hR),
    Real.exp_neg]
  congr 1
  simp only [matchedHeight]
  ring

/-! ### 3. The match -/

/-- **The two ladders match.** Under the dictionary `T + 1 = e^{2R}` the horizon ladder's limit is
exactly `e^{−2R}` and the window ladder's is at most `e^{−2R}`: one unit of prime-window radius is
worth an exponential amount of height, and neither side is intrinsically more efficient. -/
theorem theTwoLaddersMatch {L : ℝ} (hL : 0 < L) {R : ℝ} (hR : 0 ≤ R) :
    resolutionLimit horizonFrequency (heightReading (matchedHeight R)) (onLineLattice hL) =
        Real.exp (-(2 * R)) ∧
      resolutionLimit weightDefectScale (windowReading R)
        (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) ≤ Real.exp (-(2 * R)) :=
  ⟨resolutionLimit_horizonFrequency_matchedHeight hL hR, resolutionLimit_windowReading_le_exp R⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
