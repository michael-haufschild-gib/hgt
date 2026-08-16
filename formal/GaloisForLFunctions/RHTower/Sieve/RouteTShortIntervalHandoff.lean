import GaloisForLFunctions.RHTower.Sieve.MaynardUpperPhaseHandoff
import GaloisForLFunctions.RHTower.Sieve.MaynardRouteTHighAmplitudeCount

/-!
# The Route-T fixed short-interval handoff

The Route-T upper physical window at height exponent `mu` has additive width `x^(1-1/mu)`, and
above the handoff height that exponent is at least `3/4 - d/2`, where `d` is the Maynard long
global amplitude deficit.  Since the corpus proves `d < 1/100`, every such exponent exceeds the
fixed value `7/10`.

Consequently a prime supplied in the *fixed* window `(x, x + x^{7/10}]` already lies in every
Route-T upper physical window: the continuum of route-specific seam widths collapses to one
classical prime-supply exponent.  Nothing route-specific and no zero-density input is used here;
this file is exactly the unconditional scalar composition.
-/

namespace RHTower.Sieve

/-- The fixed exponent `7/10` lies strictly below the Route-T handoff width exponent. -/
theorem sevenTenths_lt_routeTPhysicalSliceHandoffTheta :
    (7 : ℝ) / 10 < routeTPhysicalSliceHandoffTheta := by
  have hd := maynardLongGlobalAmplitudeDeficit_lt_one_hundredth
  have hpos := maynardLongGlobalAmplitudeDeficit_pos
  dsimp only [routeTPhysicalSliceHandoffTheta]
  linarith

/-- Above the handoff height every physical width exponent exceeds the fixed value `7/10`. -/
theorem sevenTenths_lt_widthExponent {mu : ℝ} (hmu : routeTPhysicalSliceHandoffMu ≤ mu) :
    (7 : ℝ) / 10 < 1 - 1 / mu :=
  lt_of_lt_of_le sevenTenths_lt_routeTPhysicalSliceHandoffTheta
    (routeTPhysicalSliceHandoffTheta_le_widthExponent hmu)

/-- The fixed window is contained in every Route-T upper physical window. -/
theorem routeT_window_contains_sevenTenths_window {x : ℝ} (hx : 1 ≤ x) {mu : ℝ}
    (hmu : routeTPhysicalSliceHandoffMu ≤ mu) :
    x + x ^ ((7 : ℝ) / 10) ≤ x + x ^ (1 - 1 / mu) :=
  by linarith [Real.rpow_le_rpow_of_exponent_le hx (sevenTenths_lt_widthExponent hmu).le]

/-- **The Route-T handoff transfer.**  A prime supplied in the fixed window of width `x^{7/10}`
already lies in every Route-T upper physical window.  This is the exact unconditional composition
that removes the signed over-height boundary as an independent analytic problem; the remaining
input is the classical short-interval prime supply at the single fixed exponent `7/10`. -/
theorem routeT_prime_in_upperWindow {x : ℝ} (hx : 1 ≤ x) {mu : ℝ}
    (hmu : routeTPhysicalSliceHandoffMu ≤ mu) {p : ℕ} (hp : Nat.Prime p)
    (hlow : x < (p : ℝ)) (hhigh : (p : ℝ) ≤ x + x ^ ((7 : ℝ) / 10)) :
    Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ x + x ^ (1 - 1 / mu) :=
  ⟨hp, hlow, le_trans hhigh (routeT_window_contains_sevenTenths_window hx hmu)⟩

end RHTower.Sieve
