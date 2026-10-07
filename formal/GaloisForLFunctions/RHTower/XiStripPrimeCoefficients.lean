import GaloisForLFunctions.RHTower.XiKummerDeckActions

/-!
# Prime coefficients surviving analytic Kummer collapse

The odd part of each actual source unit root under the strip deck action is
exactly `2*i*beta_n*v`. Dividing by its common nonzero factor recovers the
original prime exponential, and odd-part ratios recover relative clocks.
This imposes no real-form condition on their values at Xi zeros and makes no
uniformizer claim at multiple zeros.
-/

noncomputable section
namespace RHTower.XiGlobalKummer
open GaloisForLFunctions.HTGeometry
local instance : CharZero K := charZero_of_injective_algebraMap constPlane_injective
local instance : CharZero stripQuadraticField :=
  charZero_of_injective_algebraMap (algebraMap K stripQuadraticField).injective

theorem strip_halfUnit_sub_deck (n : ℕ) :
    halfUnitFromRoot stripComponentXiRoot n -
      stripComponentDeck (halfUnitFromRoot stripComponentXiRoot n) =
    2 * algebraMap Marked stripQuadraticField markedI *
      algebraMap Marked stripQuadraticField (betaMarked n) * stripComponentXiRoot := by
  rw [stripComponentDeck_halfUnit,
    ← eq_inv_of_mul_eq_one_right (halfUnitFromRoot_mul_opposite stripComponentXiRoot_sq n)]
  unfold halfUnitFromRoot
  ring

private theorem stripMappedI_ne_zero : algebraMap Marked stripQuadraticField markedI ≠ 0 := by
  apply (map_ne_zero (algebraMap Marked stripQuadraticField)).mpr
  intro h
  have hi := markedI_sq
  rw [h] at hi
  norm_num at hi

theorem strip_odd_denominator_ne_zero :
    2 * algebraMap Marked stripQuadraticField markedI * stripComponentXiRoot ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) stripMappedI_ne_zero)
    (xiRoot_ne_zero stripComponentXiRoot_sq)

/-- The coefficient extracted from the actual strip involution's odd part. -/
def stripOddUnitCoefficient (n : ℕ) : stripQuadraticField :=
  (halfUnitFromRoot stripComponentXiRoot n -
    stripComponentDeck (halfUnitFromRoot stripComponentXiRoot n)) /
      (2 * algebraMap Marked stripQuadraticField markedI * stripComponentXiRoot)

/-- No prime coefficient is lost when the global division classes collapse. -/
theorem stripOddUnitCoefficient_eq (n : ℕ) :
    stripOddUnitCoefficient n = algebraMap Marked stripQuadraticField (betaMarked n) := by
  rw [stripOddUnitCoefficient, strip_halfUnit_sub_deck]
  rw [show 2 * algebraMap Marked stripQuadraticField markedI *
      algebraMap Marked stripQuadraticField (betaMarked n) * stripComponentXiRoot =
      algebraMap Marked stripQuadraticField (betaMarked n) *
        (2 * algebraMap Marked stripQuadraticField markedI * stripComponentXiRoot) by ring]
  exact mul_div_cancel_right₀ _ strip_odd_denominator_ne_zero

theorem strip_halfUnit_sub_deck_ne_zero (n : ℕ) :
    halfUnitFromRoot stripComponentXiRoot n -
      stripComponentDeck (halfUnitFromRoot stripComponentXiRoot n) ≠ 0 := by
  rw [strip_halfUnit_sub_deck]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) stripMappedI_ne_zero)
    ((map_ne_zero (algebraMap Marked stripQuadraticField)).mpr (betaMarked_ne_zero n)))
    (xiRoot_ne_zero stripComponentXiRoot_sq)

/-- Ratios of odd unit parts recover the actual relative prime exponential clocks. -/
theorem strip_odd_unit_ratio (n m : ℕ) :
    (halfUnitFromRoot stripComponentXiRoot n -
        stripComponentDeck (halfUnitFromRoot stripComponentXiRoot n)) /
      (halfUnitFromRoot stripComponentXiRoot m -
        stripComponentDeck (halfUnitFromRoot stripComponentXiRoot m)) =
    algebraMap Marked stripQuadraticField (betaMarked n / betaMarked m) := by
  rw [strip_halfUnit_sub_deck, strip_halfUnit_sub_deck, map_div₀]
  field_simp [stripMappedI_ne_zero, xiRoot_ne_zero stripComponentXiRoot_sq,
    (map_ne_zero (algebraMap Marked stripQuadraticField)).mpr (betaMarked_ne_zero m)]
  exact mul_div_cancel_left₀ _ stripMappedI_ne_zero

end RHTower.XiGlobalKummer
