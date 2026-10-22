import GaloisForLFunctions.ScaleSignedIncidenceCriticality.ThePrimeWindowLadderConverges

/-!
# The prime face's interval, and the certificate's inherited floor

The prime window has an exact limit in the defect-scale unit, `1/m₀(R)`
(`ThePrimeWindowLadderConverges`). This module gives its two-sided form and transports the result
from the window data to the object a mechanism actually produces — the radius-`R` certificate.

* `resolutionFloor_weightDefectScale_windowReading` — the floor is `0`, because the arithmetic weight
  itself lies in every window shadow. So the window reading, like the level reading, confirms and
  does not refute.
* `resolutionInterval_weightDefectScale_windowReading` — hence the interval is
  `[0, 1/m₀(R)]`, proper for every radius: the window reading is informative in its own unit, as the
  truncated divisor is in the horizon unit (`TheHorizonSeamIsEmptyToo`).
* `refines_windowReading_radiusReading` and `le_resolutionLimit_radiusReading` — the radius
  certificate is a function of the window
  (`SquareRootThreshold.radiusReading_congr_of_agree_below`), hence coarser, hence its limit is at
  least `1/m₀(R)`. **The certificate inherits the floor of the data it is computed from**, which is
  the usable form: no post-processing of a radius-`R` certificate certifies a defect scale below
  `1/m₀(R)`.

`thePrimeFaceInterval` collects the three. With `TheTwoByTwoTableOfUnits` the field's table now has a
third row, and it has the same shape as the first two: vacuous in the criterion's own unit, sharp in
the unit built from the reading's parameter.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The floor of the window reading -/

theorem bddBelow_weightDefectScale_image (s : Set (ℕ → ℝ)) :
    BddBelow (weightDefectScale '' s) :=
  ⟨0, by rintro x ⟨lam, -, rfl⟩; exact weightDefectScale_nonneg lam⟩

/-- **The window reading never forces a positive defect.** -/
theorem resolutionFloor_weightDefectScale_windowReading (R : ℝ) :
    resolutionFloor weightDefectScale (windowReading R)
      (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) = 0 := by
  refine le_antisymm ?_
    ((certifiesLower_iff_le_resolutionFloor (bddBelow_weightDefectScale_image _)).mp
      fun lam _ => weightDefectScale_nonneg lam)
  have hzero : weightDefectScale (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) = 0 :=
    (weightDefectScale_eq_zero_iff _).mpr fun _ _ => rfl
  have hle := resolutionFloor_le (I := weightDefectScale) (r := windowReading R)
    (d := fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
    (bddBelow_weightDefectScale_image _)
  rwa [hzero] at hle

/-- **The interval of the window reading.** -/
theorem resolutionInterval_weightDefectScale_windowReading (R : ℝ) :
    resolutionInterval weightDefectScale (windowReading R)
        (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) =
      Icc 0 (((leastOutsideWindow R : ℝ))⁻¹) := by
  rw [resolutionInterval, resolutionFloor_weightDefectScale_windowReading,
    resolutionLimit_weightDefectScale_windowReading]

/-! ### 2. The certificate inherits the floor -/

/-- The radius certificate is a function of the window data. -/
theorem refines_windowReading_radiusReading (R : ℝ) :
    Refines (windowReading R) (radiusReading R) := by
  intro lam lam' hmem
  have hagree : ∀ n : ℕ, 2 ≤ n → Real.log n < 2 * R → lam' n = lam n := by
    intro n hn hlog
    exact congrFun (mem_shadow_iff.mp hmem) ⟨n, hn, hlog⟩
  exact radiusReading_congr_of_agree_below hagree

/-- **The certificate inherits the floor of its window.** -/
theorem le_resolutionLimit_radiusReading (R : ℝ) :
    ((leastOutsideWindow R : ℝ))⁻¹ ≤
      resolutionLimit weightDefectScale (radiusReading R)
        (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) := by
  have hbdd : BddAbove (weightDefectScale '' shadow (radiusReading R)
      (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))) :=
    ⟨1 / 2, by rintro x ⟨lam, -, rfl⟩; exact weightDefectScale_le_half lam⟩
  have hmono := resolutionLimit_le_of_refines (I := weightDefectScale)
    (refines_windowReading_radiusReading R)
    (d := fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) hbdd
  rw [resolutionLimit_weightDefectScale_windowReading] at hmono
  exact hmono

/-! ### 3. The prime face's row -/

/-- **The prime face's row of the table.** Floor `0`, limit `1/m₀(R)`, and the certificate computed
from the window inherits that limit as a lower bound. -/
theorem thePrimeFaceInterval (R : ℝ) :
    resolutionFloor weightDefectScale (windowReading R)
        (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) = 0 ∧
      resolutionInterval weightDefectScale (windowReading R)
          (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) =
        Icc 0 (((leastOutsideWindow R : ℝ))⁻¹) ∧
      ((leastOutsideWindow R : ℝ))⁻¹ ≤
        resolutionLimit weightDefectScale (radiusReading R)
          (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) :=
  ⟨resolutionFloor_weightDefectScale_windowReading R,
    resolutionInterval_weightDefectScale_windowReading R,
    le_resolutionLimit_radiusReading R⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
