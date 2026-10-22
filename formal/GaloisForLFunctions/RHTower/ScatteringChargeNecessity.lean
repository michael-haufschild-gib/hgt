import GaloisForLFunctions.RHTower.Suzuki.SuzukiRootRetainedJumpSource

/-!
# A non-square-integrable term is not repaired by a square-integrable one

If a profile has infinite squared mass and another has finite squared mass, their sum still has
infinite squared mass — subtracting the finite part would otherwise make the infinite one finite.

This is the necessity half of a scattering-charge criterion: once the leading asymptotic term of a
solution is known to be non-square-integrable unless its coefficient vanishes, and every remaining
term is square integrable, the whole solution is square integrable only when that coefficient is
zero.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {Y : Type*} [NormedAddCommGroup Y]

/-- **A finite tail cannot repair an infinite head.** -/
theorem lintegral_sq_add_eq_top {u w : ℝ → Y} {s : Set ℝ}
    (hum : AEStronglyMeasurable u (volume.restrict s))
    (hwm : AEStronglyMeasurable w (volume.restrict s))
    (hu : (∫⁻ L in s, ‖u L‖ₑ ^ 2) = ⊤) (hw : (∫⁻ L in s, ‖w L‖ₑ ^ 2) ≠ ⊤) :
    (∫⁻ L in s, ‖u L + w L‖ₑ ^ 2) = ⊤ := by
  by_contra hcon
  have hsum : (∫⁻ L in s, ‖(u L + w L) + (-w L)‖ₑ ^ 2) ≠ ⊤ := by
    refine lintegral_sq_add_ne_top (u := fun L => u L + w L) (w := fun L => -w L) ?_ hcon ?_
    · exact hum.add hwm
    · simpa using hw
  have hcongr : (∫⁻ L in s, ‖(u L + w L) + (-w L)‖ₑ ^ 2) = ∫⁻ L in s, ‖u L‖ₑ ^ 2 := by
    refine lintegral_congr fun L => ?_
    congr 2
    abel
  rw [hcongr, hu] at hsum
  exact hsum rfl

/-- **The charge criterion, necessity half.**  If the leading term is square integrable only when
its coefficient vanishes, and the remainder is square integrable, then so is the whole profile only
when the coefficient vanishes. -/
theorem charge_eq_zero_of_lintegral_sq_ne_top {lead rem : ℝ → Y} {s : Set ℝ}
    (hlm : AEStronglyMeasurable lead (volume.restrict s))
    (hrm : AEStronglyMeasurable rem (volume.restrict s))
    (hrem : (∫⁻ L in s, ‖rem L‖ₑ ^ 2) ≠ ⊤)
    (htotal : (∫⁻ L in s, ‖lead L + rem L‖ₑ ^ 2) ≠ ⊤) :
    (∫⁻ L in s, ‖lead L‖ₑ ^ 2) ≠ ⊤ := by
  intro hlead
  exact htotal (lintegral_sq_add_eq_top hlm hrm hlead hrem)

end GaloisForLFunctions.RHTower
