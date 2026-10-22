import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEvenFourMiddle
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEvenCompensationCoefficient
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspMiddleCompensationBounds

/-!
# Canonical even rank-four source on the lower middle interval

The fixed-coefficient rank-four reserve is already strict at coefficient `10^12`.
On the lower middle interval the literal center correction is positive, so the
larger source-selected canonical coefficient preserves that reserve.  This is
the actual complete theta source, not a fitted scalar or a model determinant.
-/

namespace RHTower
noncomputable section

/-- The literal canonical coefficient retains complete rank-four positivity
through the entire positive-correction lower middle interval. -/
theorem thetaCuspNativeEvenFourCanonical_posDef_lower_middle {x : ℝ}
    (hq0 : 37 / 10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hq1 : thetaCuspSingleAtomReflectionScale 1 x ≤ 5) :
    (thetaCuspNativeEvenFourCompensated
      thetaCuspNativeEvenCompensationCoefficient x).PosDef := by
  have hx : 0 ≤ x := (thetaCusp_pos_of_thirtySevenTenths_le hq0).le
  have hfixed := thetaCuspNativeEvenFourFixed_posDef_inner hq0 hq1
  have hcorrection : 0 ≤ thetaCuspCenterCompensationSource x :=
    (thetaCuspCenterCompensationSource_pos_on_scale_five hq0 hq1).le
  have hcoefficient : (1000000000000 : ℝ) ≤
      thetaCuspNativeEvenCompensationCoefficient :=
    thetaCuspNativeEvenCompensationCoefficient_bounds.1.le
  rw [thetaCuspNativeEvenFourCompensated_posDef_iff hx] at hfixed ⊢
  have hmul := mul_le_mul_of_nonneg_right hcoefficient hcorrection
  linarith

end
end RHTower
