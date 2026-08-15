import GaloisForLFunctions.RHTower.WallTailRayEstimates

/-!
# The inward ray by reflection

Three of the four tail terms need nothing new on the inward ray: the first boundary term is proved on
the whole line through an indicator, and the other two see only the weight `(1+|x|)^{-s}`, whose two
half-lines carry equal mass.  The remainder is different, because the weighted Hardy inequality is
genuinely one-sided — it compares a moving average `x^{-p}∫_1^x` with its density.

Reflection repairs exactly that: the squared mass of a profile on `(-∞,-Y)` is the squared mass of
its reflection on `(Y,∞)`, so a bound of Hardy shape at `-x` transfers verbatim.  Nothing about the
Gamma transport is reflected — only the integration variable — which is why the estimate applies even
though the propagator itself has no symmetry.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {A : Type*} [NormedAddCommGroup A]

/-- Reflection identifies the two outward rays. -/
theorem lintegral_sq_Iio_neg_eq {f : ℝ → A} (Y : ℝ) :
    (∫⁻ x in Iio (-Y), ‖f x‖ₑ ^ 2) = ∫⁻ x in Ioi Y, ‖f (-x)‖ₑ ^ 2 := by
  have hswap : ∀ x : ℝ, (Iio (-Y)).indicator (fun y : ℝ => ‖f y‖ₑ ^ 2) (-x)
      = (Ioi Y).indicator (fun y : ℝ => ‖f (-y)‖ₑ ^ 2) x := by
    intro x
    by_cases hx : Y < x
    · rw [Set.indicator_of_mem (by simp only [mem_Iio]; linarith),
        Set.indicator_of_mem (by simpa using hx)]
    · rw [not_lt] at hx
      rw [Set.indicator_of_notMem (by simp only [mem_Iio, not_lt]; linarith),
        Set.indicator_of_notMem (by simp only [mem_Ioi, not_lt]; exact hx)]
  calc (∫⁻ x in Iio (-Y), ‖f x‖ₑ ^ 2)
      = ∫⁻ x : ℝ, (Iio (-Y)).indicator (fun y : ℝ => ‖f y‖ₑ ^ 2) x :=
        (lintegral_indicator measurableSet_Iio _).symm
    _ = ∫⁻ x : ℝ, (Iio (-Y)).indicator (fun y : ℝ => ‖f y‖ₑ ^ 2) (-x) :=
        (lintegral_neg_eq_self _).symm
    _ = ∫⁻ x : ℝ, (Ioi Y).indicator (fun y : ℝ => ‖f (-y)‖ₑ ^ 2) x := lintegral_congr hswap
    _ = ∫⁻ x in Ioi Y, ‖f (-x)‖ₑ ^ 2 := lintegral_indicator measurableSet_Ioi _

/-- **The scalar Hardy transfer on the inward ray**, by reflection. -/
theorem lintegral_sq_negRay_le_of_hardyBound_scalar {p Y : ℝ} (hp : 1 / 2 < p) (hY : 1 ≤ Y)
    {f : ℝ → A} {H : ℝ → ℝ≥0∞} {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x ∈ Iio (-Y), ‖f x‖ₑ ≤ ENNReal.ofReal (K * (-x) ^ (-p))
      * ∫⁻ t in Ioc (1 : ℝ) (-x), ENNReal.ofReal (t ^ (p - 1)) * H t)
    (hmeas : AEMeasurable H (volume.restrict (Ioi (1 : ℝ)))) :
    (∫⁻ x in Iio (-Y), ‖f x‖ₑ ^ 2)
      ≤ ENNReal.ofReal (K ^ 2)
        * (ENNReal.ofReal ((p - 1 / 2)⁻¹ ^ 2) * ∫⁻ t in Ioi (1 : ℝ), H t ^ 2) := by
  rw [lintegral_sq_Iio_neg_eq]
  refine lintegral_sq_ray_le_of_hardyBound_scalar hp hY hK ?_ hmeas
  intro x hx
  have hxneg : -x ∈ Iio (-Y) := by
    simp only [mem_Iio]
    have : Y < x := hx
    linarith
  have h := hbound (-x) hxneg
  rwa [neg_neg] at h

end GaloisForLFunctions.RHTower
