/-
# Exact energy of complex `L²` pairing functionals

The bilinear complex pairing `v ↦ ∫ u v` is the Riesz functional represented by `star u`.
Consequently its operator norm is exactly `‖u‖`, not merely bounded by Hölder.  This is the
coordinate-free identity behind the time--band localization area law and is independent of any
zeta-specific structure.
-/
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HTGeometry

/-- The square of an `L²` norm is the integral of the pointwise squared norm. -/
theorem norm_l2_sq_eq_integral_norm_sq {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] (mu : Measure X) (f : Lp E 2 mu) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂mu := by
  rw [Lp.norm_def, toReal_eLpNorm (Lp.aestronglyMeasurable f),
    lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ENNReal)) (by norm_num) (by norm_num)
      (Lp.aestronglyMeasurable f)]
  norm_num [← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt]
  exact integral_nonneg fun x => sq_nonneg _

/-- Pointwise complex multiplication, bundled as a continuous bilinear map. -/
def complexMulBilinear : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.lsmul ℂ ℂ

/-- The bilinear `L²` pairing with `u` is exactly the Riesz functional represented by `star u`.
This makes the norm identity structural rather than an estimate. -/
theorem complexMulBilinear_lpPairing_eq_toDual_star {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (u : Lp ℂ 2 mu) :
    complexMulBilinear.lpPairing mu 2 2 u =
      InnerProductSpace.toDual ℂ (Lp ℂ 2 mu) (star u) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.lpPairing_eq_integral,
    InnerProductSpace.toDual_apply_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star u] with x hx
  rw [hx]
  simp [complexMulBilinear, RCLike.inner_apply, mul_comm]

/-- Exact norm of the complex bilinear `L²` pairing functional. -/
theorem norm_complexMulBilinear_lpPairing {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (u : Lp ℂ 2 mu) :
    ‖complexMulBilinear.lpPairing mu 2 2 u‖ = ‖u‖ := by
  rw [complexMulBilinear_lpPairing_eq_toDual_star,
    (InnerProductSpace.toDual ℂ (Lp ℂ 2 mu)).norm_map]
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (Lp.coeFn_star u), eLpNorm_star]

end HTGeometry
