import GaloisForLFunctions.HTGeometry.L2NegativeHalfLineExtension
import GaloisForLFunctions.HTGeometry.L2DerivativeFourier

/-! Contractive restriction to the original negative-ray Hilbert space. -/
open MeasureTheory Set Filter
namespace GaloisForLFunctions.HTGeometry
open RHTower
noncomputable section

private def negativeRestrictionLinear : FourierRealL2 →ₗ[ℂ] NegativeLineL2 where
  toFun := restrictLp (Iio 0)
  map_add' := restrictLp_add (Iio 0)
  map_smul' c f := by
    apply Lp.ext
    have hs := (Lp.coeFn_smul c f).filter_mono
      (ae_mono (show volume.restrict (Iio (0:ℝ)) ≤ volume from Measure.restrict_le_self))
    filter_upwards [coeFn_restrictLp (Iio 0) (c • f),coeFn_restrictLp (Iio 0) f,
      Lp.coeFn_smul c (restrictLp (Iio 0) f),hs] with t ho hf hs h₀
    change restrictLp (Iio 0) (c • f) t = (c • restrictLp (Iio 0) f) t
    rw [ho,hs,h₀]
    simp only [Pi.smul_apply,hf]

def negativeRestriction : FourierRealL2 →L[ℂ] NegativeLineL2 :=
  negativeRestrictionLinear.mkContinuous 1 (by
    intro f
    change ‖restrictLp (Iio 0) f‖ ≤ 1*‖f‖
    simpa using norm_restrictLp_le (Iio 0) f)

theorem negativeRestriction_ae (f : FourierRealL2) :
    negativeRestriction f =ᵐ[volume.restrict (Iio (0:ℝ))] f := coeFn_restrictLp _ f

theorem negativeRestriction_norm_le (f : FourierRealL2) : ‖negativeRestriction f‖ ≤ ‖f‖ :=
  norm_restrictLp_le (Iio 0) f

/-- Restriction of the source-faithful odd extension is exactly the original Hilbert vector. -/
theorem negativeRestriction_oddExtension (f : NegativeLineL2) :
    negativeRestriction (negativeOddExtension f) = f := by
  apply Lp.ext
  exact (negativeRestriction_ae _).trans (negativeOddExtension_ae_negative f)

end
end GaloisForLFunctions.HTGeometry
