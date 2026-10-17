import GaloisForLFunctions.BiScaleUncertainty.NyquistWeightTailMass
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! # The positive bounded residual operator with its exact norm -/

open Set Filter Topology MeasureTheory
open scoped BoundedContinuousFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

theorem locallyIntegrable_nyquistWeightKernel {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ) :
    LocallyIntegrable (nyquistWeightKernel β m N) := by
  apply (contDiff_nyquistWeight β 1).continuous.locallyIntegrable.mono
    (measurable_nyquistWeightKernel β m N).aestronglyMeasurable
  filter_upwards with x
  have hw : 0 ≤ nyquistWeight β x := (Real.cosh_pos _).le
  simpa only [Real.norm_eq_abs, abs_of_nonneg hw,
    abs_of_nonneg (nyquistWeightKernel_nonneg hβ m N x)] using
    nyquistWeightKernel_le_weight hβ m N x

theorem lintegral_nyquistWeightKernel_eq_top {β : ℝ} (hβ : 0 < β) (m N : ℕ)
    (hcrit : (m : ℝ) + 1 ≤ β) :
    (∫⁻ x, ENNReal.ofReal (nyquistWeightKernel β m N x)) = ⊤ := by
  by_contra hfinite
  have hi := (lintegral_ofReal_ne_top_iff_integrable
    (measurable_nyquistWeightKernel β m N).aestronglyMeasurable
    (Eventually.of_forall fun x => nyquistWeightKernel_nonneg hβ.le m N x)).mp hfinite
  exact (not_lt_of_ge hcrit) ((integrable_nyquistWeightKernel_iff hβ m N).mp hi)

theorem integrable_mul_nyquistWeightKernel {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ)
    (hlt : β < (m : ℝ) + 1) (H : ℝ →ᵇ ℝ) :
    Integrable (fun x => H x * nyquistWeightKernel β m N x) :=
  ((integrable_nyquistWeightKernel_iff_nonneg hβ m N).mpr hlt).bdd_mul
    H.continuous.aestronglyMeasurable (Eventually.of_forall fun x => H.norm_coe_le_norm x)

theorem integral_mul_nyquistWeightKernel_le {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ)
    (hlt : β < (m : ℝ) + 1) (H : ℝ →ᵇ ℝ) :
    ‖∫ x, H x * nyquistWeightKernel β m N x‖ ≤ nyquistWeightTailMass β m N * ‖H‖ := by
  calc
    _ ≤ ∫ x, ‖H‖ * nyquistWeightKernel β m N x :=
      norm_integral_le_of_norm_le
        (((integrable_nyquistWeightKernel_iff_nonneg hβ m N).mpr hlt).const_mul ‖H‖)
        (Eventually.of_forall fun x => by
          simp only [norm_mul, Real.norm_eq_abs,
            abs_of_nonneg (nyquistWeightKernel_nonneg hβ m N x)]
          exact mul_le_mul_of_nonneg_right (H.norm_coe_le_norm x)
            (nyquistWeightKernel_nonneg hβ m N x))
    _ = _ := by rw [integral_const_mul, integral_nyquistWeightKernel hβ m N hlt, mul_comm]

def nyquistWeightOperator {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ)
    (hlt : β < (m : ℝ) + 1) : (ℝ →ᵇ ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun H => ∫ x, H x * nyquistWeightKernel β m N x
      map_add' := by
        intro H G
        change (∫ x, (H x + G x) * nyquistWeightKernel β m N x) = _
        simp_rw [add_mul]
        exact integral_add (integrable_mul_nyquistWeightKernel hβ m N hlt H)
          (integrable_mul_nyquistWeightKernel hβ m N hlt G)
      map_smul' := by
        intro c H
        change (∫ x, (c * H x) * nyquistWeightKernel β m N x) =
          c * ∫ x, H x * nyquistWeightKernel β m N x
        simp_rw [mul_assoc]
        exact integral_const_mul _ _ }
    (nyquistWeightTailMass β m N) (integral_mul_nyquistWeightKernel_le hβ m N hlt)

theorem nyquistWeightOperator_apply {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ)
    (hlt : β < (m : ℝ) + 1) (H : ℝ →ᵇ ℝ) :
    nyquistWeightOperator hβ m N hlt H = ∫ x, H x * nyquistWeightKernel β m N x := rfl

theorem nyquistWeightOperator_nonneg {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ)
    (hlt : β < (m : ℝ) + 1) (H : ℝ →ᵇ ℝ) (hH : ∀ x, 0 ≤ H x) :
    0 ≤ nyquistWeightOperator hβ m N hlt H :=
  integral_nonneg (fun x => mul_nonneg (hH x) (nyquistWeightKernel_nonneg hβ m N x))

theorem nyquistWeightOperator_const_one {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ)
    (hlt : β < (m : ℝ) + 1) :
    nyquistWeightOperator hβ m N hlt (BoundedContinuousFunction.const ℝ (1 : ℝ)) =
      nyquistWeightTailMass β m N := by
  simp only [nyquistWeightOperator_apply, BoundedContinuousFunction.const_apply, one_mul,
    integral_nyquistWeightKernel hβ m N hlt]

theorem norm_nyquistWeightOperator {β : ℝ} (hβ : 0 ≤ β) (m N : ℕ)
    (hlt : β < (m : ℝ) + 1) :
    ‖nyquistWeightOperator hβ m N hlt‖ = nyquistWeightTailMass β m N := by
  apply le_antisymm
  · exact (nyquistWeightOperator hβ m N hlt).opNorm_le_bound
      (nyquistWeightTailMass_nonneg hβ m N) (integral_mul_nyquistWeightKernel_le hβ m N hlt)
  · have hh := (nyquistWeightOperator hβ m N hlt).unit_le_opNorm
      (x := BoundedContinuousFunction.const ℝ (1 : ℝ))
      (by simp only [BoundedContinuousFunction.norm_const_eq, norm_one, le_refl])
    simpa only [nyquistWeightOperator_const_one, Real.norm_eq_abs,
      abs_of_nonneg (nyquistWeightTailMass_nonneg hβ m N)] using hh

theorem norm_nyquistWeightOperator_le {β : ℝ} (hβ : 0 < β) (m N : ℕ)
    (hlt : β < (m : ℝ) + 1) :
    ‖nyquistWeightOperator hβ.le m N hlt‖ ≤ nyquistWeightTailBound β m N := by
  rw [norm_nyquistWeightOperator]
  exact nyquistWeightTailMass_le hβ m N hlt

theorem tendsto_norm_nyquistWeightOperator {β : ℝ} (hβ : 0 < β) (m : ℕ)
    (hlt : β < (m : ℝ) + 1) :
    Tendsto (fun N => ‖nyquistWeightOperator hβ.le m N hlt‖) atTop (𝓝 0) := by
  simpa only [norm_nyquistWeightOperator] using tendsto_nyquistWeightTailMass hβ m hlt

theorem tendsto_norm_nyquistWeightOperator_normalized {β : ℝ} (hβ : 0 < β) (m : ℕ)
    (hlt : β < (m : ℝ) + 1) :
    Tendsto (fun N => ‖nyquistWeightOperator hβ.le m N hlt‖ /
      ((N + 1 : ℕ) : ℝ) ^ (β - ((m : ℝ) + 1))) atTop
      (𝓝 (nyquistWeightCellConstant β m / ((m : ℝ) + 1 - β))) := by
  simpa only [norm_nyquistWeightOperator] using tendsto_nyquistWeightTailMass_normalized hβ m hlt

end
end GaloisForLFunctions.BiScaleUncertainty
