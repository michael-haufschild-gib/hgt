import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Cauchy–Schwarz for a weighted integral

A product of two factors integrated against a nonnegative weight is bounded by the two weighted mean
squares:

`‖∫ g₁ g₂ W‖ ≤ (∫ ‖g₁‖²‖W‖)^{1/2} (∫ ‖g₂‖²‖W‖)^{1/2}`.

Splitting the weight symmetrically, `‖g₁ g₂ W‖ = (‖g₁‖√‖W‖)(‖g₂‖√‖W‖)`, reduces this to Hölder's
inequality with conjugate exponents `2, 2`.  This is the device that turns a vertical-line integral of a
product of Dirichlet series into two mean squares, one of which can be estimated pointwise and the other
by a mean-value theorem.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory

/-- **Cauchy–Schwarz for a weighted vertical integral.**  A product of two factors against a weight is
bounded by the two weighted mean squares. -/
theorem norm_integral_mul_mul_le_sqrt_mul_sqrt {g₁ g₂ W : ℝ → ℂ}
    (hm1 : AEStronglyMeasurable g₁ volume) (hm2 : AEStronglyMeasurable g₂ volume)
    (hmW : AEStronglyMeasurable W volume)
    (h1 : Integrable fun y => ‖g₁ y‖ ^ 2 * ‖W y‖)
    (h2 : Integrable fun y => ‖g₂ y‖ ^ 2 * ‖W y‖) :
    ‖∫ y : ℝ, g₁ y * g₂ y * W y‖
      ≤ Real.sqrt (∫ y : ℝ, ‖g₁ y‖ ^ 2 * ‖W y‖)
          * Real.sqrt (∫ y : ℝ, ‖g₂ y‖ ^ 2 * ‖W y‖) := by
  set F : ℝ → ℝ := fun y => ‖g₁ y‖ * Real.sqrt ‖W y‖ with hF
  set G : ℝ → ℝ := fun y => ‖g₂ y‖ * Real.sqrt ‖W y‖ with hG
  have hFsq : ∀ y : ℝ, F y ^ 2 = ‖g₁ y‖ ^ 2 * ‖W y‖ := by
    intro y
    rw [hF]
    have hsq : Real.sqrt ‖W y‖ ^ 2 = ‖W y‖ := Real.sq_sqrt (norm_nonneg _)
    calc (‖g₁ y‖ * Real.sqrt ‖W y‖) ^ 2 = ‖g₁ y‖ ^ 2 * (Real.sqrt ‖W y‖) ^ 2 := by ring
      _ = ‖g₁ y‖ ^ 2 * ‖W y‖ := by rw [hsq]
  have hGsq : ∀ y : ℝ, G y ^ 2 = ‖g₂ y‖ ^ 2 * ‖W y‖ := by
    intro y
    rw [hG]
    have hsq : Real.sqrt ‖W y‖ ^ 2 = ‖W y‖ := Real.sq_sqrt (norm_nonneg _)
    calc (‖g₂ y‖ * Real.sqrt ‖W y‖) ^ 2 = ‖g₂ y‖ ^ 2 * (Real.sqrt ‖W y‖) ^ 2 := by ring
      _ = ‖g₂ y‖ ^ 2 * ‖W y‖ := by rw [hsq]
  have hFm : AEStronglyMeasurable F volume := by
    refine (hm1.norm).mul ?_
    exact (Real.continuous_sqrt.comp_aestronglyMeasurable hmW.norm)
  have hGm : AEStronglyMeasurable G volume := by
    refine (hm2.norm).mul ?_
    exact (Real.continuous_sqrt.comp_aestronglyMeasurable hmW.norm)
  have hFint : Integrable fun y => ‖F y‖ ^ 2 := by
    refine h1.congr (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [Real.norm_eq_abs, sq_abs, hFsq]
  have hGint : Integrable fun y => ‖G y‖ ^ 2 := by
    refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [Real.norm_eq_abs, sq_abs, hGsq]
  have hFLp : MemLp F 2 volume := (memLp_two_iff_integrable_sq_norm hFm).mpr hFint
  have hGLp : MemLp G 2 volume := (memLp_two_iff_integrable_sq_norm hGm).mpr hGint
  have hFnn : 0 ≤ᵐ[volume] F := Filter.Eventually.of_forall fun y => by
    rw [hF]; positivity
  have hGnn : 0 ≤ᵐ[volume] G := Filter.Eventually.of_forall fun y => by
    rw [hG]; positivity
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two hFnn hGnn
    (by simpa using hFLp) (by simpa using hGLp)
  have hpt : ∀ y : ℝ, ‖g₁ y * g₂ y * W y‖ = F y * G y := by
    intro y
    rw [hF, hG, norm_mul, norm_mul]
    have hsq : Real.sqrt ‖W y‖ * Real.sqrt ‖W y‖ = ‖W y‖ := Real.mul_self_sqrt (norm_nonneg _)
    calc ‖g₁ y‖ * ‖g₂ y‖ * ‖W y‖
        = ‖g₁ y‖ * ‖g₂ y‖ * (Real.sqrt ‖W y‖ * Real.sqrt ‖W y‖) := by rw [hsq]
      _ = ‖g₁ y‖ * Real.sqrt ‖W y‖ * (‖g₂ y‖ * Real.sqrt ‖W y‖) := by ring
  have hnorm : ‖∫ y : ℝ, g₁ y * g₂ y * W y‖ ≤ ∫ y : ℝ, F y * G y := by
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  refine le_trans hnorm (le_trans hcs (le_of_eq ?_))
  have hFpow : (∫ y : ℝ, F y ^ (2:ℝ)) = ∫ y : ℝ, ‖g₁ y‖ ^ 2 * ‖W y‖ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [Real.rpow_two, hFsq]
  have hGpow : (∫ y : ℝ, G y ^ (2:ℝ)) = ∫ y : ℝ, ‖g₂ y‖ ^ 2 * ‖W y‖ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [Real.rpow_two, hGsq]
  rw [hFpow, hGpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

end GaloisForLFunctions.HTGeometry
end
