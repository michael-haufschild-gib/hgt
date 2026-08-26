import GaloisForLFunctions.HTGeometry.HardyProductArcGluing
import GaloisForLFunctions.HTGeometry.AnalyticSlopeFactor
import GaloisForLFunctions.HTGeometry.CircleSingularWitness

open Complex Filter MeasureTheory Metric Set Topology Finset
open scoped ENNReal NNReal lp

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem aestronglyMeasurable_circle_analyticSlope
    (L : ℂ → ℂ) (hL : Measurable L) (z : ℂ) :
    AEStronglyMeasurable
      (fun ζ : Circle => analyticSlope L (ζ : ℂ) z) circleLebesgue := by
  have hcoe : AEStronglyMeasurable (fun ζ : Circle => (ζ : ℂ))
      circleLebesgue := by fun_prop
  have hLcoe : AEStronglyMeasurable (fun ζ : Circle => L (ζ : ℂ))
      circleLebesgue := by
    change AEStronglyMeasurable (L ∘ fun ζ : Circle => (ζ : ℂ)) circleLebesgue
    exact (hL.comp_aemeasurable hcoe.aemeasurable).aestronglyMeasurable
  have hconstL : AEStronglyMeasurable (fun _ : Circle => L z)
      circleLebesgue := aestronglyMeasurable_const
  have hconstZ : AEStronglyMeasurable (fun _ : Circle => z)
      circleLebesgue := aestronglyMeasurable_const
  have hnum := hconstL.sub hLcoe
  have hden := hconstZ.sub hcoe
  have hraw : AEStronglyMeasurable
      (fun ζ : Circle => (L z - L (ζ : ℂ)) / (z - (ζ : ℂ)))
      circleLebesgue := by
    have hfun :
        (fun ζ : Circle => (L z - L (ζ : ℂ)) / (z - (ζ : ℂ))) =
          ((fun _ : Circle => L z) - fun ζ : Circle => L (ζ : ℂ)) *
            ((fun _ : Circle => z) - fun ζ : Circle => (ζ : ℂ))⁻¹ := by
      funext ζ
      rfl
    rw [hfun]
    exact hnum.mul hden.inv₀
  apply hraw.congr
  by_cases hz : ∃ ζ₀ : Circle, (ζ₀ : ℂ) = z
  · obtain ⟨ζ₀, hζ₀⟩ := hz
    have hneq : ∀ᵐ ζ : Circle ∂circleLebesgue, ζ ≠ ζ₀ := by
      rw [ae_iff]
      simpa using circleLebesgue_singleton ζ₀
    filter_upwards [hneq] with ζ hζ
    have hne : z ≠ (ζ : ℂ) := by
      intro heq
      apply hζ
      exact Subtype.ext (heq.symm.trans hζ₀.symm)
    rw [analyticSlope_of_ne hne]
  · filter_upwards with ζ
    have hne : z ≠ (ζ : ℂ) := by
      intro heq
      exact hz ⟨ζ, heq.symm⟩
    rw [analyticSlope_of_ne hne]

def hardyProductCauchyCommutator
    (u v : HardyDisk) (a : Circle → ℂ) (L : ℂ → ℂ)
    (z₀ : ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  ∫ ζ : Circle,
    if dist (ζ : ℂ) z₀ < 2 * r then
      -((hardyDiskBoundary u : Circle → ℂ) ζ *
        (hardyDiskBoundary v : Circle → ℂ) ζ * (ζ : ℂ) *
          analyticSlope L (ζ : ℂ) z)
    else
      (hardyDiskBoundary u : Circle → ℂ) ζ *
        (hardyDiskBoundary v : Circle → ℂ) ζ * (ζ : ℂ) *
          (L z - a ζ) / ((ζ : ℂ) - z)
    ∂circleLebesgue

theorem differentiableAt_hardyProductCauchyCommutator_of_mem_ball
    (u v : HardyDisk) (a : Circle → ℂ) (L : ℂ → ℂ)
    (z₀ : ℂ) {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (haMeas : Measurable a) (haUnit : ∀ ζ, ‖a ζ‖ = 1)
    (hLanalytic : ∀ w ∈ closedBall z₀ (3 * r), AnalyticAt ℂ L w)
    (hLlip : ∀ x ∈ closedBall z₀ (3 * r), ∀ y ∈ closedBall z₀ (3 * r),
      ‖L y - L x‖ ≤ C * ‖y - x‖)
    (hLderiv : ∀ w ∈ closedBall z₀ (3 * r), ‖deriv L w‖ ≤ C)
    (hslopeMeas : ∀ z ∈ ball z₀ r,
      AEStronglyMeasurable
        (fun ζ : Circle => analyticSlope L (ζ : ℂ) z) circleLebesgue) :
    ∀ z ∈ ball z₀ r,
      DifferentiableAt ℂ (hardyProductCauchyCommutator u v a L z₀ r) z := by
  let q : Circle → ℂ := fun ζ =>
    (hardyDiskBoundary u : Circle → ℂ) ζ *
      (hardyDiskBoundary v : Circle → ℂ) ζ
  let F : ℂ → Circle → ℂ := fun z ζ =>
    if dist (ζ : ℂ) z₀ < 2 * r then
      -(q ζ * (ζ : ℂ) * analyticSlope L (ζ : ℂ) z)
    else q ζ * (ζ : ℂ) * (L z - a ζ) / ((ζ : ℂ) - z)
  let B : ℝ := max C ((C * r + ‖L z₀‖ + 1) / r)
  let bound : Circle → ℝ := fun ζ => B * ‖q ζ‖
  have hq : Integrable q circleLebesgue := by
    exact (Lp.memLp (hardyDiskBoundary u)).integrable_mul
      (Lp.memLp (hardyDiskBoundary v))
  have hB : 0 ≤ B := le_trans hC (le_max_left _ _)
  have hmeas : ∀ z ∈ ball z₀ r,
      AEStronglyMeasurable (F z) circleLebesgue := by
    intro z hz
    have hcoe : AEStronglyMeasurable (fun ζ : Circle => (ζ : ℂ))
        circleLebesgue := by fun_prop
    have hnear : AEStronglyMeasurable
        (fun ζ : Circle => -(q ζ * (ζ : ℂ) * analyticSlope L (ζ : ℂ) z))
        circleLebesgue := by
      exact (hq.aestronglyMeasurable.mul hcoe).mul
          (hslopeMeas z hz) |>.neg
    have hfar : AEStronglyMeasurable
        (fun ζ : Circle => q ζ * (ζ : ℂ) *
          (L z - a ζ) / ((ζ : ℂ) - z)) circleLebesgue := by
      have hkernel : AEStronglyMeasurable
          (fun ζ : Circle => (ζ : ℂ) * (L z - a ζ) / ((ζ : ℂ) - z))
          circleLebesgue := by
        have hconstL : AEStronglyMeasurable (fun _ : Circle => L z)
            circleLebesgue := aestronglyMeasurable_const
        have hconstZ : AEStronglyMeasurable (fun _ : Circle => z)
            circleLebesgue := aestronglyMeasurable_const
        have hnum := hcoe.mul (hconstL.sub haMeas.aestronglyMeasurable)
        have hden := hcoe.sub hconstZ
        have hfun :
            (fun ζ : Circle => (ζ : ℂ) * (L z - a ζ) / ((ζ : ℂ) - z)) =
              ((fun ζ : Circle => (ζ : ℂ)) * ((fun _ : Circle => L z) - a)) *
                ((fun ζ : Circle => (ζ : ℂ)) - (fun _ : Circle => z))⁻¹ := by
          funext ζ
          rfl
        rw [hfun]
        exact hnum.mul hden.inv₀
      have hmul := hq.aestronglyMeasurable.mul hkernel
      rw [show (fun ζ : Circle => q ζ * (ζ : ℂ) *
          (L z - a ζ) / ((ζ : ℂ) - z)) =
          q * fun ζ : Circle => (ζ : ℂ) *
            (L z - a ζ) / ((ζ : ℂ) - z) by
        funext ζ
        simp only [Pi.mul_apply]
        ring]
      exact hmul
    have hset : MeasurableSet {ζ : Circle | dist (ζ : ℂ) z₀ < 2 * r} := by
      change @MeasurableSet Circle (borel Circle)
        {ζ : Circle | dist (ζ : ℂ) z₀ < 2 * r}
      letI : MeasurableSpace Circle := borel Circle
      rw [show {ζ : Circle | dist (ζ : ℂ) z₀ < 2 * r} =
          (fun ζ : Circle => (ζ : ℂ)) ⁻¹' ball z₀ (2 * r) by
        ext ζ
        simp [mem_ball]]
      exact @IsOpen.measurableSet Circle _ _ (borel Circle) ⟨le_rfl⟩
        (isOpen_ball.preimage continuous_subtype_val)
    have hsum := (hnear.indicator hset).add (hfar.indicator hset.compl)
    convert hsum using 1
    funext ζ
    by_cases hζ : dist (ζ : ℂ) z₀ < 2 * r <;>
      simp [F, Set.indicator, hζ]
  have hdiff : ∀ ζ : Circle,
      DifferentiableOn ℂ (fun z : ℂ => F z ζ) (ball z₀ r) := by
    intro ζ
    by_cases hnear : dist (ζ : ℂ) z₀ < 2 * r
    · simp only [F, if_pos hnear]
      intro z hz
      apply DifferentiableAt.differentiableWithinAt
      have hζmem : (ζ : ℂ) ∈ closedBall z₀ (3 * r) := by
        rw [mem_closedBall]
        linarith
      have hzmem : z ∈ closedBall z₀ (3 * r) := by
        rw [mem_closedBall]
        have := mem_ball.mp hz
        linarith
      have hslope : DifferentiableAt ℂ (analyticSlope L (ζ : ℂ)) z := by
        by_cases heq : z = (ζ : ℂ)
        · subst z
          exact (analyticAt_analyticSlope (hLanalytic _ hζmem)).differentiableAt
        · have hev : analyticSlope L (ζ : ℂ) =ᶠ[𝓝 z]
              fun w => (L w - L (ζ : ℂ)) / (w - (ζ : ℂ)) := by
            filter_upwards [isOpen_compl_singleton.mem_nhds heq] with w hw
            exact analyticSlope_of_ne hw
          apply (hev.differentiableAt_iff).2
          exact ((hLanalytic z hzmem).differentiableAt.sub_const _).div
            ((differentiableAt_id).sub_const _) (sub_ne_zero.mpr heq)
      have hprod := (differentiableAt_const (c := -(q ζ * (ζ : ℂ)))).mul hslope
      have heqfun :
          (fun w => -(q ζ * (ζ : ℂ)) * analyticSlope L (ζ : ℂ) w) =
            fun w => -(q ζ * (ζ : ℂ) * analyticSlope L (ζ : ℂ) w) := by
        funext w
        ring
      rw [← heqfun]
      exact hprod
    · simp only [F, if_neg hnear]
      intro z hz
      apply DifferentiableAt.differentiableWithinAt
      have hzmem : z ∈ closedBall z₀ (3 * r) := by
        rw [mem_closedBall]
        have := mem_ball.mp hz
        linarith
      have hden : (ζ : ℂ) - z ≠ 0 := by
        intro hzero
        have heq : (ζ : ℂ) = z := sub_eq_zero.mp hzero
        apply hnear
        rw [heq]
        have := mem_ball.mp hz
        linarith
      have hprod := (differentiableAt_const (c := q ζ * (ζ : ℂ))).mul
        (((hLanalytic z hzmem).differentiableAt.sub_const (a ζ)).div
          ((differentiableAt_const (c := (ζ : ℂ))).sub differentiableAt_id) hden)
      have heqfun :
          (fun w => (q ζ * (ζ : ℂ)) * ((L w - a ζ) / ((ζ : ℂ) - w))) =
            fun w => q ζ * (ζ : ℂ) * (L w - a ζ) / ((ζ : ℂ) - w) := by
        funext w
        ring
      rw [← heqfun]
      exact hprod
  have hbound : ∀ ζ : Circle, ∀ z ∈ ball z₀ r,
      ‖F z ζ‖ ≤ bound ζ := by
    intro ζ z hz
    have hzmem : z ∈ closedBall z₀ (3 * r) := by
      rw [mem_closedBall]
      have := mem_ball.mp hz
      linarith
    by_cases hnear : dist (ζ : ℂ) z₀ < 2 * r
    · simp only [F, if_pos hnear, norm_neg, norm_mul, Circle.norm_coe, mul_one,
        bound]
      have hζmem : (ζ : ℂ) ∈ closedBall z₀ (3 * r) := by
        rw [mem_closedBall]
        linarith
      have hslope : ‖analyticSlope L (ζ : ℂ) z‖ ≤ C := by
        by_cases heq : z = (ζ : ℂ)
        · subst z
          rw [analyticSlope_self]
          exact hLderiv _ hζmem
        · rw [analyticSlope_of_ne heq, norm_div]
          have hlip := hLlip _ hζmem _ hzmem
          rw [norm_sub_rev] at hlip ⊢
          exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr heq))).2 (by
            simpa [mul_comm] using hlip)
      calc
        ‖q ζ‖ * ‖analyticSlope L (ζ : ℂ) z‖ ≤ ‖q ζ‖ * C := by gcongr
        _ ≤ ‖q ζ‖ * B := by gcongr; exact le_max_left _ _
        _ = B * ‖q ζ‖ := by ring
    · simp only [F, if_neg hnear, norm_div, norm_mul, Circle.norm_coe, mul_one,
        bound]
      have hfar : 2 * r ≤ dist (ζ : ℂ) z₀ := le_of_not_gt hnear
      have hzdist : dist z z₀ < r := mem_ball.mp hz
      have hsep : r < ‖(ζ : ℂ) - z‖ := by
        rw [← dist_eq]
        have htri := dist_triangle (ζ : ℂ) z z₀
        linarith
      have hLz : ‖L z‖ ≤ C * r + ‖L z₀‖ := by
        have hlip := hLlip z₀ (by simp [hr.le]) z hzmem
        have hnorm := norm_le_norm_add_norm_sub' (L z) (L z₀)
        calc
          ‖L z‖ ≤ ‖L z₀‖ + ‖L z - L z₀‖ := hnorm
          _ ≤ ‖L z₀‖ + C * ‖z - z₀‖ := by gcongr
          _ ≤ ‖L z₀‖ + C * r := by
            gcongr
            simpa [dist_eq] using hzdist.le
          _ = C * r + ‖L z₀‖ := by ring
      have hnum : ‖L z - a ζ‖ ≤ C * r + ‖L z₀‖ + 1 := by
        calc
          ‖L z - a ζ‖ ≤ ‖L z‖ + ‖a ζ‖ := norm_sub_le _ _
          _ ≤ (C * r + ‖L z₀‖) + 1 := by rw [haUnit]; gcongr
          _ = C * r + ‖L z₀‖ + 1 := by ring
      have hratio : ‖L z - a ζ‖ / ‖(ζ : ℂ) - z‖ ≤
          (C * r + ‖L z₀‖ + 1) / r := by
        have hM : 0 ≤ C * r + ‖L z₀‖ + 1 := by positivity
        exact div_le_div₀ hM hnum hr hsep.le
      calc
        ‖q ζ‖ * ‖L z - a ζ‖ / ‖(ζ : ℂ) - z‖ =
            ‖q ζ‖ * (‖L z - a ζ‖ / ‖(ζ : ℂ) - z‖) := by ring
        _ ≤
            ‖q ζ‖ * ((C * r + ‖L z₀‖ + 1) / r) := by gcongr
        _ ≤ B * ‖q ζ‖ := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  have hboundInt : Integrable bound circleLebesgue := by
    exact hq.norm.const_mul B
  intro z hz
  let ρ := (r - dist z z₀) / 2
  have hz' : dist z z₀ < r := by simpa [mem_ball] using hz
  have hρ : 0 < ρ := by
    dsimp [ρ]
    linarith
  have hρsub : ball z ρ ⊆ ball z₀ r := by
    intro w hw
    rw [mem_ball] at hw ⊢
    have htri := dist_triangle w z z₀
    have hw' : dist w z < ρ := hw
    dsimp [ρ] at hw'
    linarith
  change DifferentiableAt ℂ (fun z => ∫ ζ, F z ζ ∂circleLebesgue) z
  exact differentiableAt_integral_of_cauchy_dominated hρ
    (fun w hw => hmeas w (hρsub hw))
    (fun ζ => (hdiff ζ).mono hρsub)
    (fun ζ w hw => hbound ζ w (hρsub hw)) hboundInt

theorem differentiableAt_hardyProductCauchyCommutator
    (u v : HardyDisk) (a : Circle → ℂ) (L : ℂ → ℂ)
    (z₀ : ℂ) {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (haMeas : Measurable a) (haUnit : ∀ ζ, ‖a ζ‖ = 1)
    (hLanalytic : ∀ w ∈ closedBall z₀ (3 * r), AnalyticAt ℂ L w)
    (hLlip : ∀ x ∈ closedBall z₀ (3 * r), ∀ y ∈ closedBall z₀ (3 * r),
      ‖L y - L x‖ ≤ C * ‖y - x‖)
    (hLderiv : ∀ w ∈ closedBall z₀ (3 * r), ‖deriv L w‖ ≤ C)
    (hslopeMeas : ∀ z ∈ ball z₀ r,
      AEStronglyMeasurable
        (fun ζ : Circle => analyticSlope L (ζ : ℂ) z) circleLebesgue) :
    DifferentiableAt ℂ
      (hardyProductCauchyCommutator u v a L z₀ r) z₀ := by
  exact differentiableAt_hardyProductCauchyCommutator_of_mem_ball
    u v a L z₀ hr hC haMeas haUnit hLanalytic hLlip hLderiv hslopeMeas
      z₀ (by simpa [mem_ball] using hr)

theorem hardyProductCauchyCommutator_eq
    (u v : HardyDisk) (a : Circle → ℂ) (L : ℂ → ℂ)
    (z₀ : ℂ) {r : ℝ}
    (haMeas : Measurable a) (haUnit : ∀ ζ, ‖a ζ‖ = 1)
    (hcoef : ∀ᵐ ζ : Circle ∂circleLebesgue,
      dist (ζ : ℂ) z₀ < 2 * r → a ζ = L (ζ : ℂ))
    {z : ℂ} (hz : ‖z‖ ≠ 1) :
    hardyProductCauchyCommutator u v a L z₀ r z =
      L z * circleL1CauchyTransform
        (fun ζ => (hardyDiskBoundary u : Circle → ℂ) ζ *
          (hardyDiskBoundary v : Circle → ℂ) ζ) z -
      circleL1CauchyTransform
        (fun ζ => a ζ *
          ((hardyDiskBoundary u : Circle → ℂ) ζ *
            (hardyDiskBoundary v : Circle → ℂ) ζ)) z := by
  let q : Circle → ℂ := fun ζ =>
    (hardyDiskBoundary u : Circle → ℂ) ζ *
      (hardyDiskBoundary v : Circle → ℂ) ζ
  let aq : Circle → ℂ := fun ζ => a ζ * q ζ
  let K : Circle → ℂ := fun ζ => (ζ : ℂ) / ((ζ : ℂ) - z)
  have hq : Integrable q circleLebesgue := by
    exact (Lp.memLp (hardyDiskBoundary u)).integrable_mul
      (Lp.memLp (hardyDiskBoundary v))
  have haq : Integrable aq circleLebesgue := by
    apply hq.bdd_mul haMeas.aestronglyMeasurable
    filter_upwards [hcoef] with ζ hcoefζ
    rw [haUnit]
  have hK : Continuous K := by
    apply Continuous.div continuous_subtype_val
      (continuous_subtype_val.sub continuous_const)
    intro ζ hden
    apply hz
    have heq : (ζ : ℂ) = z := sub_eq_zero.mp hden
    rw [← heq, Circle.norm_coe]
  let Kc : C(Circle, ℂ) := ⟨K, hK⟩
  have hqK : Integrable (fun ζ => q ζ * K ζ) circleLebesgue := by
    apply hq.mul_bdd
    · fun_prop
    · filter_upwards with ζ
      simpa [Kc] using ContinuousMap.norm_coe_le_norm Kc ζ
  have haqK : Integrable (fun ζ => aq ζ * K ζ) circleLebesgue := by
    apply haq.mul_bdd
    · fun_prop
    · filter_upwards with ζ
      simpa [Kc] using ContinuousMap.norm_coe_le_norm Kc ζ
  have hraw : hardyProductCauchyCommutator u v a L z₀ r z =
      ∫ ζ : Circle, q ζ * (ζ : ℂ) * (L z - a ζ) / ((ζ : ℂ) - z)
        ∂circleLebesgue := by
    rw [hardyProductCauchyCommutator]
    apply integral_congr_ae
    filter_upwards [hcoef] with ζ hcoefζ
    have hzne : z ≠ (ζ : ℂ) := by
      intro heq
      apply hz
      rw [heq, Circle.norm_coe]
    by_cases hnear : dist (ζ : ℂ) z₀ < 2 * r
    · rw [if_pos hnear, hcoefζ hnear, analyticSlope_of_ne hzne]
      have hden : (ζ : ℂ) - z ≠ 0 := sub_ne_zero.mpr hzne.symm
      field_simp [hden, sub_ne_zero.mpr hzne]
      ring
    · rw [if_neg hnear]
  rw [hraw, circleL1CauchyTransform, circleL1CauchyTransform]
  calc
    (∫ ζ : Circle, q ζ * (ζ : ℂ) * (L z - a ζ) / ((ζ : ℂ) - z)
        ∂circleLebesgue) =
        ∫ ζ : Circle,
          L z * (q ζ * K ζ) - aq ζ * K ζ ∂circleLebesgue := by
      apply integral_congr_ae
      filter_upwards with ζ
      dsimp [K, aq]
      ring
    _ = L z * ∫ ζ : Circle, q ζ * K ζ ∂circleLebesgue -
        ∫ ζ : Circle, aq ζ * K ζ ∂circleLebesgue := by
      rw [integral_sub (hqK.const_mul (L z)) haqK, integral_const_mul]
    _ = _ := by rfl

/-- Exact local analytic gluing of an analytically weighted `H¹` Hardy product to an exterior
`H¹` product. -/
theorem exists_analyticAt_weighted_hardyProduct_arc_glue
    (u₁ u₂ v₁ v₂ : HardyDisk) (a : Circle → ℂ) (L : ℂ → ℂ)
    (z₀ : ℂ) {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (haMeas : Measurable a) (haUnit : ∀ ζ, ‖a ζ‖ = 1)
    (hLanalytic : ∀ w ∈ closedBall z₀ (3 * r), AnalyticAt ℂ L w)
    (hLlip : ∀ x ∈ closedBall z₀ (3 * r), ∀ y ∈ closedBall z₀ (3 * r),
      ‖L y - L x‖ ≤ C * ‖y - x‖)
    (hLderiv : ∀ w ∈ closedBall z₀ (3 * r), ‖deriv L w‖ ≤ C)
    (hslopeMeas : ∀ z ∈ ball z₀ r,
      AEStronglyMeasurable
        (fun ζ : Circle => analyticSlope L (ζ : ℂ) z) circleLebesgue)
    (hcoef : ∀ᵐ ζ : Circle ∂circleLebesgue,
      dist (ζ : ℂ) z₀ < 2 * r → a ζ = L (ζ : ℂ))
    (hseam : ∀ᵐ ζ : Circle ∂circleLebesgue,
      dist (ζ : ℂ) z₀ < 2 * r →
        a ζ * ((hardyDiskBoundary u₁ : Circle → ℂ) ζ *
          (hardyDiskBoundary u₂ : Circle → ℂ) ζ) =
            (starRingEnd ℂ)
              ((hardyDiskBoundary v₁ : Circle → ℂ) ζ *
                (hardyDiskBoundary v₂ : Circle → ℂ) ζ)) :
    ∃ G : ℂ → ℂ,
      AnalyticAt ℂ G z₀ ∧
      (∀ z : ℂ, ‖z‖ < 1 →
        G z = L z * (hardyFun u₁ z * hardyFun u₂ z)) ∧
      (∀ z : ℂ, 1 < ‖z‖ →
        G z = hardyProductExteriorReflection v₁ v₂ z) := by
  let q : Circle → ℂ := fun ζ =>
    (hardyDiskBoundary u₁ : Circle → ℂ) ζ *
      (hardyDiskBoundary u₂ : Circle → ℂ) ζ
  let aq : Circle → ℂ := fun ζ => a ζ * q ζ
  let s : Circle → ℂ := fun ζ =>
    (hardyDiskBoundary v₁ : Circle → ℂ) ζ *
      (hardyDiskBoundary v₂ : Circle → ℂ) ζ
  let sc : Circle → ℂ := fun ζ => (starRingEnd ℂ) (s ζ)
  let d : Circle → ℂ := fun ζ => aq ζ - sc ζ
  let H : ℂ → ℂ := hardyProductCauchyCommutator u₁ u₂ a L z₀ r
  let c : ℂ := (starRingEnd ℂ) (v₁ 0 * v₂ 0)
  have hq : Integrable q circleLebesgue := by
    exact (Lp.memLp (hardyDiskBoundary u₁)).integrable_mul
      (Lp.memLp (hardyDiskBoundary u₂))
  have haq : Integrable aq circleLebesgue := by
    apply hq.bdd_mul haMeas.aestronglyMeasurable
    filter_upwards with ζ
    rw [haUnit]
  have hs : Integrable s circleLebesgue := by
    exact (Lp.memLp (hardyDiskBoundary v₁)).integrable_mul
      (Lp.memLp (hardyDiskBoundary v₂))
  have hsc : Integrable sc circleLebesgue := by
    exact hs.norm.mono'
      (Complex.continuous_conj.comp_aestronglyMeasurable hs.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ζ => by rw [RCLike.norm_conj])
  have hd : Integrable d circleLebesgue := haq.sub hsc
  have hzeroD : ∀ᵐ ζ : Circle ∂circleLebesgue,
      dist (ζ : ℂ) z₀ < 2 * r → d ζ = 0 := by
    filter_upwards [hseam] with ζ hmatch
    intro hnear
    dsimp [d, aq, q, sc, s]
    rw [hmatch hnear, sub_self]
  have hHdiff : ∀ z ∈ ball z₀ r, DifferentiableAt ℂ H z :=
    differentiableAt_hardyProductCauchyCommutator_of_mem_ball
      u₁ u₂ a L z₀ hr hC haMeas haUnit hLanalytic hLlip hLderiv hslopeMeas
  have hGanalytic : AnalyticAt ℂ
      (fun z => circleL1CauchyTransform d z + c + H z) z₀ := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [ball_mem_nhds z₀ (by positivity : 0 < r / 2)] with z hz
    have hz' : dist z z₀ < r / 2 := by simpa [mem_ball] using hz
    have hzR : z ∈ ball z₀ r := by
      rw [mem_ball]
      linarith
    have hzeroDz : ∀ᵐ ζ : Circle ∂circleLebesgue,
        dist (ζ : ℂ) z < r / 2 → d ζ = 0 := by
      filter_upwards [hzeroD] with ζ hζ
      intro hζz
      apply hζ
      have htri := dist_triangle (ζ : ℂ) z z₀
      linarith
    exact ((differentiableAt_circleL1CauchyTransform_of_ae_zero_near
      d hd z (by positivity : 0 < r / 2) hzeroDz).add
        (differentiableAt_const (c := c))).add (hHdiff z hzR)
  refine ⟨fun z => circleL1CauchyTransform d z + c + H z,
    hGanalytic, ?_, ?_⟩
  · intro z hz
    have hzne : ‖z‖ ≠ 1 := ne_of_lt hz
    have hH := hardyProductCauchyCommutator_eq
      u₁ u₂ a L z₀ haMeas haUnit hcoef hzne
    change circleL1CauchyTransform (fun ζ => aq ζ - sc ζ) z + c + H z = _
    rw [circleL1CauchyTransform_sub aq sc haq hsc hzne]
    change circleL1CauchyTransform aq z -
      circleL1CauchyTransform (fun ζ => (starRingEnd ℂ) (s ζ)) z + c + H z = _
    rw [show s = fun ζ =>
          (hardyDiskBoundary v₁ : Circle → ℂ) ζ *
            (hardyDiskBoundary v₂ : Circle → ℂ) ζ by rfl,
      circleL1CauchyTransform_conj_hardyProduct v₁ v₂ hz]
    rw [show H z = L z * circleL1CauchyTransform q z -
          circleL1CauchyTransform aq z by
      simpa [H, q, aq] using hH]
    rw [show q = fun ζ =>
          (hardyDiskBoundary u₁ : Circle → ℂ) ζ *
            (hardyDiskBoundary u₂ : Circle → ℂ) ζ by rfl,
      circleL1CauchyTransform_hardyProduct u₁ u₂ hz]
    dsimp [c]
    ring
  · intro z hz
    have hzne : ‖z‖ ≠ 1 := ne_of_gt hz
    have hH := hardyProductCauchyCommutator_eq
      u₁ u₂ a L z₀ haMeas haUnit hcoef hzne
    change circleL1CauchyTransform (fun ζ => aq ζ - sc ζ) z + c + H z = _
    rw [circleL1CauchyTransform_sub aq sc haq hsc hzne]
    change circleL1CauchyTransform aq z -
      circleL1CauchyTransform (fun ζ => (starRingEnd ℂ) (s ζ)) z + c + H z = _
    rw [show s = fun ζ =>
          (hardyDiskBoundary v₁ : Circle → ℂ) ζ *
            (hardyDiskBoundary v₂ : Circle → ℂ) ζ by rfl,
      circleL1CauchyTransform_conj_hardyProduct_exterior v₁ v₂ hz]
    rw [show H z = L z * circleL1CauchyTransform q z -
          circleL1CauchyTransform aq z by
      simpa [H, q, aq] using hH]
    rw [show q = fun ζ =>
          (hardyDiskBoundary u₁ : Circle → ℂ) ζ *
            (hardyDiskBoundary u₂ : Circle → ℂ) ζ by rfl,
      circleL1CauchyTransform_hardyProduct_exterior u₁ u₂ hz]
    dsimp [c]
    rw [hardyProductExteriorReflection]
    ring

/-- Exact local gluing of an analytically weighted `H¹` Hardy product to an exterior `H¹`
product. -/
theorem exists_differentiableAt_weighted_hardyProduct_arc_glue
    (u₁ u₂ v₁ v₂ : HardyDisk) (a : Circle → ℂ) (L : ℂ → ℂ)
    (z₀ : ℂ) {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (haMeas : Measurable a) (haUnit : ∀ ζ, ‖a ζ‖ = 1)
    (hLanalytic : ∀ w ∈ closedBall z₀ (3 * r), AnalyticAt ℂ L w)
    (hLlip : ∀ x ∈ closedBall z₀ (3 * r), ∀ y ∈ closedBall z₀ (3 * r),
      ‖L y - L x‖ ≤ C * ‖y - x‖)
    (hLderiv : ∀ w ∈ closedBall z₀ (3 * r), ‖deriv L w‖ ≤ C)
    (hslopeMeas : ∀ z ∈ ball z₀ r,
      AEStronglyMeasurable
        (fun ζ : Circle => analyticSlope L (ζ : ℂ) z) circleLebesgue)
    (hcoef : ∀ᵐ ζ : Circle ∂circleLebesgue,
      dist (ζ : ℂ) z₀ < 2 * r → a ζ = L (ζ : ℂ))
    (hseam : ∀ᵐ ζ : Circle ∂circleLebesgue,
      dist (ζ : ℂ) z₀ < 2 * r →
        a ζ * ((hardyDiskBoundary u₁ : Circle → ℂ) ζ *
          (hardyDiskBoundary u₂ : Circle → ℂ) ζ) =
            (starRingEnd ℂ)
              ((hardyDiskBoundary v₁ : Circle → ℂ) ζ *
                (hardyDiskBoundary v₂ : Circle → ℂ) ζ)) :
    ∃ G : ℂ → ℂ,
      DifferentiableAt ℂ G z₀ ∧
      (∀ z : ℂ, ‖z‖ < 1 →
        G z = L z * (hardyFun u₁ z * hardyFun u₂ z)) ∧
      (∀ z : ℂ, 1 < ‖z‖ →
        G z = hardyProductExteriorReflection v₁ v₂ z) := by
  obtain ⟨G, hG, hin, hout⟩ :=
    exists_analyticAt_weighted_hardyProduct_arc_glue
      u₁ u₂ v₁ v₂ a L z₀ hr hC haMeas haUnit hLanalytic hLlip hLderiv
        hslopeMeas hcoef hseam
  exact ⟨G, hG.differentiableAt, hin, hout⟩

end

end GaloisForLFunctions.HTGeometry
