import GaloisForLFunctions.RHTower.PaperThetaContourExchange

/-! # The original Mellin coordinate of native theta periods

The affine change of parameter preserves the full divided-difference kernel,
including its removable diagonal. This identifies the theta contour kernel
with the literal source contour used in original Meyer synthesis.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HTGeometry

theorem cutThetaTransform_mellin_coordinate (s u : ℂ) :
    cutThetaTransform (thetaContourParameter s) (thetaContourParameter u) =
      -((u-1/2)*dslope xi s u+xi s)/(thetaSource.mass : ℂ) := by
  have hd := (differentiable_entire_dslope
    deningerMeyerXi_entireRegular.differentiable s).continuous
  have hl : Continuous (fun v => cutThetaTransform (thetaContourParameter s) (thetaContourParameter v)) :=
    (differentiable_cutThetaTransform _).continuous.comp differentiable_thetaContourParameter.continuous
  have hr : Continuous (fun v => -((v-1/2)*dslope xi s v+xi s)/(thetaSource.mass : ℂ)) :=
    (((continuous_id.sub continuous_const).mul hd).add continuous_const).neg.div_const _
  have he : (fun v => cutThetaTransform (thetaContourParameter s) (thetaContourParameter v)) =
      fun v => -((v-1/2)*dslope xi s v+xi s)/(thetaSource.mass : ℂ) := by
    apply Continuous.ext_on (dense_compl_singleton s) hl hr
    intro v hv
    have hvs : v ≠ s := hv
    have ht : thetaContourParameter v-thetaContourParameter s = -I*(v-s) := by
      dsimp [thetaContourParameter]
      ring
    have hn : thetaContourParameter v-thetaContourParameter s ≠ 0 := by
      rw [ht]
      exact mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (sub_ne_zero.mpr hvs)
    change cutThetaTransform (thetaContourParameter s) (thetaContourParameter v) =
      -((v-1/2)*dslope xi s v+xi s)/(thetaSource.mass : ℂ)
    apply mul_left_cancel₀ hn
    rw [cutThetaTransform_equation, XiC_thetaContourParameter, XiC_thetaContourParameter,
      dslope_of_ne _ hvs, slope_def_field]
    have hm : (thetaSource.mass : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr thetaSource.mass_ne_zero
    dsimp [thetaContourParameter]
    field_simp [sub_ne_zero.mpr hvs]
    ring
  exact congrFun he u

theorem nativeXiContour_transform {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a b : ℂ} (hnz : ∀ s ∈ RectangleBorder a b, xi s ≠ 0) (cut : ℝ) (u : ℂ) :
    (∫ x, flatCharDensity (thetaContourParameter u) x*nativeXiContour F a b cut x) =
      (I*(u-1/2)/(thetaSource.mass : ℂ))*deningerMeyerXiContour F a b u := by
  have hcut : nativeXiContour F a b cut = nativeXiContour F a b 0 := by
    funext x
    exact nativeXiContour_cut_independent hF hnz cut 0 x
  rw [hcut]
  let A : ℂ → ℂ := fun s => F s/xi s
  have hm : (thetaSource.mass : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr thetaSource.mass_ne_zero
  have hξ := deningerMeyerXi_entireRegular.differentiable
  have hAc : ContinuousOn A (RectangleBorder a b) :=
    hF.continuous.continuousOn.div hξ.continuous.continuousOn hnz
  have hAm : Measurable A := hF.continuous.measurable.div hξ.continuous.measurable
  have hR := cutThetaTransform_rectangle hAm differentiable_thetaContourParameter.continuous
    a b hAc (thetaContourParameter u)
  have hsource : (∫ x, flatCharDensity (thetaContourParameter u) x*nativeXiContour F a b 0 x) =
      -I*RectangleIntegral' (fun s => A s*
        cutThetaTransform (thetaContourParameter s) (thetaContourParameter u)) a b := by
    calc
      _ = -I*(∫ x, flatCharDensity (thetaContourParameter u) x*
          RectangleIntegral' (fun s => A s*cutQuotient (thetaContourParameter s) 0 x) a b) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp [nativeXiContour, A]
        ring
      _ = _ := by rw [hR.2]
  let D : ℂ → ℂ := fun s => A s*dslope xi s u
  have hd : Continuous (fun s => dslope xi s u) := by
    have he : (fun s => dslope xi s u) = dslope xi u := by
      funext s
      exact dslope_symm xi s u
    rw [he]
    exact (differentiable_entire_dslope hξ u).continuous
  have hD : ContinuousOn D (RectangleBorder a b) := hAc.mul hd.continuousOn
  let c : ℂ := -(u-1/2)/(thetaSource.mass : ℂ)
  have hcont : RectangleIntegral' (fun s => A s*
        cutThetaTransform (thetaContourParameter s) (thetaContourParameter u)) a b =
      c*RectangleIntegral' D a b := by
    have he : RectangleIntegral' (fun s => A s*
          cutThetaTransform (thetaContourParameter s) (thetaContourParameter u)) a b =
        RectangleIntegral' (fun s => c*D s-F s/(thetaSource.mass : ℂ)) a b := by
      apply RectangleIntegral'_congr
      intro s hs
      change A s*cutThetaTransform (thetaContourParameter s) (thetaContourParameter u) =
        c*D s-F s/(thetaSource.mass : ℂ)
      rw [cutThetaTransform_mellin_coordinate]
      dsimp [A, D, c]
      field_simp [hnz s hs]
      ring
    have hdiv : Differentiable ℂ (fun s => F s/(thetaSource.mass : ℂ)) := hF.div_const _
    have hz : RectangleIntegral' (fun s => F s/(thetaSource.mass : ℂ)) a b = 0 := by
      have hv := HolomorphicOn.vanishesOnRectangle (f := fun s => F s/(thetaSource.mass : ℂ))
        (z := a) (w := b) (U := univ) hdiv.differentiableOn (subset_univ _)
      rw [RectangleIntegral', hv, smul_zero]
    have hcD : RectangleBorderIntegrable (fun s => c*D s) a b :=
      (continuousOn_const.mul hD).rectangleBorder_integrable
    have hFdiv : RectangleBorderIntegrable (fun s => F s/(thetaSource.mass : ℂ)) a b :=
      hdiv.continuous.continuousOn.rectangleBorder_integrable
    rw [he, rectangleIntegral'_sub hcD hFdiv, rectangleIntegral'_const_mul, hz, sub_zero]
  rw [hsource, hcont]
  change -I*(c*deningerMeyerXiContour F a b u) = _
  dsimp [c]
  ring

/-- Every period has zero actual theta mean; the exceptional constant is absent. -/
theorem nativeXiContour_theta_mean_zero {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a b : ℂ} (hnz : ∀ s ∈ RectangleBorder a b, xi s ≠ 0) (cut : ℝ) :
    (∫ x, flatCharDensity 0 x*nativeXiContour F a b cut x) = 0 := by
  simpa [thetaContourParameter] using nativeXiContour_transform hF hnz cut (1/2)

/-- Identification with the Mellin transform of the existing literal source contour. -/
theorem nativeXiContour_original_source {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (a b : ℂ) (ha : a.re = -1) (hb : b.re = 2) (hab : a.im ≤ b.im)
    (hnz : ∀ s ∈ RectangleBorder a b, xi s ≠ 0) (cut : ℝ) (u : ℂ) :
    (∫ x, flatCharDensity (thetaContourParameter u) x*nativeXiContour F a b cut x) =
      (I*(u-1/2)/(thetaSource.mass : ℂ))*
        deningerMeyerStrongLogMellin (deningerMeyerXiContourSource F hF a b ha hb hab hnz) u := by
  rw [deningerMeyerXiContourSource_mellin]
  exact nativeXiContour_transform hF hnz cut u

end RHTower.PaperThetaEndpoint
