import GaloisForLFunctions.RHTower.PaperThetaContourMellin
import GaloisForLFunctions.RHTower.PaperThetaBoundedForcing
import GaloisForLFunctions.HTGeometry.ExponentialLagrangeContour

/-! # Spatial continuity and common variation control of native periods

Charge cancellation replaces the discontinuous cut representation by the
continuous right-hand representation. The cut representation still supplies
one spatial variation control for every contour in a fixed spectral strip.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint
open HTGeometry GaloisForLFunctions.HTGeometry

theorem continuous_flatQuotient_rectangle {A γ : ℂ → ℂ} (hA : Measurable A)
    (hγ : Continuous γ) (a b : ℂ) (hAc : ContinuousOn A (RectangleBorder a b)) :
    Continuous (fun x => RectangleIntegral' (fun s => A s*flatQuotient (γ s) x) a b) := by
  obtain ⟨M₀, hM₀⟩ := (isCompact_rectangleBorder a b).exists_bound_of_continuousOn hAc
  obtain ⟨T₀, hT₀⟩ := (isCompact_rectangleBorder a b).exists_bound_of_continuousOn hγ.continuousOn
  let M := max M₀ 0
  let T := max T₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hT : 0 ≤ T := le_max_right _ _
  have hrow {p q : ℝ} (σ : ℝ → ℂ) (hσ : Continuous σ)
      (hs : MapsTo σ (uIcc p q) (RectangleBorder a b)) :
      Continuous (fun x => ∫ t in p..q, A (σ t)*flatQuotient (γ (σ t)) x) := by
    apply continuous_iff_continuousAt.mpr
    intro x₀
    let C := M*(1+T*stripTailControl T (x₀-1))
    apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => C)
    · exact Eventually.of_forall fun x =>
        ((hA.comp hσ.measurable).mul
          (((differentiable_flatQuotient_parameter x).continuous.comp (hγ.comp hσ)).measurable)).aestronglyMeasurable
    · filter_upwards [Ioi_mem_nhds (show x₀-1 < x₀ by linarith)] with x hx
      exact Eventually.of_forall fun t ht => by
        have hb := hs (uIoc_subset_uIcc ht)
        have hm : ‖A (σ t)‖ ≤ M := (hM₀ (σ t) hb).trans (le_max_left _ _)
        have hn : ‖γ (σ t)‖ ≤ T := (hT₀ (σ t) hb).trans (le_max_left _ _)
        have hz : -(γ (σ t)).im ≤ T :=
          (neg_le_abs _).trans ((abs_im_le_norm _).trans hn)
        have hq : ‖flatQuotient (γ (σ t)) x‖ ≤ 1+T*stripTailControl T (x₀-1) := by
          calc
            _ = ‖(flatQuotient (γ (σ t)) x+1)-1‖ := by rw [add_sub_cancel_right]
            _ ≤ ‖flatQuotient (γ (σ t)) x+1‖+‖(1:ℂ)‖ := norm_sub_le _ _
            _ ≤ ‖γ (σ t)‖*stripTailControl T x+1 := by
              rw [norm_one]
              linarith [flatQuotient_add_one_strip hz x]
            _ ≤ T*stripTailControl T (x₀-1)+1 := by
              gcongr
              · exact stripTailControl_nonneg T x
              · exact stripTailControl_antitone T hx.le
            _ = _ := add_comm _ _
        rw [norm_mul]
        exact mul_le_mul hm hq (norm_nonneg _) hM
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun t _ =>
        (continuous_const.mul (continuous_flatQuotient (γ (σ t)))).continuousAt
  have hB := hrow (fun t => (t : ℂ)+(a.im : ℂ)*I) (by fun_prop)
    (mapsTo_rectangleBorder_left_im a b)
  have hU := hrow (fun t => (t : ℂ)+(b.im : ℂ)*I) (by fun_prop)
    (mapsTo_rectangleBorder_right_im a b)
  have hR := hrow (fun t => (b.re : ℂ)+(t : ℂ)*I) (by fun_prop)
    (mapsTo_rectangleBorder_right_re a b)
  have hL := hrow (fun t => (a.re : ℂ)+(t : ℂ)*I) (by fun_prop)
    (mapsTo_rectangleBorder_left_re a b)
  change Continuous (fun x => (1/(2*(Real.pi : ℂ)*I))*
    (((∫ t in a.re..b.re, A ((t:ℂ)+a.im*I)*flatQuotient (γ ((t:ℂ)+a.im*I)) x)-
      (∫ t in a.re..b.re, A ((t:ℂ)+b.im*I)*flatQuotient (γ ((t:ℂ)+b.im*I)) x))+
      I*(∫ t in a.im..b.im, A ((b.re:ℂ)+t*I)*flatQuotient (γ ((b.re:ℂ)+t*I)) x)-
      I*(∫ t in a.im..b.im, A ((a.re:ℂ)+t*I)*flatQuotient (γ ((a.re:ℂ)+t*I)) x)))
  exact continuous_const.mul (((hB.sub hU).add (continuous_const.mul hR)).sub
    (continuous_const.mul hL))

theorem nativeXiContour_eq_right {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a b : ℂ} (hnz : ∀ s ∈ RectangleBorder a b, xi s ≠ 0) (cut x : ℝ) :
    nativeXiContour F a b cut x =
      -I*RectangleIntegral' (fun s => F s/xi s*flatQuotient (thetaContourParameter s) x) a b := by
  rw [nativeXiContour_cut_independent hF hnz cut x x]
  simp only [nativeXiContour, cutQuotient, lt_self_iff_false, if_false]

theorem continuous_nativeXiContour {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a b : ℂ} (hnz : ∀ s ∈ RectangleBorder a b, xi s ≠ 0) (cut : ℝ) :
    Continuous (nativeXiContour F a b cut) := by
  have he : nativeXiContour F a b cut = fun x =>
      -I*RectangleIntegral' (fun s => F s/xi s*flatQuotient (thetaContourParameter s) x) a b :=
    funext (nativeXiContour_eq_right hF hnz cut)
  rw [he]
  exact continuous_const.mul (continuous_flatQuotient_rectangle
    (hF.continuous.measurable.div deningerMeyerXi_entireRegular.differentiable.continuous.measurable)
    differentiable_thetaContourParameter.continuous a b
    (hF.continuous.continuousOn.div
      deningerMeyerXi_entireRegular.differentiable.continuous.continuousOn hnz))

theorem nativeXiContour_norm_le {F : ℂ → ℂ} {a b : ℂ} {B M T : ℝ}
    (hM : 0 ≤ M)
    (hb : ∀ s ∈ RectangleBorder a b, ‖F s/xi s‖ ≤ M ∧
      |(thetaContourParameter s).im| ≤ B ∧ ‖thetaContourParameter s‖ ≤ T) (x : ℝ) :
    ‖nativeXiContour F a b 0 x‖ ≤
      (|b.re-a.re|+|b.im-a.im|)*M*(1+T*stripTailControl B 0)/Real.pi := by
  have hi : ∀ s ∈ RectangleBorder a b,
      ‖F s/xi s*cutQuotient (thetaContourParameter s) 0 x‖ ≤ M*(1+T*stripTailControl B 0) := by
    intro s hs
    obtain ⟨hm, hz, ht⟩ := hb s hs
    have hq : ‖cutQuotient (thetaContourParameter s) 0 x‖ ≤ 1+T*stripTailControl B 0 := by
      calc
        _ = ‖(cutQuotient (thetaContourParameter s) 0 x+1)-1‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖cutQuotient (thetaContourParameter s) 0 x+1‖+‖(1:ℂ)‖ := norm_sub_le _ _
        _ ≤ ‖thetaContourParameter s‖*stripTailControl B 0+1 := by
          rw [norm_one]
          linarith [cutQuotient_add_one_strip hz x]
        _ ≤ 1+T*stripTailControl B 0 := by
          linarith [mul_le_mul_of_nonneg_right ht (stripTailControl_nonneg B 0)]
    rw [norm_mul]
    exact mul_le_mul hm hq (norm_nonneg _) hM
  have hh := norm_rectangleIntegral'_le hi
  simpa only [nativeXiContour, norm_mul, norm_neg, norm_I, one_mul, mul_assoc] using hh

theorem nativeXiContour_difference_le {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a b : ℂ} (hnz : ∀ s ∈ RectangleBorder a b, xi s ≠ 0) {B M T : ℝ}
    (hM : 0 ≤ M)
    (hb : ∀ s ∈ RectangleBorder a b, ‖F s/xi s‖ ≤ M ∧
      |(thetaContourParameter s).im| ≤ B ∧ ‖thetaContourParameter s‖ ≤ T) (x y : ℝ) :
    ‖nativeXiContour F a b 0 y-nativeXiContour F a b 0 x‖ ≤
      (|b.re-a.re|+|b.im-a.im|)*M*T/Real.pi*|stripCutControl B y-stripCutControl B x| := by
  have hi (v : ℝ) : RectangleBorderIntegrable
      (fun s => F s/xi s*cutQuotient (thetaContourParameter s) 0 v) a b :=
    ((hF.continuous.continuousOn.div
        deningerMeyerXi_entireRegular.differentiable.continuous.continuousOn hnz).mul
      (((differentiable_cutQuotient_parameter 0 v).continuous.comp
        differentiable_thetaContourParameter.continuous).continuousOn)).rectangleBorder_integrable
  have he : nativeXiContour F a b 0 y-nativeXiContour F a b 0 x =
      -I*RectangleIntegral' (fun s => F s/xi s*cutQuotient (thetaContourParameter s) 0 y-
        F s/xi s*cutQuotient (thetaContourParameter s) 0 x) a b := by
    rw [rectangleIntegral'_sub (hi y) (hi x)]
    dsimp [nativeXiContour]
    ring
  rw [he, norm_mul, norm_neg, norm_I, one_mul]
  have hh := norm_rectangleIntegral'_le (z := a) (w := b)
    (M := M*T*|stripCutControl B y-stripCutControl B x|) (f := fun s =>
      F s/xi s*cutQuotient (thetaContourParameter s) 0 y-
      F s/xi s*cutQuotient (thetaContourParameter s) 0 x) (by
        intro s hs
        obtain ⟨hm, hz, ht⟩ := hb s hs
        rw [← mul_sub, norm_mul]
        calc
          _ ≤ M*(‖thetaContourParameter s‖*|stripCutControl B y-stripCutControl B x|) :=
            mul_le_mul hm (cutQuotient_difference_strip hz x y) (norm_nonneg _) hM
          _ ≤ M*(T*|stripCutControl B y-stripCutControl B x|) := by gcongr
          _ = _ := by ring)
  exact hh.trans_eq (by ring)

end RHTower.PaperThetaEndpoint
