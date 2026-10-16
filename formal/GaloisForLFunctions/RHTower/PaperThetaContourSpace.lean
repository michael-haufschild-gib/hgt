import GaloisForLFunctions.RHTower.PaperThetaContourControl

/-! # Native contour periods as actual bounded continuous functions -/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint
open HTGeometry GaloisForLFunctions.HTGeometry

theorem nativeXiContour_bounded {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a b : ℂ} (hnz : ∀ s ∈ RectangleBorder a b, xi s ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖nativeXiContour F a b 0 x‖ ≤ C := by
  have hc : ContinuousOn (fun s => F s/xi s) (RectangleBorder a b) :=
    hF.continuous.continuousOn.div
      deningerMeyerXi_entireRegular.differentiable.continuous.continuousOn hnz
  obtain ⟨M₀, hM₀⟩ := (isCompact_rectangleBorder a b).exists_bound_of_continuousOn hc
  obtain ⟨T₀, hT₀⟩ := (isCompact_rectangleBorder a b).exists_bound_of_continuousOn
    differentiable_thetaContourParameter.continuous.continuousOn
  let M := max M₀ 0
  let T := max T₀ 0
  have ht := stripTailControl_nonneg T 0
  refine ⟨(|b.re-a.re|+|b.im-a.im|)*M*(1+T*stripTailControl T 0)/Real.pi,
    by dsimp [M, T]; positivity, ?_⟩
  exact fun x => nativeXiContour_norm_le (le_max_right _ _) (fun s hs =>
    ⟨(hM₀ s hs).trans (le_max_left _ _),
      (abs_im_le_norm _).trans ((hT₀ s hs).trans (le_max_left _ _)),
      (hT₀ s hs).trans (le_max_left _ _)⟩) x

def nativeXiContourBCF (F : ℂ → ℂ) (hF : Differentiable ℂ F) (a b : ℂ)
    (hnz : ∀ s ∈ RectangleBorder a b, xi s ≠ 0) : NativeContinuousSpace :=
  BoundedContinuousFunction.ofNormedAddCommGroup (nativeXiContour F a b 0)
    (continuous_nativeXiContour hF hnz 0) (nativeXiContour_bounded hF hnz).choose
    (nativeXiContour_bounded hF hnz).choose_spec.2

@[simp] theorem nativeXiContourBCF_apply (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (a b : ℂ) (hnz : ∀ s ∈ RectangleBorder a b, xi s ≠ 0) (x : ℝ) :
    nativeXiContourBCF F hF a b hnz x = nativeXiContour F a b 0 x := rfl

theorem nativeXiContourBCF_norm_le {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a b : ℂ} (hnz : ∀ s ∈ RectangleBorder a b, xi s ≠ 0) {B M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hb : ∀ s ∈ RectangleBorder a b, ‖F s/xi s‖ ≤ M ∧
      |(thetaContourParameter s).im| ≤ B ∧ ‖thetaContourParameter s‖ ≤ T) :
    ‖nativeXiContourBCF F hF a b hnz‖ ≤
      (|b.re-a.re|+|b.im-a.im|)*M*(1+T*stripTailControl B 0)/Real.pi := by
  apply (BoundedContinuousFunction.norm_le (by
    have ht := stripTailControl_nonneg B 0
    positivity)).mpr
  exact nativeXiContour_norm_le hM hb

theorem nativeXiContour_sub {F G : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hG : Differentiable ℂ G) {a b : ℂ}
    (hnz : ∀ s ∈ RectangleBorder a b, xi s ≠ 0) (x : ℝ) :
    nativeXiContour (fun s => F s-G s) a b 0 x =
      nativeXiContour F a b 0 x-nativeXiContour G a b 0 x := by
  have hi (H : ℂ → ℂ) (hH : Differentiable ℂ H) : RectangleBorderIntegrable
      (fun s => H s/xi s*cutQuotient (thetaContourParameter s) 0 x) a b :=
    ((hH.continuous.continuousOn.div
        deningerMeyerXi_entireRegular.differentiable.continuous.continuousOn hnz).mul
      (((differentiable_cutQuotient_parameter 0 x).continuous.comp
        differentiable_thetaContourParameter.continuous).continuousOn)).rectangleBorder_integrable
  have he : (fun s => (F s-G s)/xi s*cutQuotient (thetaContourParameter s) 0 x) =
      fun s => F s/xi s*cutQuotient (thetaContourParameter s) 0 x-
        G s/xi s*cutQuotient (thetaContourParameter s) 0 x := by funext s; ring
  simp only [nativeXiContour, he, rectangleIntegral'_sub (hi F hF) (hi G hG)]
  ring

theorem nativeXiContour_const_mul (F : ℂ → ℂ) (a b : ℂ) (c : ℂ) (x : ℝ) :
    nativeXiContour (fun s => c*F s) a b 0 x = c*nativeXiContour F a b 0 x := by
  have he : (fun s => c*F s/xi s*cutQuotient (thetaContourParameter s) 0 x) =
      fun s => c*(F s/xi s*cutQuotient (thetaContourParameter s) 0 x) := by funext s; ring
  simp only [nativeXiContour, he, rectangleIntegral'_const_mul]
  ring

theorem nativeXiContour_of_entire_division {F H : ℂ → ℂ}
    (hH : Differentiable ℂ H) (hdiv : ∀ s, F s = xi s*H s)
    {a b : ℂ} (hnz : ∀ s ∈ RectangleBorder a b, xi s ≠ 0) (x : ℝ) :
    nativeXiContour F a b 0 x = 0 := by
  have he : RectangleIntegral' (fun s => F s/xi s*cutQuotient (thetaContourParameter s) 0 x) a b =
      RectangleIntegral' (fun s => H s*cutQuotient (thetaContourParameter s) 0 x) a b := by
    apply RectangleIntegral'_congr
    intro s hs
    change F s/xi s*cutQuotient (thetaContourParameter s) 0 x = _
    rw [hdiv]
    field_simp [hnz s hs]
  have hh : Differentiable ℂ (fun s => H s*cutQuotient (thetaContourParameter s) 0 x) :=
    hH.mul ((differentiable_cutQuotient_parameter 0 x).comp differentiable_thetaContourParameter)
  have hz := HolomorphicOn.vanishesOnRectangle (f := fun s => H s*
    cutQuotient (thetaContourParameter s) 0 x) (z := a) (w := b)
    (U := univ) hh.differentiableOn (subset_univ _)
  simp only [nativeXiContour, he, RectangleIntegral', hz, smul_zero, mul_zero]

/-- One scalar controls both the uniform norm and all spatial increments. -/
theorem nativeXiContour_control {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a b : ℂ} (hnz : ∀ s ∈ RectangleBorder a b, xi s ≠ 0) {B M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hb : ∀ s ∈ RectangleBorder a b, ‖F s/xi s‖ ≤ M ∧
      |(thetaContourParameter s).im| ≤ B ∧ ‖thetaContourParameter s‖ ≤ T) :
    let C := (|b.re-a.re|+|b.im-a.im|)*M*(1+T)*(1+stripTailControl B 0)/Real.pi
    0 ≤ C ∧ ‖nativeXiContourBCF F hF a b hnz‖ ≤ C ∧
      ∀ x y, ‖nativeXiContour F a b 0 y-nativeXiContour F a b 0 x‖ ≤
        C*|stripCutControl B y-stripCutControl B x| := by
  dsimp only
  have ht := stripTailControl_nonneg B 0
  have h₁ : 1+T*stripTailControl B 0 ≤ (1+T)*(1+stripTailControl B 0) := by nlinarith
  have h₂ : T ≤ (1+T)*(1+stripTailControl B 0) := by nlinarith
  refine ⟨by positivity, ?_, ?_⟩
  · calc
      _ ≤ (|b.re-a.re|+|b.im-a.im|)*M*(1+T*stripTailControl B 0)/Real.pi :=
        nativeXiContourBCF_norm_le hF hnz hM hT hb
      _ ≤ (|b.re-a.re|+|b.im-a.im|)*M*((1+T)*(1+stripTailControl B 0))/Real.pi := by gcongr
      _ = _ := by ring
  · intro x y
    calc
      _ ≤ (|b.re-a.re|+|b.im-a.im|)*M*T/Real.pi*
          |stripCutControl B y-stripCutControl B x| := nativeXiContour_difference_le hF hnz hM hb x y
      _ ≤ ((|b.re-a.re|+|b.im-a.im|)*M*((1+T)*(1+stripTailControl B 0))/Real.pi)*
          |stripCutControl B y-stripCutControl B x| := by gcongr
      _ = _ := by ring

theorem nativeXiContour_strip_control {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a b : ℂ} (hnz : ∀ s ∈ RectangleBorder a b, xi s ≠ 0) (B : ℝ)
    (hstrip : ∀ s ∈ RectangleBorder a b, |(thetaContourParameter s).im| ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ‖nativeXiContourBCF F hF a b hnz‖ ≤ C ∧
      ∀ x y, ‖nativeXiContour F a b 0 y-nativeXiContour F a b 0 x‖ ≤
        C*|stripCutControl B y-stripCutControl B x| := by
  have hc : ContinuousOn (fun s => F s/xi s) (RectangleBorder a b) :=
    hF.continuous.continuousOn.div
      deningerMeyerXi_entireRegular.differentiable.continuous.continuousOn hnz
  obtain ⟨M, hM⟩ := (isCompact_rectangleBorder a b).exists_bound_of_continuousOn hc
  obtain ⟨T, hT⟩ := (isCompact_rectangleBorder a b).exists_bound_of_continuousOn
    differentiable_thetaContourParameter.continuous.continuousOn
  exact ⟨_, nativeXiContour_control hF hnz (M := max M 0) (T := max T 0)
    (le_max_right _ _) (le_max_right _ _) (fun s hs =>
      ⟨(hM s hs).trans (le_max_left _ _), hstrip s hs, (hT s hs).trans (le_max_left _ _)⟩)⟩

end RHTower.PaperThetaEndpoint
