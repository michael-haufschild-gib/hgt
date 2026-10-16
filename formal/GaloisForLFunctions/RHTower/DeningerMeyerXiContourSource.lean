import GaloisForLFunctions.RHTower.DeningerMeyerXiContourBounds

/-! # Literal source realization of Xi contour blocks

Each zero-free contour produces an actual all-weight source. Its full Xi
germs agree with the input inside and vanish outside, at every multiplicity.
-/

open Complex Set Filter Topology Metric
open HTGeometry GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

theorem deningerMeyerXiContour_entireRegular {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) {a b : ℂ} (ha : a.re = -1) (hb : b.re = 2)
    (hab : a.im ≤ b.im) (hnz : ∀ w ∈ RectangleBorder a b, xi w ≠ 0) :
    DeningerEntireMellinRegular (deningerMeyerXiContour F a b) := by
  have hd := differentiable_deningerMeyerXiContour hF (by rw [ha, hb]; norm_num) hab hnz
  have hc : ContinuousOn (fun w => F w/xi w) (RectangleBorder a b) :=
    hF.continuous.continuousOn.div
      deningerMeyerXi_entireRegular.differentiable.continuous.continuousOn hnz
  obtain ⟨M, hM⟩ := (GaloisForLFunctions.HTGeometry.isCompact_rectangleBorder a b)
    .exists_bound_of_continuousOn hc
  let T := |a.im|+|b.im|
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have haT : -T ≤ a.im := by dsimp [T]; linarith [neg_le_abs a.im, abs_nonneg b.im]
  have hbT : b.im ≤ T := by dsimp [T]; linarith [le_abs_self b.im, abs_nonneg a.im]
  intro α β
  refine ⟨fun z _ _ => hd z, fun c d _ _ K => ?_⟩
  obtain ⟨C, hC, hbound⟩ := deningerMeyerXiContour_weighted_bound (|c|+|d|) K
  refine ⟨C*(3+|b.im-a.im|)*|M| * (1+(T+1)^2)^K, fun z hzc hzd => ?_⟩
  apply (le_div_iff₀ (by positivity : 0 < (1+z.im^2)^K)).mpr
  apply hbound F hF a b ha hb hab T |M| hT haT hbT (abs_nonneg _) hnz
    (fun w hw => (hM w hw).trans (le_abs_self _)) z
  rw [abs_le]
  constructor <;> linarith [le_abs_self c, neg_le_abs c, le_abs_self d, neg_le_abs d,
    abs_nonneg c, abs_nonneg d]

/-- The projector is realized in the actual all-weight source. -/
def deningerMeyerXiContourSource (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (a b : ℂ) (ha : a.re = -1) (hb : b.re = 2) (hab : a.im ≤ b.im)
    (hnz : ∀ w ∈ RectangleBorder a b, xi w ≠ 0) : DeningerMeyerStrongLogTarget :=
  deningerMeyerInverseMellinSource (deningerMeyerXiContour F a b)
    (deningerMeyerXiContour_entireRegular hF ha hb hab hnz)

@[simp] theorem deningerMeyerXiContourSource_mellin
    (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (a b : ℂ) (ha : a.re = -1) (hb : b.re = 2) (hab : a.im ≤ b.im)
    (hnz : ∀ w ∈ RectangleBorder a b, xi w ≠ 0) (z : ℂ) :
    deningerMeyerStrongLogMellin (deningerMeyerXiContourSource F hF a b ha hb hab hnz) z =
      deningerMeyerXiContour F a b z :=
  deningerMeyerInverseMellinSource_mellin _ _

private theorem xi_contour_coefficient_analytic {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) {a b z : ℂ} (hab : a.re ≤ b.re) (hab' : a.im ≤ b.im)
    (hnz : ∀ w ∈ RectangleBorder a b, xi w ≠ 0) (hz : z ∉ RectangleBorder a b) :
    AnalyticAt ℂ (rectangleCauchyTransform (fun w => F w/xi w) a b) z := by
  have hA : ContinuousOn (fun w => F w/xi w) (RectangleBorder a b) :=
    hF.continuous.continuousOn.div
      deningerMeyerXi_entireRegular.differentiable.continuous.continuousOn hnz
  have hd : DifferentiableOn ℂ (rectangleCauchyTransform (fun w => F w/xi w) a b)
      (RectangleBorder a b)ᶜ := fun u hu =>
    (differentiableAt_rectangleCauchyTransform hab hab' hA hu).differentiableWithinAt
  exact hd.analyticAt
    ((GaloisForLFunctions.HTGeometry.isCompact_rectangleBorder a b).isClosed.isOpen_compl.mem_nhds hz)

private theorem xi_order_le_of_local_factor (rho : XiDivisorSupport)
    {G H : ℂ → ℂ} (hH : AnalyticAt ℂ H (rho : ℂ))
    (he : G =ᶠ[𝓝 (rho : ℂ)] (fun z => xi z*H z)) :
    (xiSupportMultiplicity rho : ℕ∞) ≤ analyticOrderAt G (rho : ℂ) := by
  calc
    (xiSupportMultiplicity rho : ℕ∞) = analyticOrderAt xi (rho : ℂ) :=
      (xi_analyticOrderAt_support rho).symm
    _ ≤ analyticOrderAt xi (rho : ℂ)+analyticOrderAt H (rho : ℂ) :=
      le_add_of_nonneg_right (zero_le _)
    _ = analyticOrderAt (xi*H) (rho : ℂ) :=
      (analyticOrderAt_mul
        (deningerMeyerXi_entireRegular.differentiable.analyticAt _) hH).symm
    _ = analyticOrderAt G (rho : ℂ) := (analyticOrderAt_congr he).symm

theorem deningerMeyerXiContour_inside_jet {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) {a b : ℂ} (hab : a.re ≤ b.re) (hab' : a.im ≤ b.im)
    (hnz : ∀ w ∈ RectangleBorder a b, xi w ≠ 0) (rho : XiDivisorSupport)
    (hρ : Rectangle a b ∈ 𝓝 (rho : ℂ)) (j : DeningerArithmeticJetIndex rho) :
    iteratedDeriv j (deningerMeyerXiContour F a b) (rho : ℂ) =
      iteratedDeriv j F (rho : ℂ) := by
  let H := rectangleCauchyTransform (fun w => F w/xi w) a b
  have hH := xi_contour_coefficient_analytic hF hab hab' hnz
    (not_mem_rectangleBorder_of_rectangle_mem_nhds hρ)
  have he : (fun z => deningerMeyerXiContour F a b z-F z) =ᶠ[𝓝 (rho : ℂ)]
      (fun z => xi z*(-H z)) := by
    filter_upwards [isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hρ)] with z hz
    rw [deningerMeyerXiContour, entireDividedDifferenceContour_inside hF
      deningerMeyerXi_entireRegular.differentiable.continuous.continuousOn hnz hab hab'
      (mem_interior_iff_mem_nhds.mp hz)]
    dsimp [H]
    ring
  have horder := xi_order_le_of_local_factor rho hH.neg he
  have hB := (differentiable_deningerMeyerXiContour hF hab hab' hnz).analyticAt (rho : ℂ)
  have hA := hF.analyticAt (rho : ℂ)
  have hz := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hB.sub hA)).mp
    horder j j.isLt
  change iteratedDeriv j (deningerMeyerXiContour F a b-F) (rho : ℂ) = 0 at hz
  rw [iteratedDeriv_sub hB.contDiffAt hA.contDiffAt, sub_eq_zero] at hz
  exact hz

theorem deningerMeyerXiContour_outside_jet {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) {a b : ℂ} (hab : a.re ≤ b.re) (hab' : a.im ≤ b.im)
    (hnz : ∀ w ∈ RectangleBorder a b, xi w ≠ 0) (rho : XiDivisorSupport)
    (hρ : (rho : ℂ) ∉ Rectangle a b) (j : DeningerArithmeticJetIndex rho) :
    iteratedDeriv j (deningerMeyerXiContour F a b) (rho : ℂ) = 0 := by
  let H := rectangleCauchyTransform (fun w => F w/xi w) a b
  have hH := xi_contour_coefficient_analytic hF hab hab' hnz
    (fun h => hρ (rectangleBorder_subset_rectangle a b h))
  have hclosed : IsClosed (Rectangle a b) := isClosed_uIcc.reProdIm isClosed_uIcc
  have he : deningerMeyerXiContour F a b =ᶠ[𝓝 (rho : ℂ)]
      (fun z => xi z*(-H z)) := by
    filter_upwards [hclosed.isOpen_compl.mem_nhds hρ] with z hz
    rw [deningerMeyerXiContour, entireDividedDifferenceContour_outside hF
      deningerMeyerXi_entireRegular.differentiable.continuous.continuousOn hnz hz]
    dsimp [H]
    ring
  have horder := xi_order_le_of_local_factor rho hH.neg he
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    ((differentiable_deningerMeyerXiContour hF hab hab' hnz).analyticAt (rho : ℂ))).mp
    horder j j.isLt

end
end RHTower
