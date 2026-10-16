import GaloisForLFunctions.RHTower.PaperThetaContourSpace
import GaloisForLFunctions.RHTower.PaperThetaMomentSeparation
import GaloisForLFunctions.RHTower.PaperThetaNativeMomentIdentity

/-! # Exact generator transport through Xi contour periods

The divided-difference commutator is the endpoint trace term in the native
Green equation. Their cancellation places every contour period in the range
of the actual compact Green operator, without differentiating a cut mode.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint
open HTGeometry GaloisForLFunctions.HTGeometry HedenmalmThetaSource

def nativeContourShift (F : ℂ → ℂ) (s : ℂ) : ℂ :=
  (thetaContourParameter s-I)*F s

theorem differentiable_nativeContourShift {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (nativeContourShift F) :=
  (differentiable_thetaContourParameter.sub_const I).mul hF

theorem xiContour_centered_shift {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a b : ℂ} (hnz : ∀ s ∈ RectangleBorder a b, xi s ≠ 0) (u : ℂ) :
    deningerMeyerXiContour (nativeContourShift F) a b u =
      (thetaContourParameter u-I)*deningerMeyerXiContour F a b u+
        I*xi u*RectangleIntegral' (fun s => F s/xi s) a b := by
  let A : ℂ → ℂ := fun s => F s/xi s
  let D : ℂ → ℂ := fun s => A s*dslope xi s u
  let c := thetaContourParameter u-I
  have hA : ContinuousOn A (RectangleBorder a b) :=
    hF.continuous.continuousOn.div
      deningerMeyerXi_entireRegular.differentiable.continuous.continuousOn hnz
  have hd : Continuous (fun s => dslope xi s u) := by
    simp_rw [dslope_symm xi _ u]
    exact (differentiable_entire_dslope deningerMeyerXi_entireRegular.differentiable u).continuous
  have hD : ContinuousOn D (RectangleBorder a b) := hA.mul hd.continuousOn
  have hG : ContinuousOn (fun s => nativeContourShift F s/xi s*dslope xi s u)
      (RectangleBorder a b) :=
    ((differentiable_nativeContourShift hF).continuous.continuousOn.div
      deningerMeyerXi_entireRegular.differentiable.continuous.continuousOn hnz).mul hd.continuousOn
  have hpoint (s : ℂ) (hs : s ∈ RectangleBorder a b) :
      nativeContourShift F s/xi s*dslope xi s u-c*D s =
        (I*xi u)*A s-I*F s := by
    have hds : (u-s)*dslope xi s u = xi u-xi s := by
      simpa only [smul_eq_mul] using sub_smul_dslope xi s u
    have hp : thetaContourParameter s-thetaContourParameter u = I*(u-s) := by
      dsimp [thetaContourParameter]
      ring
    calc
      _ = (thetaContourParameter s-thetaContourParameter u)*(F s/xi s)*dslope xi s u := by
        dsimp [nativeContourShift, c, D, A]
        ring
      _ = I*(F s/xi s)*((u-s)*dslope xi s u) := by rw [hp]; ring
      _ = I*(F s/xi s)*(xi u-xi s) := by rw [hds]
      _ = _ := by
        dsimp [A]
        field_simp [hnz s hs]
  have hz : RectangleIntegral' F a b = 0 := by
    have hv := HolomorphicOn.vanishesOnRectangle (f := F) (z := a) (w := b)
      (U := univ) hF.differentiableOn (subset_univ _)
    rw [RectangleIntegral', hv, smul_zero]
  have he : deningerMeyerXiContour (nativeContourShift F) a b u-
      c*deningerMeyerXiContour F a b u = I*xi u*RectangleIntegral' A a b := by
    have hcD : RectangleBorderIntegrable (fun s => c*D s) a b :=
      (continuousOn_const.mul hD).rectangleBorder_integrable
    have hIA : RectangleBorderIntegrable (fun s => (I*xi u)*A s) a b :=
      (continuousOn_const.mul hA).rectangleBorder_integrable
    have hIF : RectangleBorderIntegrable (fun s => I*F s) a b :=
      (continuous_const.mul hF.continuous).continuousOn.rectangleBorder_integrable
    change RectangleIntegral' (fun s => nativeContourShift F s/xi s*dslope xi s u) a b-
      c*RectangleIntegral' D a b = _
    rw [← rectangleIntegral'_const_mul, ← rectangleIntegral'_sub hG.rectangleBorder_integrable hcD]
    have hi := RectangleIntegral'_congr hpoint
    rw [hi, rectangleIntegral'_sub hIA hIF,
      rectangleIntegral'_const_mul, rectangleIntegral'_const_mul, hz, mul_zero, sub_zero]
  dsimp [c, A] at he
  linear_combination he

theorem nativeXiContour_shift_moment {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a b : ℂ} (hnz : ∀ s ∈ RectangleBorder a b, xi s ≠ 0) (u : ℂ) :
    boundedThetaMomentCLM (thetaContourParameter u)
        (nativeXiContourBCF (nativeContourShift F) (differentiable_nativeContourShift hF) a b hnz) =
      (thetaContourParameter u-I)*boundedThetaMomentCLM (thetaContourParameter u)
        (nativeXiContourBCF F hF a b hnz)-
      thetaContourParameter u*(I*RectangleIntegral' (fun s => F s/xi s) a b)*
        flatConnection (thetaContourParameter u) := by
  change (∫ x, flatCharDensity (thetaContourParameter u) x*
    nativeXiContour (nativeContourShift F) a b 0 x) = _
  rw [nativeXiContour_transform (differentiable_nativeContourShift hF) hnz,
    xiContour_centered_shift hF hnz]
  change _ = (thetaContourParameter u-I)*
    (∫ x, flatCharDensity (thetaContourParameter u) x*nativeXiContour F a b 0 x)-_
  rw [nativeXiContour_transform hF hnz, flatConnection_eq_all, XiC_thetaContourParameter]
  dsimp [thetaContourParameter]
  ring

/-- The literal compact Green operator transports the centered source shift
on each complete contour, including every enclosed multiplicity. -/
theorem nativeCompactResolvent_xiContour_shift {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a b : ℂ} (hnz : ∀ s ∈ RectangleBorder a b, xi s ≠ 0) :
    nativeCompactResolvent
        (nativeXiContourBCF (nativeContourShift F) (differentiable_nativeContourShift hF) a b hnz) =
      nativeXiContourBCF F hF a b hnz := by
  let f := nativeXiContourBCF F hF a b hnz
  let g := nativeXiContourBCF (nativeContourShift F) (differentiable_nativeContourShift hF) a b hnz
  let t := I*RectangleIntegral' (fun s => F s/xi s) a b
  have hm (z : ℂ) : boundedThetaMomentCLM z g =
      (z-I)*boundedThetaMomentCLM z f-z*t*flatConnection z := by
    have he : thetaContourParameter (1/2+I*z) = z := by
      dsimp [thetaContourParameter]
      ring_nf
      simp only [I_sq]
      ring
    simpa only [he] using nativeXiContour_shift_moment hF hnz (1/2+I*z)
  have ht : boundedResolventTrace nativeCompactParameter g = t := by
    have hk : flatConnection I ≠ 0 := by
      simpa only [nativeCompactParameter_val] using regular_connection_ne_zero nativeCompactParameter
    change -(nativeCompactParameter.val*flatConnection nativeCompactParameter)⁻¹*
      boundedThetaMomentCLM nativeCompactParameter g = t
    rw [nativeCompactParameter_val, hm]
    simp only [sub_self, zero_mul, zero_sub]
    field_simp [I_ne_zero, hk]
  apply boundedThetaMoment_ext
  intro x
  have he := nativeCompactResolvent_moment (x : ℂ) g
  rw [map_add, map_smul, ht, hm] at he
  have hn : I-(x : ℂ) ≠ 0 := by
    intro hz
    have hh := congrArg Complex.im hz
    norm_num at hh
  apply mul_left_cancel₀ hn
  change (I-(x : ℂ))*boundedThetaMomentCLM (x : ℂ) (nativeCompactResolvent g) =
    (I-(x : ℂ))*boundedThetaMomentCLM (x : ℂ) f
  linear_combination he

end RHTower.PaperThetaEndpoint
