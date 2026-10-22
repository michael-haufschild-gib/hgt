import GaloisForLFunctions.RHTower.PaperThetaUniformCutControl
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerXiContourSource

/-! # Charge-free periods of the admitted theta family

The source contour cancels the full cut charge before any limiting operation.
Consequently its native period is independent of the arbitrary spatial cut.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HTGeometry

def thetaContourParameter (s : ℂ) : ℂ := -I*(s-1/2)

theorem differentiable_thetaContourParameter : Differentiable ℂ thetaContourParameter := by
  unfold thetaContourParameter
  fun_prop

@[simp] theorem XiC_thetaContourParameter (s : ℂ) : XiC (thetaContourParameter s) = xi s := by
  rw [XiC]
  congr 1
  have hi : I*(-I) = (1 : ℂ) := by rw [mul_neg, I_mul_I, neg_neg]
  calc
    1/2+thetaContourParameter s*I = 1/2+(s-1/2)*(I*(-I)) := by
      dsimp [thetaContourParameter]
      ring
    _ = s := by rw [hi]; ring

def nativeXiContour (F : ℂ → ℂ) (a b : ℂ) (cut x : ℝ) : ℂ :=
  -I*RectangleIntegral' (fun s => F s/xi s*cutQuotient (thetaContourParameter s) cut x) a b

theorem nativeXiContour_charge_zero {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a b : ℂ} (hnz : ∀ s ∈ RectangleBorder a b, xi s ≠ 0) (x : ℝ) :
    RectangleIntegral' (fun s => F s/xi s*cutCharge (thetaContourParameter s) x) a b = 0 := by
  let H : ℂ → ℂ := fun s =>
    F s*(-(I*thetaContourParameter s))*exp (-(I*thetaContourParameter s)*(x : ℂ)) /
      (thetaSource.k x : ℂ)
  have hH : Differentiable ℂ H := by
    dsimp [H, thetaContourParameter]
    fun_prop
  have he : RectangleIntegral' (fun s => F s/xi s*cutCharge (thetaContourParameter s) x) a b =
      RectangleIntegral' H a b := by
    apply RectangleIntegral'_congr
    intro s hs
    change F s/xi s*cutCharge (thetaContourParameter s) x = H s
    rw [cutCharge_eq, XiC_thetaContourParameter]
    dsimp [H]
    field_simp [hnz s hs]
  have hv := HolomorphicOn.vanishesOnRectangle (f := H) (z := a) (w := b)
    (U := univ) hH.differentiableOn (subset_univ _)
  rw [he, RectangleIntegral', hv, smul_zero]

theorem nativeXiContour_cut_independent {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a b : ℂ} (hnz : ∀ s ∈ RectangleBorder a b, xi s ≠ 0) (c d x : ℝ) :
    nativeXiContour F a b c x = nativeXiContour F a b d x := by
  have hA : ContinuousOn (fun s => F s/xi s) (RectangleBorder a b) :=
    hF.continuous.continuousOn.div
      deningerMeyerXi_entireRegular.differentiable.continuous.continuousOn hnz
  have hR : Continuous (fun s => flatQuotient (thetaContourParameter s) x) :=
    (differentiable_flatQuotient_parameter x).continuous.comp
      differentiable_thetaContourParameter.continuous
  have hL : Continuous (fun s => leftQuotient (thetaContourParameter s) x) :=
    (differentiable_flatQuotient_parameter (-x)).continuous.comp
      differentiable_thetaContourParameter.neg.continuous
  have he : RectangleIntegral' (fun s => F s/xi s*flatQuotient (thetaContourParameter s) x) a b =
      RectangleIntegral' (fun s => F s/xi s*leftQuotient (thetaContourParameter s) x) a b := by
    have hr : RectangleBorderIntegrable
        (fun s => F s/xi s*flatQuotient (thetaContourParameter s) x) a b :=
      (hA.mul hR.continuousOn).rectangleBorder_integrable
    have hl : RectangleBorderIntegrable
        (fun s => F s/xi s*leftQuotient (thetaContourParameter s) x) a b :=
      (hA.mul hL.continuousOn).rectangleBorder_integrable
    apply sub_eq_zero.mp
    rw [← rectangleIntegral'_sub hr hl]
    have hi : (fun s => F s/xi s*flatQuotient (thetaContourParameter s) x-
        F s/xi s*leftQuotient (thetaContourParameter s) x) =
        fun s => F s/xi s*cutCharge (thetaContourParameter s) x := by
      funext s
      dsimp [cutCharge]
      ring
    rw [hi]
    exact nativeXiContour_charge_zero hF hnz x
  have hcut (t : ℝ) : nativeXiContour F a b t x =
      -I*RectangleIntegral' (fun s => F s/xi s*flatQuotient (thetaContourParameter s) x) a b := by
    unfold nativeXiContour cutQuotient
    by_cases hx : x < t
    · simp only [if_pos hx]
      rw [he]
    · simp only [if_neg hx]
  exact (hcut c).trans (hcut d).symm

end RHTower.PaperThetaEndpoint
