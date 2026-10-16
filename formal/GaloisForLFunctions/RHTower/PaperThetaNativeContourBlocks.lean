import GaloisForLFunctions.RHTower.PaperThetaContourSpace
import GaloisForLFunctions.RHTower.PaperThetaBoundedResolvent
import GaloisForLFunctions.RHTower.DeningerMeyerXiContourSeries

/-! # Literal native blocks on the original Xi contour schedule -/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource

theorem thetaContourParameter_strip {s : ℂ} (h₁ : -1 ≤ s.re) (h₂ : s.re ≤ 2) :
    |(thetaContourParameter s).im| ≤ 3/2 := by
  have he : (thetaContourParameter s).im = 1/2-s.re := by
    simp [thetaContourParameter, mul_im]
  rw [he, abs_le]
  constructor <;> linarith

theorem thetaContourParameter_norm {s : ℂ} {T : ℝ}
    (h₁ : -1 ≤ s.re) (h₂ : s.re ≤ 2) (hi : |s.im| ≤ T) :
    ‖thetaContourParameter s‖ ≤ T+2 := by
  have he : (thetaContourParameter s).re = s.im := by
    simp [thetaContourParameter, mul_re]
  have hb := Complex.norm_le_abs_re_add_abs_im (thetaContourParameter s)
  rw [he] at hb
  linarith [thetaContourParameter_strip h₁ h₂]

def nativeXiBlock (S : DeningerMeyerXiContourSchedule) (F : ℂ → ℂ)
    (hF : Differentiable ℂ F) : ℕ → NativeContinuousSpace
  | 0 => nativeXiContourBCF F hF (deningerXiContourLeft (-S.height 0))
      (deningerXiContourRight (S.height 0)) S.central_nonzero
  | n+1 =>
      nativeXiContourBCF F hF (deningerXiContourLeft (S.height n))
        (deningerXiContourRight (S.height (n+1))) (S.upper_nonzero n) +
      nativeXiContourBCF F hF (deningerXiContourLeft (-S.height (n+1)))
        (deningerXiContourRight (-S.height n)) (S.lower_nonzero n)

theorem nativeXiBlock_transform (S : DeningerMeyerXiContourSchedule)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (n : ℕ) (u : ℂ) :
    boundedThetaMomentCLM (thetaContourParameter u) (nativeXiBlock S F hF n) =
      (I*(u-1/2)/(thetaSource.mass : ℂ))*S.xiBlock F n u := by
  have hp (a b : ℂ) (hnz : ∀ s ∈ RectangleBorder a b, xi s ≠ 0) :
      boundedThetaMomentCLM (thetaContourParameter u) (nativeXiContourBCF F hF a b hnz) =
        (I*(u-1/2)/(thetaSource.mass : ℂ))*deningerMeyerXiContour F a b u :=
    nativeXiContour_transform hF hnz 0 u
  cases n with
  | zero => exact hp _ _ S.central_nonzero
  | succ n =>
      change boundedThetaMomentCLM _ (_+_) = _
      rw [map_add, hp _ _ (S.upper_nonzero n), hp _ _ (S.lower_nonzero n)]
      exact (mul_add _ _ _).symm

theorem nativeXiBlock_of_entire_division (S : DeningerMeyerXiContourSchedule)
    {F H : ℂ → ℂ} (hF : Differentiable ℂ F) (hH : Differentiable ℂ H)
    (hdiv : ∀ s, F s = xi s*H s) (n : ℕ) : nativeXiBlock S F hF n = 0 := by
  apply BoundedContinuousFunction.ext
  intro x
  cases n with
  | zero => exact nativeXiContour_of_entire_division hH hdiv S.central_nonzero x
  | succ n =>
      change nativeXiContour F _ _ 0 x+nativeXiContour F _ _ 0 x = 0
      rw [nativeXiContour_of_entire_division hH hdiv (S.upper_nonzero n),
        nativeXiContour_of_entire_division hH hdiv (S.lower_nonzero n), add_zero]

theorem nativeXiBlock_central_control (S : DeningerMeyerXiContourSchedule)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
    ∃ C : ℝ, 0 ≤ C ∧ ‖nativeXiBlock S F hF 0‖ ≤ C ∧
      ∀ x y, ‖nativeXiBlock S F hF 0 y-nativeXiBlock S F hF 0 x‖ ≤
        C*|stripCutControl (3/2) y-stripCutControl (3/2) x| := by
  apply nativeXiContour_strip_control hF S.central_nonzero (3/2)
  intro s hs
  obtain ⟨h₁, h₂, _⟩ := deningerXiContour_border_geometry
    (by linarith [S.height_pos 0] : -S.height 0 ≤ S.height 0) hs
  exact thetaContourParameter_strip h₁ h₂

end RHTower.PaperThetaEndpoint
