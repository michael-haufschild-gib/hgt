import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilWeightedVolterraIdentity
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiSignedWindowMixture
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open Set MeasureTheory
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

def ccmSuzukiConnectedThirdGradeWeight (ω h : ℝ) : ℝ :=
  ccmGuinandWeilThirdGradeWeight h *
    shiftedEulerLogConnectedThirdMultiplier ω h

private theorem contDiffOn_ccmSuzukiConnectedThirdGradeWeight
    {ω : ℝ} (hω : ω ≠ 0) :
    ContDiffOn ℝ 1 (ccmSuzukiConnectedThirdGradeWeight ω) (Set.Ioi 0) := by
  intro h hh
  have hh0 : h ≠ 0 := hh.ne'
  have hωh : ω * h ≠ 0 := mul_ne_zero hω hh0
  let S : Set ℝ := Set.Ioi 0
  have hiden : ContDiffWithinAt ℝ 1 (fun x : ℝ => x) S h := by fun_prop
  have hweight : ContDiffWithinAt ℝ 1 (fun x : ℝ => 32 / x ^ 3) S h :=
    contDiffWithinAt_const.div (hiden.pow 3) (pow_ne_zero 3 hh0)
  have harg : ContDiffWithinAt ℝ 1 (fun x : ℝ => ω * x) S h := by fun_prop
  have hsinh : ContDiffWithinAt ℝ 1
      (fun x : ℝ => Real.sinh (ω * x)) S h := harg.sinh
  have hnum : ContDiffWithinAt ℝ 1
      (fun x : ℝ => 6 * (Real.sinh (ω * x) / (ω * x) - 1)) S h := by
    exact contDiffWithinAt_const.mul
      ((hsinh.div harg hωh).sub contDiffWithinAt_const)
  have hmult : ContDiffWithinAt ℝ 1
      (fun x : ℝ => 6 * (Real.sinh (ω * x) / (ω * x) - 1) /
        (ω * x) ^ (2 : ℕ)) S h :=
    hnum.div (harg.pow 2) (pow_ne_zero 2 hωh)
  exact hweight.mul hmult

/-- The literal cumulative prime-minus-polar source under a common connected Suzuki clock. -/
def ccmSuzukiConnectedThirdGradeCumulative (b ω H : ℝ) : ℝ :=
  ccmGuinandWeilPrimePolarWeightedWindow b H
    (ccmSuzukiConnectedThirdGradeWeight ω)

theorem ccmSuzukiConnectedWindow_eq_cesaroPrimitive
    {b H ω : ℝ} (hb : 0 < b) (hbH : b ≤ H) (hω : ω ≠ 0) :
    (∫ t in b..H, ccmSuzukiConnectedThirdGradeCumulative b ω t) =
      H * ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox b H ω := by
  let F := ccmSuzukiConnectedThirdGradeWeight ω
  have hH : 0 < H := hb.trans_le hbH
  have hSmooth := contDiffOn_ccmSuzukiConnectedThirdGradeWeight hω
  have hF : ∀ x ∈ Set.Icc b H, HasDerivAt F (deriv F x) x := by
    intro x hx
    have hxpos : x ∈ Set.Ioi (0 : ℝ) := hb.trans_le hx.1
    have hAt := (hSmooth x hxpos).contDiffAt (isOpen_Ioi.mem_nhds hxpos)
    exact hAt.differentiableAt_one.hasDerivAt
  have hF'cont : ContinuousOn (deriv F) (Set.Icc b H) := by
    have hD := hSmooth.continuousOn_deriv_of_isOpen isOpen_Ioi
      (by norm_num : (1 : WithTop ℕ∞) ≤ 1)
    exact hD.mono (by
      intro x hx
      exact hb.trans_le hx.1)
  have hmain := integral_ccmPrimePolarWeightedWindow_eq_triangular
    hb hbH hF hF'cont
  change (∫ t in b..H, ccmGuinandWeilPrimePolarWeightedWindow b t F) = _
  rw [ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox_eq_weightedWindow
    hω hb hbH]
  rw [← ccmGuinandWeilPrimePolarWeightedWindow_const_mul]
  calc
    _ = ccmGuinandWeilPrimePolarWeightedWindow b H (fun h => (H - h) * F h) :=
      hmain
    _ = ccmGuinandWeilPrimePolarWeightedWindow b H
          (fun h => H *
            (ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
              shiftedEulerLogConnectedThirdMultiplier ω h)) := by
        apply ccmGuinandWeilPrimePolarWeightedWindow_congr_on hbH
        · intro k hk hbk
          have hk0 : Real.log k ≠ 0 := (hb.trans hbk).ne'
          simp only [F, ccmSuzukiConnectedThirdGradeWeight,
            ccmGuinandWeilThirdGradeCesaroTriangularWeight]
          field_simp [hH.ne', hk0]
        · intro h hh
          have hh0 : h ≠ 0 := (hb.trans_le hh.1).ne'
          simp only [F, ccmSuzukiConnectedThirdGradeWeight,
            ccmGuinandWeilThirdGradeCesaroTriangularWeight]
          field_simp [hH.ne', hh0]


end

end RHTower
