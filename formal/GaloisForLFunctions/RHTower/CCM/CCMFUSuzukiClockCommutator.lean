import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilClockCommutator
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiClockVolterraBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open Set MeasureTheory
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

private theorem contDiffOn_shiftedEulerLogConnectedThirdMultiplier_pos
    {ω : ℝ} (hω : ω ≠ 0) :
    ContDiffOn ℝ 1 (shiftedEulerLogConnectedThirdMultiplier ω) (Set.Ioi 0) := by
  intro h hh
  have hh0 : h ≠ 0 := hh.ne'
  have hωh : ω * h ≠ 0 := mul_ne_zero hω hh0
  let S : Set ℝ := Set.Ioi 0
  have harg : ContDiffWithinAt ℝ 1 (fun x : ℝ => ω * x) S h := by fun_prop
  have hsinh : ContDiffWithinAt ℝ 1
      (fun x : ℝ => Real.sinh (ω * x)) S h := harg.sinh
  have hnum : ContDiffWithinAt ℝ 1
      (fun x : ℝ => 6 * (Real.sinh (ω * x) / (ω * x) - 1)) S h := by
    exact contDiffWithinAt_const.mul
      ((hsinh.div harg hωh).sub contDiffWithinAt_const)
  exact hnum.div (harg.pow 2) (pow_ne_zero 2 hωh)

/-- The actual connected Suzuki cumulative source is the smooth-clock Volterra
commutator of the actual zero-clock completed third-grade source. -/
theorem ccmSuzukiConnectedThirdGradeCumulative_eq_clockCommutator
    {b H ω : ℝ} (hb : 0 < b) (hbH : b ≤ H) (hω : ω ≠ 0) :
    ccmSuzukiConnectedThirdGradeCumulative b ω H =
      shiftedEulerLogConnectedThirdMultiplier ω H *
        ccmGuinandWeilThirdGradeCumulativeMeasurable b H -
        ∫ t in b..H,
          deriv (shiftedEulerLogConnectedThirdMultiplier ω) t *
            ccmGuinandWeilThirdGradeCumulativeMeasurable b t := by
  let m := shiftedEulerLogConnectedThirdMultiplier ω
  let F := ccmGuinandWeilThirdGradeWeight
  let F' := ccmGuinandWeilThirdGradeWeightDeriv
  have hF : ∀ x ∈ Set.Icc b H, HasDerivAt F (F' x) x := by
    intro x hx
    exact hasDerivAt_ccmGuinandWeilThirdGradeWeight
      (ne_of_gt (hb.trans_le hx.1))
  have hF'cont : ContinuousOn F' (Set.Icc b H) := by
    intro x hx
    change ContinuousWithinAt ccmGuinandWeilThirdGradeWeightDeriv (Set.Icc b H) x
    unfold ccmGuinandWeilThirdGradeWeightDeriv
    exact (continuousAt_const.div (continuousAt_id.pow 4)
      (pow_ne_zero 4 (ne_of_gt (hb.trans_le hx.1)))).continuousWithinAt
  have hMcd := contDiffOn_shiftedEulerLogConnectedThirdMultiplier_pos hω
  have hm : ∀ x ∈ Set.Icc b H, HasDerivAt m (deriv m x) x := by
    intro x hx
    have hxpos : x ∈ Set.Ioi (0 : ℝ) := hb.trans_le hx.1
    have hAt := (hMcd x hxpos).contDiffAt (isOpen_Ioi.mem_nhds hxpos)
    exact hAt.differentiableAt_one.hasDerivAt
  have hm'cont : ContinuousOn (deriv m) (Set.Icc b H) := by
    have hD := hMcd.continuousOn_deriv_of_isOpen isOpen_Ioi
      (by norm_num : (1 : WithTop ℕ∞) ≤ 1)
    exact hD.mono (by intro x hx; exact hb.trans_le hx.1)
  have hmAC : AbsolutelyContinuousOnInterval m b H := by
    have hmIcc : ContDiffOn ℝ 1 m (Set.Icc b H) :=
      hMcd.mono (by intro x hx; exact hb.trans_le hx.1)
    have hmIccU : ContDiffOn ℝ 1 m (Set.uIcc b H) := by
      simpa only [Set.uIcc_of_le hbH] using hmIcc
    exact hmIccU.absolutelyContinuousOnInterval
  have hmain := ccmPrimePolarWeightedWindow_clockCommutator
    hb hbH hF hF'cont hm hm'cont hmAC
  have hleft : ccmSuzukiConnectedThirdGradeCumulative b ω H =
      ccmGuinandWeilPrimePolarWeightedWindow b H (fun h => m h * F h) := by
    unfold ccmSuzukiConnectedThirdGradeCumulative
    apply ccmGuinandWeilPrimePolarWeightedWindow_congr_on hbH
    · intro k hk hbk
      simp only [m, F, ccmSuzukiConnectedThirdGradeWeight]
      ring
    · intro h hh
      simp only [m, F, ccmSuzukiConnectedThirdGradeWeight]
      ring
  rw [hleft, hmain,
    ← ccmGuinandWeilThirdGradeCumulativeMeasurable_eq_primePolar hbH]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc b H := by simpa only [Set.uIcc_of_le hbH] using ht
  change deriv m t * ccmGuinandWeilPrimePolarWeightedWindow b t F =
    deriv m t * ccmGuinandWeilThirdGradeCumulativeMeasurable b t
  rw [ccmGuinandWeilThirdGradeCumulativeMeasurable_eq_primePolar ht'.1]

end

end RHTower
