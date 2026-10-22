import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilActualDampedEnvelope

open Set MeasureTheory
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

def ccmThirdGradeExponentialClockCumulative (b a H : ℝ) : ℝ :=
  ccmGuinandWeilPrimePolarWeightedWindow b H
    (fun h => Real.exp (a * h) * ccmGuinandWeilThirdGradeWeight h)

private theorem expClockDamped_integral_eq_literal
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) (a : ℝ) :
    Real.exp ((1 + a) * H) *
      (∫ h in Ioc (0 : ℝ) H,
        Real.exp (-((1 + a) * (H - h))) * ccmThirdGradeDampedSource b h) =
      ∫ h in b..H,
        Real.exp (a * h) * ccmGuinandWeilThirdGradeCumulativeMeasurable b h := by
  rw [← MeasureTheory.integral_const_mul]
  have hpoint (h : ℝ) :
      Real.exp ((1 + a) * H) *
          (Real.exp (-((1 + a) * (H - h))) * ccmThirdGradeDampedSource b h) =
        Set.indicator (Set.Ioi b)
          (fun h => Real.exp (a * h) *
            ccmGuinandWeilThirdGradeCumulativeMeasurable b h) h := by
    by_cases hbh : b < h
    · simp only [ccmThirdGradeDampedSource, if_pos hbh]
      change _ = if h ∈ Set.Ioi b then
          Real.exp (a * h) * ccmGuinandWeilThirdGradeCumulativeMeasurable b h else 0
      have hhmem : h ∈ Set.Ioi b := hbh
      rw [if_pos hhmem]
      rw [show Real.exp ((1 + a) * H) *
        (Real.exp (-((1 + a) * (H - h))) *
          (Real.exp (-h) * ccmGuinandWeilThirdGradeCumulativeMeasurable b h)) =
        Real.exp ((1 + a) * H + -((1 + a) * (H - h)) + -h) *
          ccmGuinandWeilThirdGradeCumulativeMeasurable b h by
            rw [Real.exp_add, Real.exp_add]; ring]
      congr 1
      ring
    · simp [ccmThirdGradeDampedSource, hbh, Set.indicator_of_notMem]
  rw [setIntegral_congr_fun measurableSet_Ioc (fun h _ => hpoint h),
    setIntegral_indicator measurableSet_Ioi]
  have hset : Set.Ioc (0 : ℝ) H ∩ Set.Ioi b = Set.Ioc b H := by
    ext h
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · intro hmem
      exact ⟨hmem.2, hmem.1.2⟩
    · intro hmem
      exact ⟨⟨hb.trans hmem.1, hmem.2⟩, hmem.1⟩
  rw [hset, ← intervalIntegral.integral_of_le hbH]

theorem ccmThirdGradeExponentialClockCumulative_eq_expClockOnDampedSource
    {b H : ℝ} (hb : 0 < b) (hbh : b < H) (a : ℝ) :
    ccmThirdGradeExponentialClockCumulative b a H =
      expClockOnDampedSource a (ccmThirdGradeDampedSource b) H := by
  let F := ccmGuinandWeilThirdGradeWeight
  let F' := ccmGuinandWeilThirdGradeWeightDeriv
  let m : ℝ → ℝ := fun h => Real.exp (a * h)
  let m' : ℝ → ℝ := fun h => a * Real.exp (a * h)
  have hbH : b ≤ H := hbh.le
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
  have hm : ∀ x ∈ Set.Icc b H, HasDerivAt m (m' x) x := by
    intro x hx
    have harg : HasDerivAt (fun t : ℝ => a * t) a x := by
      simpa using (hasDerivAt_id x).const_mul a
    simpa only [m, m', mul_comm] using harg.exp
  have hm'cont : ContinuousOn m' (Set.Icc b H) := by
    fun_prop
  have hmAC : AbsolutelyContinuousOnInterval m b H := by
    have hmcd : ContDiff ℝ 1 m := by fun_prop
    exact hmcd.contDiffOn.absolutelyContinuousOnInterval
  have hmain := ccmPrimePolarWeightedWindow_clockCommutator
    hb hbH hF hF'cont hm hm'cont hmAC
  have hfirst : Real.exp ((1 + a) * H) * ccmThirdGradeDampedSource b H =
      Real.exp (a * H) * ccmGuinandWeilThirdGradeCumulativeMeasurable b H := by
    simp only [ccmThirdGradeDampedSource, if_pos hbh]
    rw [← mul_assoc, ← Real.exp_add]
    congr 1
    ring
  unfold ccmThirdGradeExponentialClockCumulative expClockOnDampedSource
  rw [hmain]
  have hint := expClockDamped_integral_eq_literal hb hbH a
  have hInt :
      (∫ t in b..H, m' t * ccmGuinandWeilPrimePolarWeightedWindow b t F) =
        a * ∫ t in b..H,
          Real.exp (a * t) * ccmGuinandWeilThirdGradeCumulativeMeasurable b t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc b H := by simpa only [Set.uIcc_of_le hbH] using ht
    change m' t * ccmGuinandWeilPrimePolarWeightedWindow b t F =
      a * (Real.exp (a * t) * ccmGuinandWeilThirdGradeCumulativeMeasurable b t)
    rw [ccmGuinandWeilThirdGradeCumulativeMeasurable_eq_primePolar ht'.1]
    dsimp [m']
    ring
  rw [← ccmGuinandWeilThirdGradeCumulativeMeasurable_eq_primePolar hbH, hInt]
  change Real.exp (a * H) * ccmGuinandWeilThirdGradeCumulativeMeasurable b H -
      a * (∫ t in b..H,
        Real.exp (a * t) * ccmGuinandWeilThirdGradeCumulativeMeasurable b t) = _
  rw [← hfirst, ← hint]
  ring

end

end RHTower
