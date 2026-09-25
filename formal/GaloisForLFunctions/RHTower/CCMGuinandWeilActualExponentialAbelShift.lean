import GaloisForLFunctions.RHTower.CCMGuinandWeilActualExponentialClock

open Set MeasureTheory Complex
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

private theorem integral_Ioi_zeroBelow_eq_Ioi
    {b : ℝ} (hb : 0 < b) {f : ℝ → ℂ}
    (hf : ∀ h : ℝ, h ≤ b → f h = 0) :
    (∫ h in Set.Ioi (0 : ℝ), f h) = ∫ h in Set.Ioi b, f h := by
  calc
    _ = ∫ h in Set.Ioi (0 : ℝ), (Set.Ioi b).indicator f h := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro h hh
      by_cases hbh : b < h
      · rw [Set.indicator_of_mem (show h ∈ Set.Ioi b from hbh)]
      · rw [Set.indicator_of_notMem (show h ∉ Set.Ioi b from hbh)]
        exact hf h (le_of_not_gt hbh)
    _ = ∫ h in Set.Ioi (0 : ℝ) ∩ Set.Ioi b, f h := by
      rw [setIntegral_indicator measurableSet_Ioi]
    _ = _ := by
      have hset : Set.Ioi (0 : ℝ) ∩ Set.Ioi b = Set.Ioi b := by
        ext h
        simp only [Set.mem_inter_iff, Set.mem_Ioi]
        exact ⟨fun hh => hh.2, fun hh => ⟨hb.trans hh, hh⟩⟩
      rw [hset]

private theorem ccmThirdGradeDampedSource_zeroBelow
    {b : ℝ} (h : ℝ) (hh : h ≤ b) : ccmThirdGradeDampedSource b h = 0 := by
  simp [ccmThirdGradeDampedSource, not_lt.mpr hh]

private theorem expClockDamped_zeroBelow
    {b a H : ℝ} (hH : H ≤ b) :
    expClockOnDampedSource a (ccmThirdGradeDampedSource b) H = 0 := by
  have hinner : (∫ h in Set.Ioc (0 : ℝ) H,
      Real.exp (-((1 + a) * (H - h))) * ccmThirdGradeDampedSource b h) = 0 := by
    calc
      _ = ∫ h in Set.Ioc (0 : ℝ) H, (0 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro h hh
        change Real.exp (-((1 + a) * (H - h))) *
          ccmThirdGradeDampedSource b h = (0 : ℝ)
        rw [ccmThirdGradeDampedSource_zeroBelow h (hh.2.trans hH)]
        ring
      _ = 0 := by simp
  simp [expClockOnDampedSource, ccmThirdGradeDampedSource_zeroBelow H hH, hinner]

/-- On the safe Euler half-plane, Abel transformation of the actual one-sided clocked
completed source is horizontal translation of the actual zero-clock Abel transform. -/
theorem ccmThirdGradeExponentialClock_abel_shift
    {b a : ℝ} (hb : 0 < b) (ha : 0 ≤ a)
    {u : ℂ} (hu : 1 + a < u.re) :
    ccmAbelCumulativeSourceContinuation
        (ccmThirdGradeExponentialClockCumulative b a) b u =
      ccmAbelCumulativeSourceContinuation
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b (u - (a : ℂ)) := by
  let φ := ccmThirdGradeDampedSource b
  let z : ℂ := u - (1 + a : ℝ)
  have hφmeas : Measurable φ := measurable_ccmThirdGradeDampedSource hb
  have hφbound := ccmThirdGradeDampedSource_linearBound hb
  have hshift := expClockOnDampedSource_abel_shift ha hφmeas hφbound hu
  have hleft : (∫ H in Set.Ioi b,
      Complex.exp (-(u * (H : ℂ))) *
        (ccmThirdGradeExponentialClockCumulative b a H : ℂ)) =
      ∫ H in Set.Ioi (0 : ℝ),
        Complex.exp (-(u * (H : ℂ))) * (expClockOnDampedSource a φ H : ℂ) := by
    rw [integral_Ioi_zeroBelow_eq_Ioi hb (f := fun H =>
        Complex.exp (-(u * (H : ℂ))) * (expClockOnDampedSource a φ H : ℂ))
      (by intro H hH; rw [expClockDamped_zeroBelow hH]; simp)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro H hH
    simp only [ccmThirdGradeExponentialClockCumulative_eq_expClockOnDampedSource
      hb (show b < H from hH) a, φ]
  have hright : (∫ H in Set.Ioi b,
      Complex.exp (-((u - (a : ℂ)) * (H : ℂ))) *
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b H : ℂ)) =
      ∫ H in Set.Ioi (0 : ℝ),
        Complex.exp (-(z * (H : ℂ))) * (φ H : ℂ) := by
    rw [integral_Ioi_zeroBelow_eq_Ioi hb (f := fun H =>
      Complex.exp (-(z * (H : ℂ))) * (φ H : ℂ))
      (by intro H hH; simp [φ, ccmThirdGradeDampedSource, not_lt.mpr hH])]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro H hH
    have hexp : Complex.exp (-(z * (H : ℂ))) *
        (Real.exp (-H) : ℂ) =
          Complex.exp (-((u - (a : ℂ)) * (H : ℂ))) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      dsimp [z]
      push_cast
      ring
    change Complex.exp (-((u - (a : ℂ)) * (H : ℂ))) *
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b H : ℂ) =
      Complex.exp (-(z * (H : ℂ))) * (φ H : ℂ)
    dsimp [φ, ccmThirdGradeDampedSource]
    rw [if_pos (show b < H from hH)]
    simp only [Complex.ofReal_mul]
    rw [← mul_assoc, hexp]
  unfold ccmAbelCumulativeSourceContinuation ccmAbelLaplaceTail
  simp only [neg_mul] at hleft hright hshift ⊢
  rw [hleft, hright]
  simpa only [z, φ] using hshift

end

end RHTower
