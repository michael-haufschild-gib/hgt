import GaloisForLFunctions.RHTower.Sieve.MaynardOverweightCountExponents

/-!
# Shifted-amplitude scalar budget for middle Route T

Set `alpha0 = alpha - d/100000`, where `d` is the fixed long-factor amplitude deficit.  The shift
pays every fixed order-90 Huxley cost.  Its change in the adjacent-optimizer cap is much smaller
than the already proved `d/100` receiver reserve.
-/

noncomputable section
namespace RHTower.Sieve

/-- Reference amplitude used to pay fixed middle-strip Huxley costs. -/
def maynardMiddleReferenceAmplitude (alpha : ℝ) : ℝ :=
  alpha - maynardLongGlobalAmplitudeDeficit / 100000

theorem maynardMiddleReferenceAmplitude_range
    {alpha : ℝ} (halphaLo : 19 / 25 ≤ alpha) (halphaHi : alpha ≤ 997 / 1000) :
    3 / 4 ≤ maynardMiddleReferenceAmplitude alpha ∧
      maynardMiddleReferenceAmplitude alpha < 1 := by
  have hd : 0 < maynardLongGlobalAmplitudeDeficit := maynardLongGlobalAmplitudeDeficit_pos
  have hdsmall : maynardLongGlobalAmplitudeDeficit < (1 / 1000000 : ℝ) :=
    maynardLongGlobalAmplitudeDeficit_lt_one_millionth
  dsimp only [maynardMiddleReferenceAmplitude]
  constructor <;> linarith

/-- The shifted adjacent-optimizer cap, plus `d/1000` for all remaining fixed costs, still fits
one of Route T's first two receiver alternatives. -/
theorem routeT_middle_shifted_adjacent_with_cost_first_or_second
    {mu alpha : ℝ}
    (hmuLo : 4 / 3 ≤ mu) (hmuHi : mu ≤ 19 / 9)
    (halphaLo : 19 / 25 ≤ alpha) (halphaHi : alpha ≤ 997 / 1000) :
    2 * (1 - maynardMiddleReferenceAmplitude alpha) /
          maynardMiddleReferenceAmplitude alpha +
          maynardLongGlobalAmplitudeDeficit / 1000 ≤ mu * (1 - alpha) ∨
      2 * (1 - maynardMiddleReferenceAmplitude alpha) /
          maynardMiddleReferenceAmplitude alpha +
          maynardLongGlobalAmplitudeDeficit / 1000 ≤
        1 + mu * (1 + routeTGapMomentNu - 2 * alpha) := by
  let d : ℝ := maynardLongGlobalAmplitudeDeficit
  let alpha0 : ℝ := maynardMiddleReferenceAmplitude alpha
  have hd : 0 < d := maynardLongGlobalAmplitudeDeficit_pos
  have halphaThree : 3 / 4 ≤ alpha := by linarith
  have ha0Range := maynardMiddleReferenceAmplitude_range halphaLo halphaHi
  have ha0pos : 0 < alpha0 := lt_of_lt_of_le (by norm_num) ha0Range.1
  have halphapos : 0 < alpha := lt_of_lt_of_le (by norm_num) halphaThree
  have ha0le : alpha0 ≤ alpha := by
    dsimp only [alpha0, maynardMiddleReferenceAmplitude, d]
    linarith
  have hprod : (9 / 16 : ℝ) ≤ alpha * alpha0 := by
    have := mul_le_mul halphaThree ha0Range.1 (by norm_num : (0 : ℝ) ≤ 3 / 4)
      halphapos.le
    norm_num at this ⊢
    exact this
  have hshift : alpha - alpha0 = d / 100000 := by
    dsimp only [alpha0, maynardMiddleReferenceAmplitude, d]
    ring
  have hfrac : 2 * (alpha - alpha0) / (alpha * alpha0) ≤ d / 1000 := by
    rw [div_le_iff₀ (mul_pos halphapos ha0pos)]
    rw [hshift]
    have hmul := mul_le_mul_of_nonneg_left hprod hd.le
    nlinarith
  have hcapIdentity :
      2 * (1 - alpha0) / alpha0 =
        2 * (1 - alpha) / alpha +
          2 * (alpha - alpha0) / (alpha * alpha0) := by
    field_simp [halphapos.ne', ha0pos.ne']
    ring
  have hcap :
      2 * (1 - alpha0) / alpha0 + d / 1000 ≤
        2 * (1 - alpha) / alpha + d / 100 := by
    rw [hcapIdentity]
    nlinarith
  rcases routeT_adjacent_optimizer_with_reserve_of_amplitude_le_997
      hmuLo hmuHi halphaThree halphaHi with hfirst | hsecond
  · left
    simpa only [alpha0, d] using hcap.trans hfirst
  · right
    simpa only [alpha0, d] using hcap.trans hsecond

end RHTower.Sieve
