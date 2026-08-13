import GaloisForLFunctions.RHTower.Sieve.MaynardOverweightCountExponents

/-!
# Route-T receiver scalar laws have no upper height-ratio boundary

The historical condition `mu ≤ 19/9` belongs to Maynard's published parameter range, not to the
receiver geometry.  The exact branch point is `mu * alpha = 2`: above it the first receiver grows
with `mu`; below it the negative-slope second receiver has enough room.  Consequently the small
optimizer cell and literal overweight cell laws remain valid for every `mu ≥ 4/3`, including the
full low-ordinate Perron range `mu ≤ 8`.
-/

noncomputable section
namespace RHTower.Sieve

/-- Upper-height-free form of the adjacent-optimizer receiver dichotomy. -/
theorem routeT_adjacent_optimizer_first_or_second_unbounded
    {mu alpha : ℝ} (_hmuLo : 4 / 3 ≤ mu)
    (halphaLo : 3 / 4 ≤ alpha)
    (halphaHi : alpha ≤ 1 - maynardLongGlobalAmplitudeDeficit) :
    2 * (1 - alpha) / alpha ≤ mu * (1 - alpha) ∨
      2 * (1 - alpha) / alpha ≤
        1 + mu * (1 + routeTGapMomentNu - 2 * alpha) := by
  let d := maynardLongGlobalAmplitudeDeficit
  let delta := 1 - alpha
  have hd : 0 < d := maynardLongGlobalAmplitudeDeficit_pos
  have halpha0 : 0 < alpha := lt_of_lt_of_le (by norm_num) halphaLo
  have hdelta : 0 ≤ delta := by dsimp only [delta, d] at halphaHi ⊢; linarith
  have hdDelta : d ≤ delta := by dsimp only [delta, d] at halphaHi ⊢; linarith
  by_cases hfirst : 2 ≤ mu * alpha
  · left
    have hratio : 2 / alpha ≤ mu :=
      (div_le_iff₀ halpha0).2 (by simpa [mul_comm] using hfirst)
    have hmul := mul_le_mul_of_nonneg_right hratio hdelta
    dsimp only [delta] at hmul ⊢
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul
  · right
    have hmualpha : mu * alpha ≤ 2 := le_of_not_ge hfirst
    have hmu : mu ≤ 2 / alpha :=
      (le_div_iff₀ halpha0).2 (by simpa [mul_comm] using hmualpha)
    let q := 1 + routeTGapMomentNu - 2 * alpha
    have hq : q < 0 := by
      dsimp only [q, routeTGapMomentNu, d]
      linarith
    have hqmul : (2 / alpha) * q ≤ mu * q :=
      mul_le_mul_of_nonpos_right hmu hq.le
    have hbase : 2 * delta / alpha ≤ 1 + (2 / alpha) * q := by
      have hid : 1 + (2 / alpha) * q = (3 * delta - d) / alpha := by
        dsimp only [q, routeTGapMomentNu, delta, d]
        field_simp [halpha0.ne']
        ring
      rw [hid]
      exact (div_le_div_iff_of_pos_right halpha0).2 (by linarith)
    dsimp only [delta] at hbase ⊢
    exact hbase.trans (by dsimp only [q] at hqmul; linarith)

/-- The fixed small-cell reserve also survives without any upper bound on `mu`. -/
theorem routeT_small_adjacent_optimizer_with_reserve_first_or_second_unbounded
    {mu alpha : ℝ} (hmuLo : 4 / 3 ≤ mu)
    (halphaLo : 3 / 4 ≤ alpha)
    (halphaHi : alpha ≤ 1 - maynardLongGlobalAmplitudeDeficit) :
    (19 / 10 : ℝ) * (1 - alpha) / alpha +
          maynardLongGlobalAmplitudeDeficit / 100 ≤ mu * (1 - alpha) ∨
      (19 / 10 : ℝ) * (1 - alpha) / alpha +
          maynardLongGlobalAmplitudeDeficit / 100 ≤
        1 + mu * (1 + routeTGapMomentNu - 2 * alpha) := by
  let d := maynardLongGlobalAmplitudeDeficit
  let delta := 1 - alpha
  have hd : 0 < d := maynardLongGlobalAmplitudeDeficit_pos
  have halpha0 : 0 < alpha := lt_of_lt_of_le (by norm_num) halphaLo
  have halphaOne : alpha ≤ 1 := by linarith
  have hdDelta : d ≤ delta := by dsimp only [delta, d] at halphaHi ⊢; linarith
  have hreserve : (19 / 10 : ℝ) * delta / alpha + d / 100 ≤
      2 * delta / alpha := by
    have halphaD : alpha * d ≤ delta := by
      have hmul := mul_le_mul_of_nonneg_right halphaOne hd.le
      have hmul' : alpha * d ≤ d := by simpa using hmul
      exact hmul'.trans hdDelta
    have hddiv : d ≤ delta / alpha :=
      (le_div_iff₀ halpha0).2 (by simpa [mul_comm] using halphaD)
    have hratio0 : 0 ≤ delta / alpha := by positivity
    have hddiv100 : d / 100 ≤ (delta / alpha) / 100 :=
      div_le_div_of_nonneg_right hddiv (by norm_num)
    calc
      (19 / 10 : ℝ) * delta / alpha + d / 100 ≤
          (19 / 10 : ℝ) * delta / alpha + (delta / alpha) / 100 := by
        linarith
      _ ≤ 2 * delta / alpha := by
        have hmain : (19 / 10 : ℝ) * (delta / alpha) +
            (delta / alpha) / 100 ≤ 2 * (delta / alpha) := by nlinarith
        convert hmain using 1 <;> ring
  rcases routeT_adjacent_optimizer_first_or_second_unbounded
      hmuLo halphaLo halphaHi with hfirst | hsecond
  · exact Or.inl (by simpa [delta, d] using hreserve.trans hfirst)
  · exact Or.inr (by simpa [delta, d] using hreserve.trans hsecond)

/-- Literal overweight packing scalar law on every height ratio.  Its proof uses only the split
`mu ≤ 207/100`; the published upper endpoint never enters. -/
theorem routeT_overweight_literal_cap_with_reserve_first_or_second_unbounded
    {mu alpha beta : ℝ}
    (hmuLo : 4 / 3 ≤ mu)
    (_halphaLo : 3 / 4 ≤ alpha) (halphaHi : alpha ≤ 983 / 1000)
    (hbetaHi : beta ≤ 1 + mu / 60) :
    beta * (2 - 2 * alpha) + maynardLongGlobalAmplitudeDeficit / 1000 ≤
          mu * (1 - alpha) ∨
      beta * (2 - 2 * alpha) + maynardLongGlobalAmplitudeDeficit / 1000 ≤
          1 + mu * (1 + routeTGapMomentNu - 2 * alpha) := by
  let d := maynardLongGlobalAmplitudeDeficit
  let delta := 1 - alpha
  have hd : 0 < d := maynardLongGlobalAmplitudeDeficit_pos
  have hdsmall : d < (1 / 1000000 : ℝ) :=
    maynardLongGlobalAmplitudeDeficit_lt_one_millionth
  have hmu0 : 0 ≤ mu := by linarith
  have hdeltaLo : (17 / 1000 : ℝ) ≤ delta := by
    dsimp only [delta]
    linarith
  have hdelta0 : 0 ≤ delta :=
    (by norm_num : (0 : ℝ) ≤ 17 / 1000).trans hdeltaLo
  have hscaled : beta * (2 * delta) ≤ (1 + mu / 60) * (2 * delta) :=
    mul_le_mul_of_nonneg_right hbetaHi (by positivity)
  by_cases hmuSplit : mu ≤ 207 / 100
  · right
    have hcoef0 : 0 ≤ 2 * mu - 2 - mu / 30 := by linarith
    have hdeltaCoef := mul_le_mul_of_nonneg_right hdeltaLo hcoef0
    have hmud : mu * d ≤ (207 / 100 : ℝ) * (1 / 1000000 : ℝ) := by
      calc
        mu * d ≤ (207 / 100 : ℝ) * d :=
          mul_le_mul_of_nonneg_right hmuSplit hd.le
        _ ≤ (207 / 100 : ℝ) * (1 / 1000000 : ℝ) :=
          mul_le_mul_of_nonneg_left hdsmall.le (by norm_num)
    dsimp only [routeTGapMomentNu]
    dsimp only [delta, d] at hscaled hdeltaCoef hmud ⊢
    linarith
  · left
    have hmuSplit' : 207 / 100 ≤ mu := le_of_not_ge hmuSplit
    have hcoefLo : (1 / 1000 : ℝ) ≤ mu - 2 - mu / 30 := by linarith
    have hmargin : (17 / 1000 : ℝ) * (1 / 1000) ≤
        delta * (mu - 2 - mu / 30) := by
      calc
        (17 / 1000 : ℝ) * (1 / 1000) ≤ delta * (1 / 1000) :=
          mul_le_mul_of_nonneg_right hdeltaLo (by norm_num)
        _ ≤ delta * (mu - 2 - mu / 30) :=
          mul_le_mul_of_nonneg_left hcoefLo hdelta0
    dsimp only [delta, d] at hscaled hmargin hdsmall ⊢
    linarith

/-- Full Perron low-ordinate interval lies inside the scalar laws; `mu ≤ 8` is recorded only to
match the analytic truncation and is not used by the receiver proof. -/
theorem routeT_fullPerronHeight_small_or_overweight_scalar
    {mu alpha beta : ℝ}
    (hmuLo : 19 / 9 ≤ mu) (_hmuHi : mu ≤ 8)
    (halphaLo : 3 / 4 ≤ alpha)
    (halphaEndpoint : alpha ≤ 1 - maynardLongGlobalAmplitudeDeficit)
    (halphaOverweight : alpha ≤ 983 / 1000)
    (hbetaHi : beta ≤ 1 + mu / 60) :
    (((19 / 10 : ℝ) * (1 - alpha) / alpha +
          maynardLongGlobalAmplitudeDeficit / 100 ≤ mu * (1 - alpha)) ∨
      ((19 / 10 : ℝ) * (1 - alpha) / alpha +
          maynardLongGlobalAmplitudeDeficit / 100 ≤
        1 + mu * (1 + routeTGapMomentNu - 2 * alpha))) ∧
    ((beta * (2 - 2 * alpha) + maynardLongGlobalAmplitudeDeficit / 1000 ≤
          mu * (1 - alpha)) ∨
      (beta * (2 - 2 * alpha) + maynardLongGlobalAmplitudeDeficit / 1000 ≤
        1 + mu * (1 + routeTGapMomentNu - 2 * alpha))) := by
  have hmu : 4 / 3 ≤ mu := by linarith
  exact ⟨routeT_small_adjacent_optimizer_with_reserve_first_or_second_unbounded
      hmu halphaLo halphaEndpoint,
    routeT_overweight_literal_cap_with_reserve_first_or_second_unbounded
      hmu halphaLo halphaOverweight hbetaHi⟩

end RHTower.Sieve
