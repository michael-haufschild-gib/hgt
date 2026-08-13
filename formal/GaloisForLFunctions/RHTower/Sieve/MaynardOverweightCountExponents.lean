import GaloisForLFunctions.RHTower.Sieve.MaynardAdjacentOptimizerRaise

/-!
# Route-T count margin for the unique overweight spill cell

The capped sub-height packing can leave one cell of exponent below `1 + mu/120`.  Its distinguished
near-height zeta/log atom admits a third-derivative pointwise deficit, so this cell only survives
when `alpha <= 99/100`.  On that fixed strip, even the unraised Huxley width exponent has a uniform
margin inside Route T's first or second alternative.
-/

noncomputable section
namespace RHTower.Sieve

theorem maynardLongGlobalAmplitudeDeficit_lt_one_millionth :
    maynardLongGlobalAmplitudeDeficit < (1 / 1000000 : ℝ) := by
  norm_num [maynardLongGlobalAmplitudeDeficit, maynardDerivativeDeficit]

set_option maxHeartbeats 300000 in
/-- **Overweight spill-cell scalar law.**  The split `mu=1019/500` lies in the overlap where
both receiver alternatives have positive room.  The explicit `d/100` reserve pays every fixed
coloring and coefficient-energy loss. -/
theorem routeT_overweight_huxley_with_reserve_first_or_second
    {mu alpha beta : ℝ}
    (hmuLo : 4 / 3 ≤ mu) (hmuHi : mu ≤ 19 / 9)
    (halphaLo : 3 / 4 ≤ alpha) (halphaHi : alpha ≤ 99 / 100)
    (hbetaHi : beta ≤ 1 + mu / 120) :
    beta * (2 - 2 * alpha) + maynardLongGlobalAmplitudeDeficit / 100 ≤
          mu * (1 - alpha) ∨
      beta * (2 - 2 * alpha) + maynardLongGlobalAmplitudeDeficit / 100 ≤
          1 + mu * (1 + routeTGapMomentNu - 2 * alpha) := by
  let d := maynardLongGlobalAmplitudeDeficit
  let delta := 1 - alpha
  have hd : 0 < d := maynardLongGlobalAmplitudeDeficit_pos
  have hdsmall : d < (1 / 1000000 : ℝ) :=
    maynardLongGlobalAmplitudeDeficit_lt_one_millionth
  have hmu0 : 0 ≤ mu := by linarith
  have hdeltaLo : (1 / 100 : ℝ) ≤ delta := by
    dsimp only [delta]
    linarith
  have hdelta0 : 0 ≤ delta := hdeltaLo.trans' (by norm_num)
  have hscaled : beta * (2 * delta) ≤ (1 + mu / 120) * (2 * delta) :=
    mul_le_mul_of_nonneg_right hbetaHi (by positivity)
  by_cases hmuSplit : mu ≤ 1019 / 500
  · right
    have hcoef : 0 ≤ 2 * mu - 2 - mu / 60 := by linarith
    have hdeltaCoef := mul_le_mul_of_nonneg_right hdeltaLo hcoef
    have hmud : mu * d ≤ (1019 / 500 : ℝ) * (1 / 1000000 : ℝ) := by
      calc
        mu * d ≤ (1019 / 500 : ℝ) * d :=
          mul_le_mul_of_nonneg_right hmuSplit hd.le
        _ ≤ (1019 / 500 : ℝ) * (1 / 1000000 : ℝ) :=
          mul_le_mul_of_nonneg_left hdsmall.le (by norm_num)
    dsimp only [routeTGapMomentNu]
    dsimp only [delta, d] at hscaled hdeltaCoef hmud ⊢
    linarith
  · left
    have hmuSplit' : 1019 / 500 ≤ mu := le_of_not_ge hmuSplit
    have hcoefLo : (121 / 30000 : ℝ) ≤ mu - 2 - mu / 60 := by
      linarith
    have hcoef0 : 0 ≤ mu - 2 - mu / 60 := (by norm_num : (0 : ℝ) ≤ 121 / 30000).trans hcoefLo
    have hmargin : (1 / 100 : ℝ) * (121 / 30000) ≤
        delta * (mu - 2 - mu / 60) := by
      calc
        (1 / 100 : ℝ) * (121 / 30000) ≤ delta * (121 / 30000) :=
          mul_le_mul_of_nonneg_right hdeltaLo (by norm_num)
        _ ≤ delta * (mu - 2 - mu / 60) :=
          mul_le_mul_of_nonneg_left hcoefLo hdelta0
    dsimp only [delta, d] at hscaled hmargin hdsmall ⊢
    linarith

set_option maxHeartbeats 300000 in
/-- **Literal overweight packing law.**  The actual witnessed packing has the larger cap
`beta < 1 + mu/60`.  Its order-three factor deficit confines this branch to `alpha <= 983/1000`.
Those two sharp facts exactly restore overlap between Route T's receivers; `mu = 207/100` is a
rational interior split with enough room for the fixed analytic cost. -/
theorem routeT_overweight_literal_cap_with_reserve_first_or_second
    {mu alpha beta : ℝ}
    (hmuLo : 4 / 3 ≤ mu) (hmuHi : mu ≤ 19 / 9)
    (halphaLo : 3 / 4 ≤ alpha) (halphaHi : alpha ≤ 983 / 1000)
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
  have hdelta0 : 0 ≤ delta := (by norm_num : (0 : ℝ) ≤ 17 / 1000).trans hdeltaLo
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

/-- Away from the last `3/1000` of the amplitude interval, the exact adjacent-power Huxley cap
has enough receiver room to pay the fixed `d/100` coefficient loss. -/
theorem routeT_adjacent_optimizer_with_reserve_of_amplitude_le_997
    {mu alpha : ℝ}
    (hmuLo : 4 / 3 ≤ mu) (_hmuHi : mu ≤ 19 / 9)
    (halphaLo : 3 / 4 ≤ alpha) (halphaHi : alpha ≤ 997 / 1000) :
    2 * (1 - alpha) / alpha + maynardLongGlobalAmplitudeDeficit / 100 ≤
          mu * (1 - alpha) ∨
      2 * (1 - alpha) / alpha + maynardLongGlobalAmplitudeDeficit / 100 ≤
          1 + mu * (1 + routeTGapMomentNu - 2 * alpha) := by
  let d := maynardLongGlobalAmplitudeDeficit
  let delta := 1 - alpha
  let q := 1 + routeTGapMomentNu - 2 * alpha
  have hd : 0 < d := maynardLongGlobalAmplitudeDeficit_pos
  have hdsmall : d < (1 / 1000000 : ℝ) :=
    maynardLongGlobalAmplitudeDeficit_lt_one_millionth
  have halpha0 : 0 < alpha := lt_of_lt_of_le (by norm_num) halphaLo
  have halphaOne : alpha ≤ 1 := by linarith
  have hdeltaLo : (3 / 1000 : ℝ) ≤ delta := by
    dsimp only [delta]
    linarith
  have hdelta0 : 0 ≤ delta := (by norm_num : (0 : ℝ) ≤ 3 / 1000).trans hdeltaLo
  have hqnonpos : q ≤ 0 := by
    dsimp only [q, routeTGapMomentNu]
    linarith
  by_cases hfirst : 2 + delta / 100 ≤ mu * alpha
  · left
    have hmargin : delta * delta / (100 * alpha) ≤
        mu * delta - 2 * delta / alpha := by
      have hgap : delta / 100 ≤ mu * alpha - 2 := by linarith
      have hscale := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ delta / alpha)
      calc
        delta * delta / (100 * alpha) = (delta / alpha) * (delta / 100) := by ring
        _ ≤ (delta / alpha) * (mu * alpha - 2) := hscale
        _ = mu * delta - 2 * delta / alpha := by field_simp [halpha0.ne']
    have hfixed : d / 100 ≤ delta * delta / (100 * alpha) := by
      have hdeltaSq : (9 / 1000000 : ℝ) ≤ delta * delta := by nlinarith
      have halphaD : alpha * d ≤ d := by
        have hmul := mul_le_mul_of_nonneg_right halphaOne hd.le
        simpa using hmul
      have hcore : d ≤ delta * delta / alpha := by
        rw [le_div_iff₀ halpha0]
        linarith
      calc
        d / 100 ≤ (delta * delta / alpha) / 100 :=
          div_le_div_of_nonneg_right hcore (by norm_num)
        _ = delta * delta / (100 * alpha) := by ring
    dsimp only [delta, d] at hmargin hfixed ⊢
    linarith
  · right
    have hmualpha : mu * alpha < 2 + delta / 100 := lt_of_not_ge hfirst
    have hmu : mu < (2 + delta / 100) / alpha := by
      rw [lt_div_iff₀ halpha0]
      simpa [mul_comm] using hmualpha
    have hqmul : ((2 + delta / 100) / alpha) * q ≤ mu * q :=
      mul_le_mul_of_nonpos_right hmu.le hqnonpos
    have hbase : 2 * delta / alpha + d / 100 ≤
        1 + ((2 + delta / 100) / alpha) * q := by
      have hqLower : -(1 / 2 : ℝ) ≤ q := by
        dsimp only [q, routeTGapMomentNu]
        linarith
      have hid : 1 + (2 / alpha) * q - 2 * delta / alpha =
          (delta - d) / alpha := by
        dsimp only [q, routeTGapMomentNu, delta, d]
        field_simp [halpha0.ne']
        ring
      have hperturb : (delta / (100 * alpha)) * q ≥
          -delta / (200 * alpha) := by
        have hmul := mul_le_mul_of_nonneg_left hqLower
          (by positivity : 0 ≤ delta / (100 * alpha))
        calc
          -delta / (200 * alpha) = (delta / (100 * alpha)) * (-(1 / 2 : ℝ)) := by ring
          _ ≤ (delta / (100 * alpha)) * q := hmul
      have hdDelta : d ≤ delta := by linarith
      have hroom : d / 100 + delta / (200 * alpha) ≤ (delta - d) / alpha := by
        have halphaD : alpha * d ≤ d := by
          have hmul := mul_le_mul_of_nonneg_right halphaOne hd.le
          simpa using hmul
        have hscaledD : alpha * (d / 100) ≤ d / 100 := by nlinarith
        have hsmallCore : d + d / 100 + delta / 200 ≤ delta := by linarith
        rw [le_div_iff₀ halpha0]
        calc
          (d / 100 + delta / (200 * alpha)) * alpha =
              alpha * (d / 100) + delta / 200 := by field_simp [halpha0.ne']
          _ ≤ d / 100 + delta / 200 := by
            simpa [add_comm] using add_le_add_right hscaledD (delta / 200)
          _ ≤ delta - d := by linarith
      have hsplit : ((2 + delta / 100) / alpha) * q =
          (2 / alpha) * q + (delta / (100 * alpha)) * q := by ring
      calc
        2 * delta / alpha + d / 100 =
            1 + (2 / alpha) * q - (delta - d) / alpha + d / 100 := by
          linarith [hid]
        _ ≤ 1 + (2 / alpha) * q - delta / (200 * alpha) := by linarith
        _ ≤ 1 + (2 / alpha) * q + (delta / (100 * alpha)) * q := by
          have hh := add_le_add_left hperturb (1 + (2 / alpha) * q)
          convert hh using 1 <;> ring
        _ = 1 + ((2 + delta / 100) / alpha) * q := by
          rw [hsplit]
          ring
    dsimp only [q] at hqmul
    have hqmul' : 1 + ((2 + delta / 100) / alpha) *
        (1 + routeTGapMomentNu - 2 * alpha) ≤
          1 + mu * (1 + routeTGapMomentNu - 2 * alpha) :=
      by simpa [add_comm] using add_le_add_left hqmul 1
    have htarget := hbase.trans (by simpa only [q] using hqmul')
    simpa [delta, d] using htarget

end RHTower.Sieve
