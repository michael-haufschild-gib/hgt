import GaloisForLFunctions.RHTower.Sieve.MaynardTunedRaise
import GaloisForLFunctions.RHTower.Sieve.MaynardRouteTAmplitudeOverlap

/-!
# Receiver-tailored exponents from tuned bounded raising

Route T needs large-value counts only in the tiny strip adjacent to amplitude `3/4`.  Raising a
robust group first through `T^(4/5)` and applying Montgomery gives two explicit exponents.  Both
are at most `2/3` on the whole strip, leaving enough fixed height reserve to absorb every bounded
coefficient and coloring polylogarithm.
-/

noncomputable section
namespace RHTower.Sieve

/-- Width term after a first crossing of `T^(4/5)` with maximal robust overshoot `19/270`. -/
def maynardTunedMontgomeryWidthExponent (alpha : ℝ) : ℝ :=
  (47 / 54 : ℝ) * (2 - 2 * alpha)

/-- Height term after a first crossing of `T^(4/5)`.  Its length exponent is nonpositive in the
Route-T strip, so overshoot can only improve it. -/
def maynardTunedMontgomeryHeightExponent (alpha : ℝ) : ℝ :=
  1 + (4 / 5 : ℝ) * (1 - 2 * alpha)

/-- Both terms of the tuned Montgomery mean square are at most `T^(2/3)` throughout the only
strip where Route T needs the lower global count. -/
theorem routeT_tunedMontgomery_exponents_le_two_thirds
    {alpha : ℝ}
    (halphaLo : (1 + routeTGapMomentNu) / 2 ≤ alpha)
    (_halphaHi : alpha ≤ 3 / 4) :
    maynardTunedMontgomeryWidthExponent alpha ≤ 2 / 3 ∧
      maynardTunedMontgomeryHeightExponent alpha ≤ 2 / 3 := by
  have hd : 0 < maynardLongGlobalAmplitudeDeficit :=
    maynardLongGlobalAmplitudeDeficit_pos
  have hdsmall : maynardLongGlobalAmplitudeDeficit < 1 / 100 :=
    maynardLongGlobalAmplitudeDeficit_lt_one_hundredth
  dsimp only [routeTGapMomentNu] at halphaLo
  constructor
  · dsimp only [maynardTunedMontgomeryWidthExponent]
    nlinarith
  · dsimp only [maynardTunedMontgomeryHeightExponent]
    nlinarith

/-- Even after spending `T^(1/100)` on all fixed-polylog costs, the tuned Montgomery count is far
inside Route T's second alternative. -/
theorem routeT_tunedMontgomery_with_polylog_le_second_alternative
    {mu alpha : ℝ}
    (hmuHi : mu ≤ 19 / 9)
    (halphaLo : (1 + routeTGapMomentNu) / 2 ≤ alpha)
    (halphaHi : alpha ≤ 3 / 4) :
    2 / 3 + 1 / 100 ≤
      1 + mu * (1 + routeTGapMomentNu - 2 * alpha) := by
  let d : ℝ := maynardLongGlobalAmplitudeDeficit
  let q : ℝ := 1 + routeTGapMomentNu - 2 * alpha
  have hd : 0 < d := maynardLongGlobalAmplitudeDeficit_pos
  have hdsmall : d < 1 / 100 :=
    maynardLongGlobalAmplitudeDeficit_lt_one_hundredth
  dsimp only [routeTGapMomentNu] at halphaLo
  have hqnonpos : q ≤ 0 := by
    dsimp only [q, d, routeTGapMomentNu]
    linarith
  have hqlower : -d / 2 ≤ q := by
    dsimp only [q, d, routeTGapMomentNu]
    linarith
  have hmuq : (19 / 9 : ℝ) * q ≤ mu * q :=
    mul_le_mul_of_nonpos_right hmuHi hqnonpos
  have hqscaled : -(19 / 18 : ℝ) * d ≤ (19 / 9 : ℝ) * q := by
    nlinarith
  dsimp only [q] at hmuq
  nlinarith

/-- **Wide-cell lower-strip Montgomery law.**  The selected-cell construction only gives
`beta < 1 + mu/60` when a long atom is present.  First crossing of `4/5` can therefore overshoot
far beyond the old robust bound `19/270`.  Nevertheless, through amplitude `19/25`, both raw
Montgomery exponents still fit Route T's second alternative after paying a fixed `T^(1/100)`
cost.  This removes the lower zero-reserve triple point without a zeta twelfth moment. -/
theorem routeT_wide_tunedMontgomery_exponents_with_polylog_le_second
    {mu alpha beta r : ℝ}
    (_hmuLo : 4 / 3 ≤ mu) (hmuHi : mu ≤ 19 / 9)
    (halphaLo : (1 + routeTGapMomentNu) / 2 ≤ alpha)
    (halphaHi : alpha ≤ 19 / 25)
    (_hbetaLo : mu / 120 ≤ beta) (hbetaHi : beta < 1 + mu / 60)
    (hrLo : 4 / 5 ≤ r) (hrHi : r < 4 / 5 + beta) :
    r * (2 - 2 * alpha) + 1 / 100 ≤
        1 + mu * (1 + routeTGapMomentNu - 2 * alpha) ∧
      1 + r * (1 - 2 * alpha) + 1 / 100 ≤
        1 + mu * (1 + routeTGapMomentNu - 2 * alpha) := by
  let d : ℝ := maynardLongGlobalAmplitudeDeficit
  let q : ℝ := 1 + routeTGapMomentNu - 2 * alpha
  have hd : 0 < d := maynardLongGlobalAmplitudeDeficit_pos
  have hdsmall : d < 1 / 100 :=
    maynardLongGlobalAmplitudeDeficit_lt_one_hundredth
  have hq : q ≤ 0 := by
    dsimp only [q]
    linarith
  have hmuq : (19 / 9 : ℝ) * q ≤ mu * q :=
    mul_le_mul_of_nonpos_right hmuHi hq
  have hbeta : beta < 559 / 540 := by linarith
  have hr : r < 991 / 540 := by linarith
  have halphaLower : 149 / 200 < alpha := by
    dsimp only [routeTGapMomentNu] at halphaLo
    linarith
  have hwidth : r * (2 - 2 * alpha) + 1 / 100 ≤
      1 + (19 / 9 : ℝ) * q := by
    dsimp only [q, routeTGapMomentNu, d]
    nlinarith
  have hheight : 1 + r * (1 - 2 * alpha) + 1 / 100 ≤
      1 + (19 / 9 : ℝ) * q := by
    have hcoef : 1 - 2 * alpha < 0 := by linarith
    have hmul := mul_le_mul_of_nonpos_right hrLo hcoef.le
    dsimp only [q, routeTGapMomentNu, d]
    nlinarith
  dsimp only [q] at hmuq
  exact ⟨hwidth.trans (by linarith), hheight.trans (by linarith)⟩

/-- First Huxley length term after crossing its optimizer `T^(1/(4 alpha-2))` with maximal
robust-group overshoot.  The second Huxley length term decreases under this overshoot. -/
def maynardTunedHuxleyCountExponent (alpha : ℝ) : ℝ :=
  (1 / (4 * alpha - 2) + 19 / 270) * (2 - 2 * alpha)

/-- Receiver-specific upper-strip dichotomy for tuned Huxley.  A reserve proportional to the
fixed endpoint deficit pays all bounded polylogarithmic costs.  The resulting count either is the
first alternative or its universal cube is the third alternative. -/
theorem routeT_tunedHuxley_exponent_first_or_cube_third
    {mu alpha : ℝ}
    (hmuLo : 4 / 3 ≤ mu) (_hmuHi : mu ≤ 19 / 9)
    (halphaLo : 3 / 4 ≤ alpha)
    (halphaHi : alpha ≤ 1 - maynardLongGlobalAmplitudeDeficit) :
    maynardTunedHuxleyCountExponent alpha +
          maynardLongGlobalAmplitudeDeficit / 100 ≤
        mu * (1 - alpha) ∨
      3 * (maynardTunedHuxleyCountExponent alpha +
          maynardLongGlobalAmplitudeDeficit / 100) ≤
        1 + mu * (3 + routeTGapMomentNu - 4 * alpha) := by
  let d : ℝ := maynardLongGlobalAmplitudeDeficit
  let delta : ℝ := 1 - alpha
  let x : ℝ := 2 * alpha - 1
  let c0 : ℝ := 407 / 2700
  let K : ℝ := 1 / x + c0
  let b : ℝ := 4 * delta - 1 / 2 - d / 2
  have hd : 0 < d := maynardLongGlobalAmplitudeDeficit_pos
  have hdsmall : d < 1 / 100 :=
    maynardLongGlobalAmplitudeDeficit_lt_one_hundredth
  have hdelta0 : 0 ≤ delta := by
    dsimp only [delta, d] at halphaHi ⊢
    linarith
  have hdDelta : d ≤ delta := by
    dsimp only [delta, d] at halphaHi ⊢
    linarith
  have hdeltaQuarter : delta ≤ 1 / 4 := by
    dsimp only [delta]
    linarith
  have hxlo : 1 / 2 ≤ x := by
    dsimp only [x]
    linarith
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hxlo
  have hxhi : x ≤ 1 := by
    dsimp only [x, delta] at halphaHi hdelta0 ⊢
    linarith
  have hc0 : 0 ≤ c0 := by norm_num [c0]
  have hc0le : c0 ≤ 1 / 6 := by norm_num [c0]
  have hinv : 1 / x ≤ 2 := by
    apply (div_le_iff₀ hxpos).2
    nlinarith
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hKle : K ≤ 13 / 6 := by
    dsimp only [K]
    linarith
  have hexponent :
      maynardTunedHuxleyCountExponent alpha =
        delta * (1 / x + 19 / 135) := by
    dsimp only [maynardTunedHuxleyCountExponent]
    rw [show 4 * alpha - 2 = 2 * x by dsimp only [x]; ring,
      show 2 - 2 * alpha = 2 * delta by dsimp only [delta]; ring]
    field_simp [hxpos.ne']
    ring_nf
  have hE :
      maynardTunedHuxleyCountExponent alpha + d / 100 ≤ delta * K := by
    rw [hexponent]
    dsimp only [K, c0]
    have hreserve : d / 100 ≤ delta / 100 := by linarith
    linarith
  have hbEq : 3 + routeTGapMomentNu - 4 * alpha = b := by
    dsimp only [b, delta, d, routeTGapMomentNu]
    ring
  rw [hbEq]
  by_cases hfirst : K ≤ mu
  · left
    have hmul := mul_le_mul_of_nonneg_left hfirst hdelta0
    exact hE.trans (by simpa [delta, mul_comm] using hmul)
  · right
    have hmuK : mu < K := lt_of_not_ge hfirst
    by_cases hb0 : 0 ≤ b
    · have hmuB := mul_le_mul_of_nonneg_right hmuLo hb0
      have hprod : delta * K ≤ delta * (13 / 6 : ℝ) :=
        mul_le_mul_of_nonneg_left hKle hdelta0
      have hthreeE := mul_le_mul_of_nonneg_left hE (by norm_num : (0 : ℝ) ≤ 3)
      have hbase : 3 * (delta * K) ≤ 1 + (4 / 3 : ℝ) * b := by
        calc
          3 * (delta * K) ≤ 3 * (delta * (13 / 6 : ℝ)) :=
            mul_le_mul_of_nonneg_left hprod (by norm_num)
          _ = (13 / 2 : ℝ) * delta := by ring
          _ ≤ 1 + (4 / 3 : ℝ) * b := by
            dsimp only [b]
            nlinarith
      exact hthreeE.trans (hbase.trans (by linarith))
    · have hbneg : b < 0 := lt_of_not_ge hb0
      have hmuB : K * b ≤ mu * b :=
        mul_le_mul_of_nonpos_right hmuK.le hbneg.le
      have hKx : K * x = 1 + c0 * x := by
        dsimp only [K]
        field_simp [hxpos.ne']
      have hcx : c0 * x ≤ 1 / 6 := by
        calc
          c0 * x ≤ (1 / 6 : ℝ) * 1 :=
            mul_le_mul hc0le hxhi (by linarith) (by norm_num)
          _ = 1 / 6 := by ring
      have hKd : K * d ≤ (13 / 6 : ℝ) * (1 / 100) :=
        mul_le_mul hKle hdsmall.le hd.le (by norm_num)
      have hKsum : K * (x + d) ≤ 2 := by
        calc
          K * (x + d) = K * x + K * d := by ring
          _ ≤ (1 + 1 / 6 : ℝ) + (13 / 6 : ℝ) * (1 / 100) := by
            apply add_le_add
            · rw [hKx]
              linarith
            · exact hKd
          _ ≤ 2 := by norm_num
      have hrelation : 3 * delta - b = (x + d) / 2 := by
        dsimp only [b, delta, x]
        ring
      have hcore : 3 * (delta * K) ≤ 1 + K * b := by
        have hhalf : K * ((x + d) / 2) ≤ 1 := by
          calc
            K * ((x + d) / 2) = K * (x + d) / 2 := by ring
            _ ≤ 2 / 2 := div_le_div_of_nonneg_right hKsum (by norm_num)
            _ = 1 := by norm_num
        calc
          3 * (delta * K) = K * b + K * (3 * delta - b) := by ring
          _ = K * b + K * ((x + d) / 2) := by rw [hrelation]
          _ ≤ K * b + 1 := by linarith
          _ = 1 + K * b := by ring
      have hthreeE := mul_le_mul_of_nonneg_left hE (by norm_num : (0 : ℝ) ≤ 3)
      exact hthreeE.trans (hcore.trans (by linarith))

end RHTower.Sieve
