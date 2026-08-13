import GaloisForLFunctions.RHTower.Sieve.MaynardTunedCountExponents

/-!
# Adjacent-power optimization for every sub-height Maynard group

First crossing alone can overshoot Huxley's optimizer by almost one full atom.  The power just
before the crossing is also available.  Choosing the better of these two adjacent powers removes
the atom-size loss entirely: for every selected exponent in `[1/90,1]`, the two Huxley terms are
simultaneously bounded by `2(1-alpha)/alpha` for `3/4 <= alpha < 1`.

This is the exact replacement for the published global Huxley exponent needed by Route T.
-/

noncomputable section
namespace RHTower.Sieve

/-- Huxley's optimizer in height-exponent coordinates. -/
def maynardHuxleyOptimizer (alpha : ℝ) : ℝ :=
  1 / (4 * alpha - 2)

/-- The larger of the two Huxley count exponents at raised length `T^r`. -/
def maynardHuxleyRaisedCountExponent (alpha r : ℝ) : ℝ :=
  max (r * (2 - 2 * alpha)) (1 + r * (4 - 6 * alpha))

theorem maynardHuxleyOptimizer_pos {alpha : ℝ} (halpha : 3 / 4 ≤ alpha) :
    0 < maynardHuxleyOptimizer alpha := by
  dsimp only [maynardHuxleyOptimizer]
  exact one_div_pos.mpr (by linarith)

theorem maynardHuxleyOptimizer_le_one
    {alpha : ℝ} (halpha : 3 / 4 ≤ alpha) :
    maynardHuxleyOptimizer alpha ≤ 1 := by
  dsimp only [maynardHuxleyOptimizer]
  rw [div_le_one (by linarith : 0 < 4 * alpha - 2)]
  linarith

/-- First optimizer crossing for an arbitrary sub-height exponent. -/
theorem exists_maynard_optimizer_crossing
    {alpha beta : ℝ} (halpha : 3 / 4 ≤ alpha)
    (hbetaLo : 1 / 90 ≤ beta) :
    ∃ n : ℕ, 0 < n ∧ n ≤ 90 ∧
      maynardHuxleyOptimizer alpha ≤ (n : ℝ) * beta ∧
      (n : ℝ) * beta < maynardHuxleyOptimizer alpha + beta := by
  let theta := maynardHuxleyOptimizer alpha
  have htheta : 0 < theta := maynardHuxleyOptimizer_pos halpha
  have hthetaOne : theta ≤ 1 := maynardHuxleyOptimizer_le_one halpha
  have hbeta : 0 < beta := lt_of_lt_of_le (by norm_num) hbetaLo
  let n : ℕ := ⌈theta / beta⌉₊
  have harg0 : 0 ≤ theta / beta := by positivity
  have hnlo : theta / beta ≤ (n : ℝ) := Nat.le_ceil _
  have hnhi : (n : ℝ) < theta / beta + 1 := Nat.ceil_lt_add_one harg0
  have hn90 : n ≤ 90 := by
    rw [Nat.ceil_le, div_le_iff₀ hbeta]
    have hone : (1 : ℝ) ≤ 90 * beta := by nlinarith
    exact hthetaOne.trans hone
  have hcross := mul_le_mul_of_nonneg_right hnlo hbeta.le
  have hover := mul_lt_mul_of_pos_right hnhi hbeta
  have hcross' : theta ≤ (n : ℝ) * beta := by
    rw [div_mul_cancel₀ _ hbeta.ne'] at hcross
    simpa [mul_comm] using hcross
  have hover' : (n : ℝ) * beta < theta + beta := by
    rw [add_mul, div_mul_cancel₀ _ hbeta.ne', one_mul] at hover
    simpa [mul_comm] using hover
  have hnpos : 0 < n := by
    have : (0 : ℝ) < (n : ℝ) := by nlinarith
    exact_mod_cast this
  exact ⟨n, hnpos, hn90, hcross', hover'⟩

/-- **Adjacent-power Huxley law.**  One of the crossing power and its predecessor has count
exponent at most `2(1-alpha)/alpha`.  The bound is uniform in the atom/group exponent. -/
theorem exists_maynard_adjacent_optimizer_raise
    {alpha beta : ℝ} (halphaLo : 3 / 4 ≤ alpha) (halphaHi : alpha < 1)
    (hbetaLo : 1 / 90 ≤ beta) (hbetaHi : beta ≤ 1) :
    ∃ ell : ℕ, 0 < ell ∧ ell ≤ 90 ∧
      1 / 2 ≤ (ell : ℝ) * beta ∧
      maynardHuxleyRaisedCountExponent alpha ((ell : ℝ) * beta) ≤
        2 * (1 - alpha) / alpha := by
  let theta := maynardHuxleyOptimizer alpha
  let delta := 1 - alpha
  let K := 2 * delta / alpha
  have halpha0 : 0 < alpha := lt_of_lt_of_le (by norm_num) halphaLo
  have hdelta : 0 < delta := by dsimp only [delta]; linarith
  have hcoef : 4 - 6 * alpha < 0 := by linarith
  have htheta : 0 < theta := maynardHuxleyOptimizer_pos halphaLo
  have hthetaHalf : (1 / 2 : ℝ) < theta := by
    dsimp only [theta, maynardHuxleyOptimizer]
    rw [lt_div_iff₀ (by linarith : 0 < 4 * alpha - 2)]
    linarith
  obtain ⟨n, hnpos, hn90, hcross, hover⟩ :=
    exists_maynard_optimizer_crossing halphaLo hbetaLo
  have hoptimizer :
      1 + theta * (4 - 6 * alpha) = theta * (2 - 2 * alpha) := by
    have hden : 4 * alpha - 2 ≠ 0 := by linarith
    dsimp only [theta, maynardHuxleyOptimizer]
    field_simp [hden]
    ring
  by_cases hn1 : n = 1
  · have hthetaBeta : theta ≤ beta := by simpa [hn1] using hcross
    have hhalf : (1 / 2 : ℝ) ≤ beta := hthetaHalf.le.trans hthetaBeta
    have hheight : 1 + beta * (4 - 6 * alpha) ≤
        beta * (2 - 2 * alpha) := by
      have hmul := mul_le_mul_of_nonpos_right hthetaBeta hcoef.le
      nlinarith [hoptimizer]
    have hwidth : beta * (2 - 2 * alpha) ≤ K := by
      have hfactor : 2 - 2 * alpha = 2 * delta := by
        dsimp only [delta]
        ring
      rw [hfactor]
      have hmul := mul_le_mul_of_nonneg_right hbetaHi (by positivity : 0 ≤ 2 * delta)
      dsimp only [K]
      have hbase : 2 * delta ≤ 2 * delta / alpha := by
        rw [le_div_iff₀ halpha0]
        nlinarith
      exact hmul.trans (by simpa using hbase)
    refine ⟨1, by norm_num, by norm_num, by simpa using hhalf, ?_⟩
    dsimp only [maynardHuxleyRaisedCountExponent]
    rw [max_le_iff]
    simpa only [Nat.cast_one, one_mul, delta, K] using ⟨hwidth, hheight.trans hwidth⟩
  · have hn2 : 2 ≤ n := by omega
    let r : ℝ := (n : ℝ) * beta
    by_cases hwidth : r * (2 - 2 * alpha) ≤ K
    · have hhalf : (1 / 2 : ℝ) ≤ r := by
        simpa [r] using hthetaHalf.le.trans hcross
      have hheight : 1 + r * (4 - 6 * alpha) ≤
          r * (2 - 2 * alpha) := by
        have hmul := mul_le_mul_of_nonpos_right hcross hcoef.le
        dsimp only [r]
        nlinarith [hoptimizer]
      refine ⟨n, hnpos, hn90, by simpa [r] using hhalf, ?_⟩
      dsimp only [maynardHuxleyRaisedCountExponent]
      rw [max_le_iff]
      exact ⟨hwidth, hheight.trans hwidth⟩
    · let ell := n - 1
      have hellpos : 0 < ell := by dsimp only [ell]; omega
      have hell90 : ell ≤ 90 := by dsimp only [ell]; omega
      let r0 : ℝ := (ell : ℝ) * beta
      have hwidthStrict : K < r * (2 - 2 * alpha) := lt_of_not_ge hwidth
      have hrInv : 1 / alpha < r := by
        have hfactor : 2 - 2 * alpha = 2 * delta := by
          dsimp only [delta]
          ring
        rw [hfactor] at hwidthStrict
        dsimp only [K] at hwidthStrict
        have htwoDelta : 0 < 2 * delta := by positivity
        have hscaled : (1 / alpha) * (2 * delta) < r * (2 * delta) := by
          calc
          (1 / alpha) * (2 * delta) = 2 * delta / alpha := by ring
          _ < r * (2 * delta) := hwidthStrict
        nlinarith
      have htwor0 : r ≤ 2 * r0 := by
        have hnat : n ≤ 2 * (n - 1) := by omega
        have hreal : (n : ℝ) ≤ 2 * ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
        have := mul_le_mul_of_nonneg_right hreal (lt_of_lt_of_le (by norm_num) hbetaLo).le
        dsimp only [r, r0, ell]
        simpa only [mul_assoc] using this
      have hr0 : 1 / (2 * alpha) < r0 := by
        have halphaTwo : 0 < 2 * alpha := by positivity
        have hinv : 2 * (1 / (2 * alpha)) = 1 / alpha := by
          field_simp [halpha0.ne']
        nlinarith
      have hhalfInv : (1 / 2 : ℝ) < 1 / (2 * alpha) := by
        rw [lt_div_iff₀ (by positivity : 0 < 2 * alpha)]
        nlinarith
      have hhalf : (1 / 2 : ℝ) ≤ r0 := (hhalfInv.trans hr0).le
      have hprev : r0 < theta := by
        have hr0add : r0 + beta = r := by
          dsimp only [r0, ell, r]
          rw [Nat.cast_sub (by omega : 1 ≤ n)]
          push_cast
          ring
        have hover' : r < theta + beta := by
          simpa [r, theta] using hover
        linarith
      have hwidth0 : r0 * (2 - 2 * alpha) ≤ K := by
        have hfactor : 2 - 2 * alpha = 2 * delta := by
          dsimp only [delta]
          ring
        have hthetaAlpha : theta ≤ 1 / alpha := by
          dsimp only [theta, maynardHuxleyOptimizer]
          apply (div_le_div_iff₀ (by linarith : 0 < 4 * alpha - 2) halpha0).2
          nlinarith
        rw [hfactor]
        have hr0le : r0 ≤ 1 / alpha := hprev.le.trans hthetaAlpha
        dsimp only [K]
        have hmul := mul_le_mul_of_nonneg_right hr0le (by positivity : 0 ≤ 2 * delta)
        calc
          r0 * (2 * delta) ≤ (1 / alpha) * (2 * delta) := hmul
          _ = 2 * delta / alpha := by ring
      have hheight0 : 1 + r0 * (4 - 6 * alpha) ≤ K := by
        have hmul := mul_le_mul_of_nonpos_right hr0.le hcoef.le
        have hid : 1 + (1 / (2 * alpha)) * (4 - 6 * alpha) = K := by
          dsimp only [K, delta]
          field_simp [halpha0.ne']
          ring
        linarith
      refine ⟨ell, hellpos, hell90, by simpa [r0] using hhalf, ?_⟩
      dsimp only [maynardHuxleyRaisedCountExponent]
      rw [max_le_iff]
      exact ⟨hwidth0, hheight0⟩

/-- Route T's receiver needs only first or second alternative for the adjacent-power exponent.
The branch point is the universal scalar `mu*alpha = 2`. -/
theorem routeT_adjacent_optimizer_first_or_second
    {mu alpha : ℝ} (hmuLo : 4 / 3 ≤ mu) (_hmuHi : mu ≤ 19 / 9)
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
    have hratio : 2 / alpha ≤ mu := (div_le_iff₀ halpha0).2 (by simpa [mul_comm] using hfirst)
    have hmul := mul_le_mul_of_nonneg_right hratio hdelta
    dsimp only [delta] at hmul ⊢
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul
  · right
    have hmualpha : mu * alpha ≤ 2 := le_of_not_ge hfirst
    have hmu : mu ≤ 2 / alpha := (le_div_iff₀ halpha0).2 (by simpa [mul_comm] using hmualpha)
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

/-- At amplitude at least `99/100`, the first optimizer-crossing index is at most `46`. -/
theorem maynard_optimizer_crossing_index_le_46
    {alpha beta : ℝ} {n : ℕ}
    (halphaLo : 99 / 100 ≤ alpha)
    (hbetaLo : 1 / 90 ≤ beta)
    (hover : (n : ℝ) * beta < maynardHuxleyOptimizer alpha + beta) :
    n ≤ 46 := by
  let theta := maynardHuxleyOptimizer alpha
  have halpha0 : 0 < alpha := by linarith
  have hbeta0 : 0 < beta := by linarith
  have hthetaUpper : theta ≤ 25 / 49 := by
    dsimp only [theta, maynardHuxleyOptimizer]
    rw [div_le_iff₀ (by linarith : 0 < 4 * alpha - 2)]
    nlinarith
  have hthetaBeta : theta < 46 * beta := by
    have hfixed : (25 / 49 : ℝ) < 46 * (1 / 90 : ℝ) := by norm_num
    have hmul := mul_le_mul_of_nonneg_left hbetaLo (by norm_num : (0 : ℝ) ≤ 46)
    exact hthetaUpper.trans_lt (hfixed.trans_le hmul)
  have hnBeta : (n : ℝ) * beta < 47 * beta := by
    have hsum : theta + beta < 46 * beta + beta := by
      simpa [add_comm] using add_lt_add_right hthetaBeta beta
    have hhover : (n : ℝ) * beta < theta + beta := by simpa [theta] using hover
    calc
      (n : ℝ) * beta < theta + beta := hhover
      _ < 46 * beta + beta := hsum
      _ = 47 * beta := by ring
  have hnReal : (n : ℝ) < 47 := by nlinarith
  have hnNat : n < 47 := by exact_mod_cast hnReal
  omega

/-- At Route T endpoint amplitudes, the first optimizer-crossing power itself is admissible,
has bounded order, and retains the fixed small-cell reserve.  Unlike the adjacent predecessor,
this witness also lies on the absorbing side of Huxley's square-scale threshold. -/
theorem exists_maynard_small_crossing_raise_high_amplitude
    {alpha beta : ℝ} (halphaLo : 99 / 100 ≤ alpha) (halphaHi : alpha < 1)
    (hbetaLo : 1 / 90 ≤ beta) (hbetaHi : beta ≤ 5 / 12) :
    ∃ ell : ℕ, 0 < ell ∧ ell ≤ 51 ∧
      maynardHuxleyOptimizer alpha ≤ (ell : ℝ) * beta ∧
      (ell : ℝ) * beta < maynardHuxleyOptimizer alpha + beta ∧
      maynardHuxleyRaisedCountExponent alpha ((ell : ℝ) * beta) ≤
        (19 / 10 : ℝ) * (1 - alpha) / alpha := by
  let theta := maynardHuxleyOptimizer alpha
  let delta := 1 - alpha
  let K := (19 / 10 : ℝ) * delta / alpha
  have halphaThreeQuarters : 3 / 4 ≤ alpha := by linarith
  have halpha0 : 0 < alpha := by linarith
  have hdelta : 0 < delta := by dsimp only [delta]; linarith
  have hcoef : 4 - 6 * alpha < 0 := by linarith
  have hthetaHalf : (1 / 2 : ℝ) < theta := by
    dsimp only [theta, maynardHuxleyOptimizer]
    rw [lt_div_iff₀ (by linarith : 0 < 4 * alpha - 2)]
    linarith
  obtain ⟨n, hnpos, _hn90, hcross, hover⟩ :=
    exists_maynard_optimizer_crossing halphaThreeQuarters hbetaLo
  have hn46 : n ≤ 46 :=
    maynard_optimizer_crossing_index_le_46 halphaLo hbetaLo (by simpa [theta] using hover)
  have hn51 : n ≤ 51 := hn46.trans (by norm_num)
  have hn2 : 2 ≤ n := by
    by_contra hnot
    have hn1 : n = 1 := by omega
    have : theta ≤ beta := by simpa [hn1] using hcross
    linarith
  let r : ℝ := (n : ℝ) * beta
  have hoptimizer :
      1 + theta * (4 - 6 * alpha) = theta * (2 - 2 * alpha) := by
    have hden : 4 * alpha - 2 ≠ 0 := by linarith
    dsimp only [theta, maynardHuxleyOptimizer]
    field_simp [hden]
    ring
  have hheight : 1 + r * (4 - 6 * alpha) ≤ r * (2 - 2 * alpha) := by
    have hmul := mul_le_mul_of_nonpos_right hcross hcoef.le
    dsimp only [r]
    nlinarith [hoptimizer]
  have hwidth : r * (2 - 2 * alpha) ≤ K := by
    have hfactor : 2 - 2 * alpha = 2 * delta := by
      dsimp only [delta]
      ring
    rw [hfactor]
    by_cases hnEq : n = 2
    · have hr : r ≤ 5 / 6 := by
        dsimp only [r]
        rw [hnEq]
        norm_num
        linarith
      have hcoeff : (5 / 3 : ℝ) ≤ (19 / 10) / alpha := by
        rw [le_div_iff₀ halpha0]
        nlinarith
      have hrmul := mul_le_mul_of_nonneg_right hr (by positivity : 0 ≤ 2 * delta)
      have hcoeffMul := mul_le_mul_of_nonneg_right hcoeff hdelta.le
      dsimp only [K]
      calc
        r * (2 * delta) ≤ (5 / 6 : ℝ) * (2 * delta) := hrmul
        _ = (5 / 3 : ℝ) * delta := by ring
        _ ≤ ((19 / 10 : ℝ) / alpha) * delta := hcoeffMul
        _ = (19 / 10 : ℝ) * delta / alpha := by ring
    · have hn3 : 3 ≤ n := by omega
      have hbetaTheta : 2 * beta < theta := by
        have hnat : 2 ≤ n - 1 := by omega
        have hreal : (2 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
        have hmul := mul_le_mul_of_nonneg_right hreal (by linarith : 0 ≤ beta)
        have hprev : ((n : ℝ) - 1) * beta < theta := by
          have := hover
          dsimp only [r, theta]
          nlinarith
        have hcast : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n)]
          norm_num
        rw [hcast] at hmul
        nlinarith
      have hrUpper : r < (3 / 2 : ℝ) * theta := by
        dsimp only [r]
        nlinarith [hover, hbetaTheta]
      have hthetaCoeff : 3 * theta ≤ (19 / 10 : ℝ) / alpha := by
        have hden : 0 < 4 * alpha - 2 := by linarith
        calc
          3 * theta = 3 / (4 * alpha - 2) := by
            dsimp only [theta, maynardHuxleyOptimizer]
            ring
          _ ≤ (19 / 10 : ℝ) / alpha := by
            rw [div_le_div_iff₀ hden halpha0]
            nlinarith
      have hrmul := mul_le_mul_of_nonneg_right hrUpper.le (by positivity : 0 ≤ 2 * delta)
      have hcoeffMul := mul_le_mul_of_nonneg_right hthetaCoeff hdelta.le
      dsimp only [K]
      calc
        r * (2 * delta) ≤ ((3 / 2 : ℝ) * theta) * (2 * delta) := hrmul
        _ = (3 * theta) * delta := by ring
        _ ≤ ((19 / 10 : ℝ) / alpha) * delta := hcoeffMul
        _ = (19 / 10 : ℝ) * delta / alpha := by ring
  refine ⟨n, hnpos, hn51, by simpa [r] using hcross,
    by simpa [r, theta] using hover, ?_⟩
  dsimp only [maynardHuxleyRaisedCountExponent]
  rw [max_le_iff]
  simpa only [delta, K] using ⟨hwidth, hheight.trans hwidth⟩

/-- Below exponent `5/12`, absence of the `n=1` crossing leaves a fixed fraction of the
adjacent-power Huxley cap unused. -/
theorem exists_maynard_small_adjacent_optimizer_raise
    {alpha beta : ℝ} (halphaLo : 3 / 4 ≤ alpha) (halphaHi : alpha < 1)
    (hbetaLo : 1 / 90 ≤ beta) (hbetaHi : beta ≤ 5 / 12) :
    ∃ ell : ℕ, 0 < ell ∧ ell ≤ 90 ∧
      1 / 2 ≤ (ell : ℝ) * beta ∧
      maynardHuxleyRaisedCountExponent alpha ((ell : ℝ) * beta) ≤
        (19 / 10 : ℝ) * (1 - alpha) / alpha := by
  let theta := maynardHuxleyOptimizer alpha
  let delta := 1 - alpha
  let K := (19 / 10 : ℝ) * delta / alpha
  have halpha0 : 0 < alpha := lt_of_lt_of_le (by norm_num) halphaLo
  have hdelta : 0 < delta := by dsimp only [delta]; linarith
  have hcoef : 4 - 6 * alpha < 0 := by linarith
  have hthetaHalf : (1 / 2 : ℝ) < theta := by
    dsimp only [theta, maynardHuxleyOptimizer]
    rw [lt_div_iff₀ (by linarith : 0 < 4 * alpha - 2)]
    linarith
  obtain ⟨n, hnpos, hn90, hcross, hover⟩ :=
    exists_maynard_optimizer_crossing halphaLo hbetaLo
  have hoptimizer :
      1 + theta * (4 - 6 * alpha) = theta * (2 - 2 * alpha) := by
    have hden : 4 * alpha - 2 ≠ 0 := by linarith
    dsimp only [theta, maynardHuxleyOptimizer]
    field_simp [hden]
    ring
  have hn2 : 2 ≤ n := by
    by_contra hnot
    have hn1 : n = 1 := by omega
    have : theta ≤ beta := by simpa [theta, hn1] using hcross
    linarith
  let r : ℝ := (n : ℝ) * beta
  by_cases hnEq : n = 2
  · have hhalf : (1 / 2 : ℝ) ≤ r := by
      simpa [r] using hthetaHalf.le.trans hcross
    have hr : r ≤ 5 / 6 := by
      dsimp only [r]
      rw [hnEq]
      norm_num
      linarith
    have hwidth : r * (2 - 2 * alpha) ≤ K := by
      have hfactor : 2 - 2 * alpha = 2 * delta := by
        dsimp only [delta]
        ring
      rw [hfactor]
      have hrmul := mul_le_mul_of_nonneg_right hr (by positivity : 0 ≤ 2 * delta)
      have hcoeff : (5 / 6 : ℝ) * 2 ≤ (19 / 10) / alpha := by
        rw [le_div_iff₀ halpha0]
        nlinarith
      have hcoeffMul := mul_le_mul_of_nonneg_right hcoeff hdelta.le
      dsimp only [K]
      calc
        r * (2 * delta) ≤ (5 / 6 : ℝ) * (2 * delta) := hrmul
        _ = ((5 / 6 : ℝ) * 2) * delta := by ring
        _ ≤ ((19 / 10 : ℝ) / alpha) * delta := hcoeffMul
        _ = (19 / 10 : ℝ) * delta / alpha := by ring
    have hheight : 1 + r * (4 - 6 * alpha) ≤ r * (2 - 2 * alpha) := by
      have hmul := mul_le_mul_of_nonpos_right hcross hcoef.le
      dsimp only [r]
      nlinarith [hoptimizer]
    refine ⟨n, hnpos, hn90, by simpa [r] using hhalf, ?_⟩
    dsimp only [maynardHuxleyRaisedCountExponent]
    rw [max_le_iff]
    exact ⟨hwidth, hheight.trans hwidth⟩
  · have hn3 : 3 ≤ n := by omega
    by_cases hwidth : r * (2 - 2 * alpha) ≤ K
    · have hhalf : (1 / 2 : ℝ) ≤ r := by
        simpa [r] using hthetaHalf.le.trans hcross
      have hheight : 1 + r * (4 - 6 * alpha) ≤ r * (2 - 2 * alpha) := by
        have hmul := mul_le_mul_of_nonpos_right hcross hcoef.le
        dsimp only [r]
        nlinarith [hoptimizer]
      refine ⟨n, hnpos, hn90, by simpa [r] using hhalf, ?_⟩
      dsimp only [maynardHuxleyRaisedCountExponent]
      rw [max_le_iff]
      exact ⟨hwidth, hheight.trans hwidth⟩
    · let ell := n - 1
      let r0 : ℝ := (ell : ℝ) * beta
      have hellpos : 0 < ell := by dsimp only [ell]; omega
      have hell90 : ell ≤ 90 := by dsimp only [ell]; omega
      have hwidthStrict : K < r * (2 - 2 * alpha) := lt_of_not_ge hwidth
      have hrLower : 19 / (20 * alpha) < r := by
        have hfactor : 2 - 2 * alpha = 2 * delta := by
          dsimp only [delta]
          ring
        rw [hfactor] at hwidthStrict
        dsimp only [K] at hwidthStrict
        have hscale : (19 / (20 * alpha)) * (2 * delta) =
            (19 / 10) * delta / alpha := by
          field_simp [halpha0.ne']
          ring
        have hscaled : (19 / (20 * alpha)) * (2 * delta) <
            r * (2 * delta) := by simpa [hscale] using hwidthStrict
        nlinarith
      have hthreeR0 : 2 * r ≤ 3 * r0 := by
        have hnat : 2 * n ≤ 3 * (n - 1) := by omega
        have hreal : 2 * (n : ℝ) ≤ 3 * ((n - 1 : ℕ) : ℝ) := by
          exact_mod_cast hnat
        have hmul := mul_le_mul_of_nonneg_right hreal
          (lt_of_lt_of_le (by norm_num) hbetaLo).le
        dsimp only [r, r0, ell]
        nlinarith
      have hr0Lower : 19 / (30 * alpha) < r0 := by
        have hidentity : 3 * (19 / (30 * alpha)) = 2 * (19 / (20 * alpha)) := by
          field_simp [halpha0.ne']
          ring
        nlinarith
      have hhalfBase : (1 / 2 : ℝ) < 19 / (30 * alpha) := by
        rw [lt_div_iff₀ (by positivity : 0 < 30 * alpha)]
        nlinarith
      have hhalf : (1 / 2 : ℝ) ≤ r0 := (hhalfBase.trans hr0Lower).le
      have hprev : r0 < theta := by
        have hr0add : r0 + beta = r := by
          dsimp only [r0, ell, r]
          rw [Nat.cast_sub (by omega : 1 ≤ n)]
          push_cast
          ring
        have hover' : r < theta + beta := by simpa [r, theta] using hover
        linarith
      have hthetaUpper : theta ≤ 19 / (20 * alpha) := by
        dsimp only [theta, maynardHuxleyOptimizer]
        rw [div_le_div_iff₀ (by linarith : 0 < 4 * alpha - 2)
          (by positivity : 0 < 20 * alpha)]
        nlinarith
      have hwidth0 : r0 * (2 - 2 * alpha) ≤ K := by
        have hfactor : 2 - 2 * alpha = 2 * delta := by
          dsimp only [delta]
          ring
        rw [hfactor]
        have hr0Upper : r0 ≤ 19 / (20 * alpha) := hprev.le.trans hthetaUpper
        have hmul := mul_le_mul_of_nonneg_right hr0Upper (by positivity : 0 ≤ 2 * delta)
        dsimp only [K]
        calc
          r0 * (2 * delta) ≤ (19 / (20 * alpha)) * (2 * delta) := hmul
          _ = (19 / 10) * delta / alpha := by
            field_simp [halpha0.ne']
            ring
      have hheight0 : 1 + r0 * (4 - 6 * alpha) ≤ K := by
        have hmul := mul_le_mul_of_nonpos_right hr0Lower.le hcoef.le
        have hbase : 1 + (19 / (30 * alpha)) * (4 - 6 * alpha) ≤ K := by
          dsimp only [K, delta]
          rw [le_div_iff₀ halpha0]
          field_simp [halpha0.ne']
          nlinarith
        linarith
      refine ⟨ell, hellpos, hell90, by simpa [r0] using hhalf, ?_⟩
      dsimp only [maynardHuxleyRaisedCountExponent]
      rw [max_le_iff]
      exact ⟨hwidth0, hheight0⟩

/-- The fixed small-cell reserve pays `d/100` before applying Route T's exact dichotomy. -/
theorem routeT_small_adjacent_optimizer_with_reserve_first_or_second
    {mu alpha : ℝ} (hmuLo : 4 / 3 ≤ mu) (hmuHi : mu ≤ 19 / 9)
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
    have hddiv : d ≤ delta / alpha := (le_div_iff₀ halpha0).2 (by
      simpa [mul_comm] using halphaD)
    have hdiv := div_le_div_of_nonneg_right hddiv (by norm_num : (0 : ℝ) ≤ 100)
    have hratio0 : 0 ≤ delta / alpha := by positivity
    calc
      (19 / 10 : ℝ) * delta / alpha + d / 100 ≤
          (19 / 10 : ℝ) * delta / alpha + (delta / alpha) / 100 :=
        by linarith
      _ ≤ 2 * delta / alpha := by
        have hmain : (19 / 10 : ℝ) * (delta / alpha) +
            (delta / alpha) / 100 ≤ 2 * (delta / alpha) := by nlinarith
        convert hmain using 1 <;> ring
  rcases routeT_adjacent_optimizer_first_or_second hmuLo hmuHi halphaLo halphaHi with
    hfirst | hsecond
  · exact Or.inl (by simpa [delta, d] using hreserve.trans hfirst)
  · exact Or.inr (by simpa [delta, d] using hreserve.trans hsecond)

end RHTower.Sieve
