import GaloisForLFunctions.RHTower.CCMRectangularOneSidedTransverseExponent

/-!
# Two-sided transverse oscillation of the fixed rectangular observable

The lower-loss spectrum detects the negative excursions of the logarithmically sampled
rectangular Xi--Weil observable.  This file supplies the dual Landau argument.  If the right Xi
divisor is nonempty, an eventual upper budget `Q_L(n) ≤ C n^alpha` with
`alpha < xiRightTransverseSup` is equally impossible.  Hence false RH forces both signs to exceed
every subcritical power scale cofinally.
-/

open Complex Filter Function Set

namespace RHTower

noncomputable section

/-- The nonnegative coefficient used by the upper-budget Landau argument. -/
def xiRectangularPowerUpperLandauCoefficient
    (L C alpha : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    C * powerCorrectionCoefficient alpha n -
      xiRectangularRightDirichletCoefficientReal L n

theorem xiRectangularPowerUpperLandauCoefficient_nonneg
    {L C alpha : ℝ}
    (hupper : ∀ n : ℕ, n ≠ 0 →
      xiRectangularRightDirichletCoefficientReal L n ≤
        C * powerCorrectionCoefficient alpha n) :
    ∀ n, 0 ≤ xiRectangularPowerUpperLandauCoefficient L C alpha n := by
  intro n
  rw [xiRectangularPowerUpperLandauCoefficient]
  split_ifs with hn
  · exact le_rfl
  · linarith [hupper n hn]

/-- Canonical continuation of the dual power-corrected Landau series. -/
def xiRectangularPowerUpperLandauContinuation
    (L C alpha : ℝ) (s : ℂ) : ℂ :=
  C * riemannZeta (s - alpha) -
    2 * xiRectangularShiftedZetaSeries L s

theorem xiRectangularPowerUpperLandauCoefficient_LSeriesSummable
    (L C : ℝ) {alpha delta : ℝ}
    (hzeros : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ delta)
    {s : ℂ} (hsdelta : 1 + delta < s.re)
    (hsalpha : 1 + alpha < s.re) :
    LSeriesSummable
      (fun n => ((xiRectangularPowerUpperLandauCoefficient L C alpha n : ℝ) : ℂ)) s := by
  have hfull := xiRectangularRightDirichletComplex_LSeriesSummable L hzeros hsdelta
  have hpower := (powerCorrectionCoefficient_LSeriesSummable hsalpha).smul (C : ℂ)
  have hsub : LSeriesSummable
      ((C : ℂ) • (fun n => ((powerCorrectionCoefficient alpha n : ℝ) : ℂ)) -
        (fun n => xiRectangularRightDirichletComplex L n)) s :=
    hpower.sub hfull
  change Summable (LSeries.term
    (fun n => ((xiRectangularPowerUpperLandauCoefficient L C alpha n : ℝ) : ℂ)) s)
  change Summable (LSeries.term _ s) at hsub
  apply hsub.congr
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [LSeries.term_zero]
  · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      xiRectangularPowerUpperLandauCoefficient, if_neg hn0,
      ofReal_sub, ofReal_mul,
      ofReal_xiRectangularRightDirichletCoefficientReal]

theorem LSeries_xiRectangularPowerUpperLandauCoefficient_eq_continuation
    (L C : ℝ) {alpha delta : ℝ}
    (hzeros : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ delta)
    {s : ℂ} (hsdelta : 1 + delta < s.re)
    (hsalpha : 1 + alpha < s.re) :
    LSeries
        (fun n => ((xiRectangularPowerUpperLandauCoefficient L C alpha n : ℝ) : ℂ)) s =
      xiRectangularPowerUpperLandauContinuation L C alpha s := by
  have hfull := xiRectangularRightDirichletComplex_LSeriesSummable L hzeros hsdelta
  have hpower0 := powerCorrectionCoefficient_LSeriesSummable hsalpha
  have hpower := hpower0.smul (C : ℂ)
  calc
    LSeries
        (fun n => ((xiRectangularPowerUpperLandauCoefficient L C alpha n : ℝ) : ℂ)) s =
        LSeries ((C : ℂ) •
          (fun n => ((powerCorrectionCoefficient alpha n : ℝ) : ℂ)) -
          (fun n => xiRectangularRightDirichletComplex L n)) s := by
      apply LSeries_congr
      intro n hn
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        xiRectangularPowerUpperLandauCoefficient, if_neg hn,
        ofReal_sub, ofReal_mul,
        ofReal_xiRectangularRightDirichletCoefficientReal]
    _ = LSeries ((C : ℂ) •
          (fun n => ((powerCorrectionCoefficient alpha n : ℝ) : ℂ))) s -
        LSeries (fun n => xiRectangularRightDirichletComplex L n) s :=
      LSeries_sub hpower hfull
    _ = C * LSeries (fun n => ((powerCorrectionCoefficient alpha n : ℝ) : ℂ)) s -
        2 * xiRectangularShiftedZetaSeries L s := by
      rw [LSeries_smul,
        LSeries_xiRectangularRightDirichletComplex_eq_shiftedZeta L hzeros hsdelta]
    _ = xiRectangularPowerUpperLandauContinuation L C alpha s := by
      rw [LSeries_powerCorrectionCoefficient_eq_riemannZeta hsalpha]
      rfl

theorem differentiableOn_xiRectangularPowerUpperLandauContinuation_landauBall
    (L C alpha : ℝ) {delta eta r : ℝ}
    (hdelta0 : 0 ≤ delta) (hdeltahalf : delta ≤ 1 / 2)
    (heta : 0 < eta) (hr : 0 < r)
    (hrquarter : r ≤ 1 / 4) (hreta : r ≤ eta / 2)
    (halpha : alpha + r < delta)
    (hzeros : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ delta)
    (hordinate : ∀ q : XiRightZeroCopy,
      eta ≤ |(xiRightCenteredZero q).im|) :
    DifferentiableOn ℂ (xiRectangularPowerUpperLandauContinuation L C alpha)
      (Metric.ball (((1 + delta : ℝ) : ℂ)) r) := by
  have hpower := differentiableOn_xiRectangularPowerLandauContinuation_landauBall
    L (-C) alpha hdelta0 hdeltahalf heta hr hrquarter hreta halpha hzeros hordinate
  have hneg := hpower.neg
  convert hneg using 1
  funext s
  simp only [Pi.neg_apply, xiRectangularPowerLandauContinuation,
    xiRectangularPowerUpperLandauContinuation]
  push_cast
  ring

/-- Landau transfer for an eventual upper power budget: the dual nonnegative series converges at
a real point strictly left of the transverse boundary. -/
theorem exists_xiRectangularPowerUpperLandauCoefficient_summable_left_of_boundary
    (L C alpha : ℝ) (hne : Nonempty XiRightZeroCopy)
    (halphaDelta : alpha < xiRightTransverseSup)
    (hupper : ∀ n : ℕ, n ≠ 0 →
      xiRectangularRightDirichletCoefficientReal L n ≤
        C * powerCorrectionCoefficient alpha n) :
    ∃ sigma : ℝ,
      1 + alpha < sigma ∧
      sigma < 1 + xiRightTransverseSup ∧
      LSeriesSummable
        (fun n => ((xiRectangularPowerUpperLandauCoefficient L C
          alpha n : ℝ) : ℂ)) (sigma : ℂ) := by
  let delta : ℝ := xiRightTransverseSup
  have hdelta : 0 < delta := xiRightTransverseSup_pos hne
  have hdeltahalf : delta ≤ 1 / 2 := xiRightTransverseSup_le_half hne
  have hzeros : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ delta :=
    fun q => xiRightCenteredZero_re_le_sup q
  obtain ⟨eta, heta, hordinate⟩ :=
    exists_xiRightCenteredZero_abs_im_lower_bound
  let r : ℝ := min (min (1 / 8) (eta / 4)) ((delta - alpha) / 4)
  have hr : 0 < r := by
    dsimp only [r]
    exact lt_min
      (lt_min (by norm_num) (div_pos heta (by norm_num)))
      (div_pos (sub_pos.mpr (by simpa only [delta] using halphaDelta)) (by norm_num))
  have hrquarter : r ≤ 1 / 4 :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (by norm_num))
  have hreta : r ≤ eta / 2 :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (by linarith))
  have hrgap : r ≤ (delta - alpha) / 4 := min_le_right _ _
  have halpha : alpha + r < delta := by
    have hgap : 0 < delta - alpha := by
      simpa only [delta] using sub_pos.mpr halphaDelta
    linarith
  have hcont :=
    differentiableOn_xiRectangularPowerUpperLandauContinuation_landauBall
      L C alpha hdelta.le hdeltahalf heta hr hrquarter hreta halpha
      hzeros hordinate
  let sigma1 : ℝ := 1 + delta + r / 8
  let h : ℝ := r / 8
  let R : NNReal := ⟨r / 2, div_nonneg hr.le (by norm_num)⟩
  let sigma : ℝ := 1 + delta - r / 8
  have hh : 0 < h := by dsimp only [h]; positivity
  have hsigma1delta : 1 + delta < sigma1 := by
    dsimp only [sigma1]
    linarith
  have hsigma1alpha : 1 + alpha < sigma1 := by
    dsimp only [sigma1]
    linarith
  have hsum : LSeriesSummable
      (fun n => ((xiRectangularPowerUpperLandauCoefficient L C alpha n : ℝ) : ℂ))
      (sigma1 : ℂ) := by
    apply xiRectangularPowerUpperLandauCoefficient_LSeriesSummable L C hzeros
    · simpa only [ofReal_re] using hsigma1delta
    · simpa only [ofReal_re] using hsigma1alpha
  have hGd : DifferentiableOn ℂ
      (xiRectangularPowerUpperLandauContinuation L C alpha)
      (Metric.closedBall ((sigma1 + h : ℝ) : ℂ) (R : ℝ)) := by
    apply hcont.mono
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm]
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hcenter :
        ‖(((sigma1 + h : ℝ) : ℂ) - (((1 + delta : ℝ) : ℂ)))‖ = r / 4 := by
      have heq : (((sigma1 + h : ℝ) : ℂ) - (((1 + delta : ℝ) : ℂ))) =
          ((r / 4 : ℝ) : ℂ) := by
        dsimp only [sigma1, h]
        push_cast
        ring
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
      positivity
    calc
      ‖z - (((1 + delta : ℝ) : ℂ))‖ ≤
          ‖z - (((sigma1 + h : ℝ) : ℂ))‖ +
            ‖(((sigma1 + h : ℝ) : ℂ) - (((1 + delta : ℝ) : ℂ)))‖ := by
        have := norm_add_le
          (z - (((sigma1 + h : ℝ) : ℂ)))
          ((((sigma1 + h : ℝ) : ℂ)) - (((1 + delta : ℝ) : ℂ)))
        simpa only [sub_add_sub_cancel] using this
      _ ≤ r / 2 + r / 4 := by
        rw [hcenter]
        exact add_le_add hz le_rfl
      _ < r := by linarith
  have hagree : ∀ s : ℂ, sigma1 < s.re →
      xiRectangularPowerUpperLandauContinuation L C alpha s =
        LSeries
          (fun n => ((xiRectangularPowerUpperLandauCoefficient L C alpha n : ℝ) : ℂ)) s := by
    intro s hsright
    symm
    apply LSeries_xiRectangularPowerUpperLandauCoefficient_eq_continuation
      L C hzeros
    · dsimp only [sigma1] at hsright
      linarith
    · dsimp only [sigma1] at hsright
      linarith
  have hnonneg := xiRectangularPowerUpperLandauCoefficient_nonneg hupper
  have hineq : sigma1 + h - (R : ℝ) < sigma := by
    change sigma1 + h - r / 2 < sigma
    dsimp only [sigma1, h, sigma]
    linarith
  have htransfer := landau_local_summability_transfer
    (a := xiRectangularPowerUpperLandauCoefficient L C alpha)
    hnonneg hh hsum (R := R)
    (G := xiRectangularPowerUpperLandauContinuation L C alpha) hGd hagree hineq
  refine ⟨sigma, ?_, ?_, ?_⟩
  · dsimp only [sigma, delta]
    have := hrgap
    linarith
  · dsimp only [sigma, delta]
    linarith
  · simpa only [delta] using htransfer

/-- A global upper power budget for the positive-transverse coefficient bounds the full transverse
supremum by the same exponent. -/
theorem xiRightTransverseSup_le_of_xiRectangularRightPowerUpper
    {L alpha C : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha)
    (hne : Nonempty XiRightZeroCopy)
    (hupper : ∀ n : ℕ, n ≠ 0 →
      xiRectangularRightDirichletCoefficientReal L n ≤
        C * powerCorrectionCoefficient alpha n) :
    xiRightTransverseSup ≤ alpha := by
  by_contra hnot
  have halphaDelta : alpha < xiRightTransverseSup := lt_of_not_ge hnot
  obtain ⟨sigma, hsigmaAlpha, hsigmaDelta, hsumUpper⟩ :=
    exists_xiRectangularPowerUpperLandauCoefficient_summable_left_of_boundary
      L C alpha hne halphaDelta hupper
  have hsigma : 1 < sigma := by linarith
  have hpower :=
    (powerCorrectionCoefficient_LSeriesSummable (s := (sigma : ℂ)) (by
      simpa only [ofReal_re] using hsigmaAlpha)).smul (C : ℂ)
  have horiginalRaw := hpower.sub hsumUpper
  have horiginal : LSeriesSummable
      (fun n => ((xiRectangularLandauCoefficient L 0 0 n : ℝ) : ℂ))
      (sigma : ℂ) := by
    change Summable (LSeries.term
      (fun n => ((xiRectangularLandauCoefficient L 0 0 n : ℝ) : ℂ))
      (sigma : ℂ))
    change Summable (LSeries.term _ (sigma : ℂ)) at horiginalRaw
    apply horiginalRaw.congr
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [LSeries.term_zero]
    · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
      rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        xiRectangularPowerUpperLandauCoefficient, if_neg hn0,
        xiRectangularLandauCoefficient, if_pos (Nat.zero_le n), add_zero]
      push_cast
      ring
  have hpoleBound : ∀ q : XiRightZeroCopy,
      (xiRightShiftedPole q).re ≤ sigma :=
    xiRightShiftedPole_re_le_of_landau_summable hL 0 0 hsigma
      (xiRightTransverseSup_pos hne).le
      (fun q => xiRightCenteredZero_re_le_sup q) horiginal
  have hcenterBound : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ sigma - 1 := by
    intro q
    have hq := hpoleBound q
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re] at hq
    linarith
  have hsupBound : xiRightTransverseSup ≤ sigma - 1 := by
    apply csSup_le (Set.range_nonempty _)
    intro x hx
    obtain ⟨q, rfl⟩ := hx
    exact hcenterBound q
  linarith

/-- False RH forces the actual fixed-window values above every positive subcritical power scale,
arbitrarily late on the logarithmic mesh. -/
theorem not_riemannHypothesis_implies_rectangular_weil_cofinally_unbounded_above_power
    {L alpha : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha)
    (hRH : ¬RiemannHypothesis) (halpha : alpha < xiRightTransverseSup) :
    ∀ C : ℝ, 0 ≤ C → ∀ N0 : ℕ, ∃ n : ℕ,
      N0 ≤ n ∧ L ≤ Real.log n / 2 ∧
      C * (n : ℝ) ^ alpha <
        (xiRectangularWeilLogCoefficient L n).re := by
  intro C hC N0
  have hne := nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
  by_contra hnot
  push Not at hnot
  obtain ⟨Nadm, hNadm⟩ := exists_xiRectangularAdmissibleCutoff L
  let N : ℕ := max N0 Nadm
  have heventObs : ∀ n : ℕ, N ≤ n →
      (xiRectangularWeilLogCoefficient L n).re ≤
        C * powerCorrectionCoefficient alpha n := by
    intro n hn
    have hn0 : N0 ≤ n := (le_max_left _ _).trans hn
    have hLa : L ≤ Real.log n / 2 := (hNadm n ((le_max_right _ _).trans hn)).2
    have hle := hnot n hn0 hLa
    have hn1 := (hNadm n ((le_max_right _ _).trans hn)).1
    have hnne : n ≠ 0 := by omega
    simpa only [powerCorrectionCoefficient, if_neg hnne] using hle
  let B : ℝ := rectangularTwoEdgeRemainderBound L *
    ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
  have hB : 0 ≤ B := mul_nonneg
    (by unfold rectangularTwoEdgeRemainderBound; positivity)
    (tsum_nonneg fun q => by positivity)
  have heventRight : ∀ n : ℕ, N ≤ n → n ≠ 0 →
      xiRectangularRightDirichletCoefficientReal L n ≤
        (C + B) * powerCorrectionCoefficient alpha n := by
    intro n hn hn0
    have hnNadm : Nadm ≤ n := (le_max_right _ _).trans hn
    have hn1 := (hNadm n hnNadm).1
    have hremNorm := norm_xiRectangularWeilRemainderCoefficient_le hNadm n
    have hremNeg :
        -(xiRectangularWeilRemainderCoefficient L Nadm n).re ≤ B :=
      (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hremNorm)
    have hremEq : xiRectangularWeilRemainderCoefficient L Nadm n =
        xiRectangularWeilLogCoefficient L n -
          (xiRectangularRightDirichletCoefficientReal L n : ℂ) := by
      rw [xiRectangularWeilRemainderCoefficient,
        xiRectangularWeilTailCoefficient, if_pos hnNadm,
        xiRectangularLandauPrefixCoefficient, if_neg (not_lt.mpr hnNadm), add_zero,
        ofReal_xiRectangularRightDirichletCoefficientReal]
    have hremReEq := congrArg Complex.re hremEq
    simp only [Complex.sub_re, ofReal_re] at hremReEq
    have hpone : 1 ≤ powerCorrectionCoefficient alpha n := by
      rw [powerCorrectionCoefficient, if_neg hn0]
      exact Real.one_le_rpow (by exact_mod_cast hn1) halpha0
    have hobs := heventObs n hn
    nlinarith [mul_le_mul_of_nonneg_left hpone hB]
  obtain ⟨D, hD, hglobalNeg⟩ := exists_global_power_lower_of_eventual
    (fun n => -xiRectangularRightDirichletCoefficientReal L n)
    halpha0 (add_nonneg hC hB) (by
      intro n hn hn0
      have := heventRight n hn hn0
      linarith)
  have hglobal : ∀ n : ℕ, n ≠ 0 →
      xiRectangularRightDirichletCoefficientReal L n ≤
        D * powerCorrectionCoefficient alpha n := by
    intro n hn0
    have := hglobalNeg n hn0
    linarith
  have hsup := xiRightTransverseSup_le_of_xiRectangularRightPowerUpper
    hL halpha0 hne hglobal
  linarith

/-- False RH also forces negative values below every negative subcritical power scale, arbitrarily
late on the logarithmic mesh. -/
theorem not_riemannHypothesis_implies_rectangular_weil_cofinally_unbounded_below_power
    {L alpha : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha)
    (hRH : ¬RiemannHypothesis) (halpha : alpha < xiRightTransverseSup) :
    ∀ C : ℝ, 0 ≤ C → ∀ N0 : ℕ, ∃ n : ℕ,
      N0 ≤ n ∧ L ≤ Real.log n / 2 ∧
      (xiRectangularWeilLogCoefficient L n).re <
        -(C * (n : ℝ) ^ alpha) := by
  intro C hC N0
  by_contra hnot
  push Not at hnot
  obtain ⟨Nadm, hNadm⟩ := exists_xiRectangularAdmissibleCutoff L
  let N : ℕ := max N0 Nadm
  have hfloor : XiRectangularWeilTailPowerLower L N alpha := by
    refine ⟨C, hC, ?_⟩
    intro n hn
    have hn0 : N0 ≤ n := (le_max_left _ _).trans hn
    have hnNadm : Nadm ≤ n := (le_max_right _ _).trans hn
    have hLa := (hNadm n hnNadm).2
    have hle := hnot n hn0 hLa
    have hn1 := (hNadm n hnNadm).1
    have hnne : n ≠ 0 := by omega
    rw [powerCorrectionCoefficient, if_neg hnne]
    linarith
  have hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2 := by
    intro n hn
    exact hNadm n ((le_max_right _ _).trans hn)
  have hsup := (xiRectangularWeilTailPowerLower_iff_transverseSup_le
    hL halpha0 (nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH)).1
    ⟨N, hN, hfloor⟩
  linarith

/-- **Exact two-sided oscillation law.**  Under false RH, for every exponent below the transverse
support endpoint, the normalized fixed-window samples are cofinally unbounded in both signs. -/
theorem not_riemannHypothesis_implies_rectangular_weil_twoSided_power_oscillation
    {L alpha : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha)
    (hRH : ¬RiemannHypothesis) (halpha : alpha < xiRightTransverseSup) :
    (∀ C : ℝ, 0 ≤ C → ∀ N0 : ℕ, ∃ n : ℕ,
      N0 ≤ n ∧ L ≤ Real.log n / 2 ∧
      (xiRectangularWeilLogCoefficient L n).re <
        -(C * (n : ℝ) ^ alpha)) ∧
    (∀ C : ℝ, 0 ≤ C → ∀ N0 : ℕ, ∃ n : ℕ,
      N0 ≤ n ∧ L ≤ Real.log n / 2 ∧
      C * (n : ℝ) ^ alpha <
        (xiRectangularWeilLogCoefficient L n).re) := by
  exact ⟨
    not_riemannHypothesis_implies_rectangular_weil_cofinally_unbounded_below_power
      hL halpha0 hRH halpha,
    not_riemannHypothesis_implies_rectangular_weil_cofinally_unbounded_above_power
      hL halpha0 hRH halpha⟩

end

end RHTower
