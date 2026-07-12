import GaloisForLFunctions.RHTower.CCMRectangularObservablePoleTomography
import GaloisForLFunctions.RHTower.CCMShiftedXiLandauPoleContradiction

/-!
# One-sided subpower lower control of the rectangular Weil tail

A uniform lower floor is far stronger than the rectangular Landau mechanism needs. This module
allows the observable fixed-width Weil values to drift to minus infinity at every prescribed
subpower rate. If `Q_L(n) >= -C_epsilon n^epsilon` eventually for every `epsilon > 0`, then RH.

Under false RH let `delta > 0` be the maximal transverse exponent and choose
`alpha = delta / 4`. Adding `C n^alpha` makes the tail coefficients nonnegative. Its Dirichlet
series differs from the rectangular shifted-zeta carrier by `C * zeta(s-alpha)`; that extra pole
lies strictly left of the real Landau ball at `1 + delta`. Local Landau transfer therefore forces
absolute convergence strictly left of `1 + delta`, and the exact pole-order contradiction bounds
every right Xi zero below its own transverse supremum.
-/

open Complex Filter Function Set

namespace RHTower

noncomputable section

def powerCorrectionCoefficient (alpha : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (n : ℝ) ^ alpha

theorem powerCorrectionCoefficient_nonneg (alpha : ℝ) (n : ℕ) :
    0 ≤ powerCorrectionCoefficient alpha n := by
  simp only [powerCorrectionCoefficient]
  split_ifs
  · exact le_rfl
  · positivity

theorem powerCorrectionCoefficient_LSeriesSummable
    {alpha : ℝ} {s : ℂ} (hs : 1 + alpha < s.re) :
    LSeriesSummable (fun n => ((powerCorrectionCoefficient alpha n : ℝ) : ℂ)) s := by
  apply LSeriesSummable_of_le_const_mul_rpow (x := 1 + alpha) hs
  refine ⟨1, fun n hn => ?_⟩
  rw [powerCorrectionCoefficient, if_neg hn, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) alpha)]
  ring_nf
  exact le_rfl

theorem LSeries_powerCorrectionCoefficient_eq_riemannZeta
    {alpha : ℝ} {s : ℂ} (hs : 1 + alpha < s.re) :
    LSeries (fun n => ((powerCorrectionCoefficient alpha n : ℝ) : ℂ)) s =
      riemannZeta (s - alpha) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by simp only [Complex.sub_re, ofReal_re]; linarith)]
  unfold LSeries
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero, powerCorrectionCoefficient]
    have hexp : s - (alpha : ℂ) ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      simp only [Complex.sub_re, ofReal_re, Complex.zero_re] at hre
      linarith
    rw [show ((0 : ℕ) : ℂ) = 0 by norm_num, Complex.zero_cpow hexp, div_zero]
  · rw [LSeries.term_of_ne_zero hn, powerCorrectionCoefficient, if_neg hn]
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [Complex.cpow_sub _ _ hnC]
    have hna : (n : ℂ) ^ (alpha : ℂ) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
    have hns : (n : ℂ) ^ s ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
    calc
      (((n : ℝ) ^ alpha : ℝ) : ℂ) / (n : ℂ) ^ s =
          (n : ℂ) ^ (alpha : ℂ) / (n : ℂ) ^ s := by
            exact congrArg (fun z : ℂ => z / (n : ℂ) ^ s)
              (Complex.ofReal_cpow (Nat.cast_nonneg n) alpha)
      _ = 1 / ((n : ℂ) ^ s / (n : ℂ) ^ (alpha : ℂ)) := by
            field_simp

def xiRectangularPowerLandauCoefficient
    (L C alpha : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    xiRectangularRightDirichletCoefficientReal L n +
      C * powerCorrectionCoefficient alpha n

theorem xiRectangularPowerLandauCoefficient_nonneg
    {L C alpha : ℝ}
    (hlower : ∀ n : ℕ, n ≠ 0 →
      0 ≤ xiRectangularRightDirichletCoefficientReal L n +
        C * powerCorrectionCoefficient alpha n) :
    ∀ n, 0 ≤ xiRectangularPowerLandauCoefficient L C alpha n := by
  intro n
  rw [xiRectangularPowerLandauCoefficient]
  split_ifs with hn
  · exact le_rfl
  · exact hlower n hn

theorem xiRectangularPowerLandauCoefficient_LSeriesSummable
    (L C : ℝ) {alpha delta : ℝ}
    (hupper : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ delta)
    {s : ℂ} (hsdelta : 1 + delta < s.re)
    (hsalpha : 1 + alpha < s.re) :
    LSeriesSummable
      (fun n => ((xiRectangularPowerLandauCoefficient L C alpha n : ℝ) : ℂ)) s := by
  have hfull := xiRectangularRightDirichletComplex_LSeriesSummable L hupper hsdelta
  have hpower := (powerCorrectionCoefficient_LSeriesSummable hsalpha).smul (C : ℂ)
  have hadd : LSeriesSummable
      ((fun n => xiRectangularRightDirichletComplex L n) +
        (C : ℂ) • (fun n => ((powerCorrectionCoefficient alpha n : ℝ) : ℂ))) s :=
    hfull.add hpower
  change Summable (LSeries.term
    (fun n => ((xiRectangularPowerLandauCoefficient L C alpha n : ℝ) : ℂ)) s)
  change Summable (LSeries.term _ s) at hadd
  apply hadd.congr
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [LSeries.term_zero]
  · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      xiRectangularPowerLandauCoefficient, if_neg hn0,
      ofReal_add, ofReal_mul,
      ofReal_xiRectangularRightDirichletCoefficientReal]

theorem LSeries_xiRectangularPowerLandauCoefficient_eq_continuation
    (L C : ℝ) {alpha delta : ℝ}
    (hupper : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ delta)
    {s : ℂ} (hsdelta : 1 + delta < s.re)
    (hsalpha : 1 + alpha < s.re) :
    LSeries
        (fun n => ((xiRectangularPowerLandauCoefficient L C alpha n : ℝ) : ℂ)) s =
      2 * xiRectangularShiftedZetaSeries L s +
        C * riemannZeta (s - alpha) := by
  have hfull := xiRectangularRightDirichletComplex_LSeriesSummable L hupper hsdelta
  have hpower0 := powerCorrectionCoefficient_LSeriesSummable hsalpha
  have hpower := hpower0.smul (C : ℂ)
  calc
    LSeries
        (fun n => ((xiRectangularPowerLandauCoefficient L C alpha n : ℝ) : ℂ)) s =
        LSeries ((fun n => xiRectangularRightDirichletComplex L n) +
          (C : ℂ) • (fun n => ((powerCorrectionCoefficient alpha n : ℝ) : ℂ))) s := by
      apply LSeries_congr
      intro n hn
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        xiRectangularPowerLandauCoefficient, if_neg hn,
        ofReal_add, ofReal_mul,
        ofReal_xiRectangularRightDirichletCoefficientReal]
    _ = LSeries (fun n => xiRectangularRightDirichletComplex L n) s +
        LSeries ((C : ℂ) •
          (fun n => ((powerCorrectionCoefficient alpha n : ℝ) : ℂ))) s :=
      LSeries_add hfull hpower
    _ = 2 * xiRectangularShiftedZetaSeries L s +
        C * LSeries (fun n => ((powerCorrectionCoefficient alpha n : ℝ) : ℂ)) s := by
      rw [LSeries_xiRectangularRightDirichletComplex_eq_shiftedZeta L hupper hsdelta,
        LSeries_smul]
    _ = 2 * xiRectangularShiftedZetaSeries L s +
        C * riemannZeta (s - alpha) := by
      rw [LSeries_powerCorrectionCoefficient_eq_riemannZeta hsalpha]

def xiRectangularPowerLandauContinuation
    (L C alpha : ℝ) (s : ℂ) : ℂ :=
  2 * xiRectangularShiftedZetaSeries L s +
    C * riemannZeta (s - alpha)

theorem differentiableOn_xiRectangularPowerLandauContinuation_landauBall
    (L C alpha : ℝ) {delta eta r : ℝ}
    (hdelta0 : 0 ≤ delta) (hdeltahalf : delta ≤ 1 / 2)
    (heta : 0 < eta) (hr : 0 < r)
    (hrquarter : r ≤ 1 / 4) (hreta : r ≤ eta / 2)
    (halpha : alpha + r < delta)
    (hupper : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ delta)
    (hordinate : ∀ q : XiRightZeroCopy,
      eta ≤ |(xiRightCenteredZero q).im|) :
    DifferentiableOn ℂ (xiRectangularPowerLandauContinuation L C alpha)
      (Metric.ball (((1 + delta : ℝ) : ℂ)) r) := by
  have hshift := differentiableOn_xiRectangularShiftedZetaSeries_landauBall L
    hdelta0 hdeltahalf heta hr hrquarter hreta hupper hordinate
  intro s hs
  have hdist : ‖s - (((1 + delta : ℝ) : ℂ))‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hs
  have hre : 1 + alpha < s.re := by
    have habs := Complex.abs_re_le_norm (s - (((1 + delta : ℝ) : ℂ)))
    rw [Complex.sub_re, ofReal_re] at habs
    have hlower : -r < s.re - (1 + delta) := by
      have := lt_of_le_of_lt habs hdist
      rw [abs_lt] at this
      exact this.1
    linarith
  have hne : s - (alpha : ℂ) ≠ 1 := by
    intro heq
    have hreeq := congrArg Complex.re heq
    simp only [Complex.sub_re, ofReal_re, Complex.one_re] at hreeq
    linarith
  have hzeta : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (z - alpha)) s :=
    (differentiableAt_riemannZeta hne).comp s
      (differentiableAt_id.sub (differentiableAt_const (c := (alpha : ℂ))))
  simpa only [xiRectangularPowerLandauContinuation] using
    ((hshift s hs).const_mul (2 : ℂ)).add
      (hzeta.differentiableWithinAt.const_mul (C : ℂ))

theorem exists_xiRectangularPowerLandauCoefficient_summable_left_of_boundary
    (L C alpha : ℝ) (hne : Nonempty XiRightZeroCopy)
    (halphaDelta : alpha < xiRightTransverseSup)
    (hlower : ∀ n : ℕ, n ≠ 0 →
      0 ≤ xiRectangularRightDirichletCoefficientReal L n +
        C * powerCorrectionCoefficient alpha n) :
    ∃ sigma : ℝ,
      1 + alpha < sigma ∧
      sigma < 1 + xiRightTransverseSup ∧
      LSeriesSummable
        (fun n => ((xiRectangularPowerLandauCoefficient L C
          alpha n : ℝ) : ℂ)) (sigma : ℂ) := by
  let delta : ℝ := xiRightTransverseSup
  have hdelta : 0 < delta := xiRightTransverseSup_pos hne
  have hdeltahalf : delta ≤ 1 / 2 := xiRightTransverseSup_le_half hne
  have hupper : ∀ q : XiRightZeroCopy,
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
    differentiableOn_xiRectangularPowerLandauContinuation_landauBall
      L C alpha hdelta.le hdeltahalf heta hr hrquarter hreta halpha
      hupper hordinate
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
      (fun n => ((xiRectangularPowerLandauCoefficient L C alpha n : ℝ) : ℂ))
      (sigma1 : ℂ) := by
    apply xiRectangularPowerLandauCoefficient_LSeriesSummable L C hupper
    · simpa only [ofReal_re] using hsigma1delta
    · simpa only [ofReal_re] using hsigma1alpha
  have hGd : DifferentiableOn ℂ
      (xiRectangularPowerLandauContinuation L C alpha)
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
      xiRectangularPowerLandauContinuation L C alpha s =
        LSeries
          (fun n => ((xiRectangularPowerLandauCoefficient L C alpha n : ℝ) : ℂ)) s := by
    intro s hsright
    symm
    apply LSeries_xiRectangularPowerLandauCoefficient_eq_continuation
      L C hupper
    · dsimp only [sigma1] at hsright
      linarith
    · dsimp only [sigma1] at hsright
      linarith
  have hnonneg := xiRectangularPowerLandauCoefficient_nonneg hlower
  have hineq : sigma1 + h - (R : ℝ) < sigma := by
    change sigma1 + h - r / 2 < sigma
    dsimp only [sigma1, h, sigma]
    linarith
  have htransfer := landau_local_summability_transfer
    (a := xiRectangularPowerLandauCoefficient L C alpha)
    hnonneg hh hsum (R := R)
    (G := xiRectangularPowerLandauContinuation L C alpha) hGd hagree hineq
  refine ⟨sigma, ?_, ?_, ?_⟩
  · dsimp only [sigma, delta]
    have := hrgap
    linarith
  · dsimp only [sigma, delta]
    linarith
  · simpa only [delta] using htransfer

/-- One-sided subpower lower control of the positive-transverse rectangular coefficient. -/
def XiRectangularRightSubpowerLower (L : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, n ≠ 0 →
      0 ≤ xiRectangularRightDirichletCoefficientReal L n +
        C * powerCorrectionCoefficient epsilon n

theorem exists_global_power_lower_of_eventual
    (a : ℕ → ℝ) {alpha C : ℝ} {N : ℕ}
    (halpha : 0 ≤ alpha) (hC : 0 ≤ C)
    (hlower : ∀ n : ℕ, N ≤ n → n ≠ 0 →
      0 ≤ a n + C * powerCorrectionCoefficient alpha n) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, n ≠ 0 →
      0 ≤ a n + D * powerCorrectionCoefficient alpha n := by
  let F : ℝ := ∑ k ∈ Finset.range N, |a k|
  let D : ℝ := C + F
  have hF : 0 ≤ F := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hD : 0 ≤ D := add_nonneg hC hF
  refine ⟨D, hD, ?_⟩
  intro n hn0
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hpnonneg : 0 ≤ powerCorrectionCoefficient alpha n :=
    powerCorrectionCoefficient_nonneg alpha n
  have hpone : 1 ≤ powerCorrectionCoefficient alpha n := by
    rw [powerCorrectionCoefficient, if_neg hn0]
    exact Real.one_le_rpow (by exact_mod_cast hn1) halpha
  by_cases hnN : N ≤ n
  · have hbase := hlower n hnN hn0
    have hCD : C ≤ D := by dsimp only [D]; linarith
    nlinarith [mul_le_mul_of_nonneg_right hCD hpnonneg]
  · have hnmem : n ∈ Finset.range N := Finset.mem_range.mpr (Nat.lt_of_not_ge hnN)
    have habsF : |a n| ≤ F := by
      dsimp only [F]
      exact Finset.single_le_sum
        (fun k hk => abs_nonneg (a k)) hnmem
    have hFD : F ≤ D := by dsimp only [D]; linarith
    have hDmul : F ≤ D * powerCorrectionCoefficient alpha n := by
      calc
        F ≤ D := hFD
        _ ≤ D * powerCorrectionCoefficient alpha n := by
          nlinarith [mul_le_mul_of_nonneg_left hpone hD]
    have hneg : -a n ≤ |a n| := neg_le_abs (a n)
    linarith

theorem riemannHypothesis_of_xiRectangularRightSubpowerLower
    {L : ℝ} (hL : 0 < L)
    (hlower : XiRectangularRightSubpowerLower L) :
    RiemannHypothesis := by
  by_contra hRH
  have hne : Nonempty XiRightZeroCopy :=
    nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
  let delta : ℝ := xiRightTransverseSup
  let alpha : ℝ := delta / 4
  have hdelta : 0 < delta := xiRightTransverseSup_pos hne
  have halpha : 0 < alpha := by dsimp only [alpha]; positivity
  obtain ⟨C, hC, hcoeffLower⟩ := hlower alpha halpha
  have hcoeffLower' : ∀ n : ℕ, n ≠ 0 →
      0 ≤ xiRectangularRightDirichletCoefficientReal L n +
        C * powerCorrectionCoefficient (xiRightTransverseSup / 4) n := by
    simpa only [alpha, delta] using hcoeffLower
  obtain ⟨sigma, hsigmaAlpha, hsigmaDelta, hsumPower⟩ :=
    exists_xiRectangularPowerLandauCoefficient_summable_left_of_boundary
      L C (xiRightTransverseSup / 4)
        hne (by
          have := xiRightTransverseSup_pos hne
          linarith) hcoeffLower'
  have hsigma : 1 < sigma := by
    have : 0 < xiRightTransverseSup / 4 := by positivity
    linarith
  have hpower : LSeriesSummable
      (fun n => ((powerCorrectionCoefficient (xiRightTransverseSup / 4) n : ℝ) : ℂ))
      (sigma : ℂ) := by
    apply powerCorrectionCoefficient_LSeriesSummable
    simpa only [ofReal_re] using hsigmaAlpha
  have hscaled := hpower.smul (C : ℂ)
  have hdiff := hsumPower.sub hscaled
  have horiginal : LSeriesSummable
      (fun n => ((xiRectangularLandauCoefficient L 0 0 n : ℝ) : ℂ))
      (sigma : ℂ) := by
    change Summable (LSeries.term
      (fun n => ((xiRectangularLandauCoefficient L 0 0 n : ℝ) : ℂ))
      (sigma : ℂ))
    change Summable (LSeries.term _ (sigma : ℂ)) at hdiff
    apply hdiff.congr
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [LSeries.term_zero]
    · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
      rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        xiRectangularPowerLandauCoefficient, if_neg hn0,
        xiRectangularLandauCoefficient, if_pos (Nat.zero_le n)]
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

/-- One-sided subpower lower control of the actual observable rectangular Weil tail. -/
def XiRectangularWeilTailSubpowerLower (L : ℝ) (N : ℕ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
      0 ≤ (xiRectangularWeilLogCoefficient L n).re +
        C * powerCorrectionCoefficient epsilon n

theorem riemannHypothesis_of_xiRectangularWeilTailSubpowerLower
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (hlower : XiRectangularWeilTailSubpowerLower L N) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiRectangularRightSubpowerLower hL
  intro epsilon hepsilon
  obtain ⟨C, hC, hobs⟩ := hlower epsilon hepsilon
  let B : ℝ := rectangularTwoEdgeRemainderBound L *
    ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
  have hB : 0 ≤ B := mul_nonneg
    (by unfold rectangularTwoEdgeRemainderBound; positivity)
    (tsum_nonneg fun q => by positivity)
  have hevent : ∀ n : ℕ, N ≤ n → n ≠ 0 →
      0 ≤ xiRectangularRightDirichletCoefficientReal L n +
        (C + B) * powerCorrectionCoefficient epsilon n := by
    intro n hnN hn0
    obtain ⟨hn1, hLa⟩ := hN n hnN
    have hremNorm := norm_xiRectangularWeilRemainderCoefficient_le hN n
    have hremRe :
        (xiRectangularWeilRemainderCoefficient L N n).re ≤ B :=
      (Complex.re_le_norm _).trans hremNorm
    have hremEq : xiRectangularWeilRemainderCoefficient L N n =
        xiRectangularWeilLogCoefficient L n -
          (xiRectangularRightDirichletCoefficientReal L n : ℂ) := by
      rw [xiRectangularWeilRemainderCoefficient,
        xiRectangularWeilTailCoefficient, if_pos hnN,
        xiRectangularLandauPrefixCoefficient, if_neg (not_lt.mpr hnN), add_zero,
        ofReal_xiRectangularRightDirichletCoefficientReal]
    have hremReEq := congrArg Complex.re hremEq
    simp only [Complex.sub_re, ofReal_re] at hremReEq
    have hpone : 1 ≤ powerCorrectionCoefficient epsilon n := by
      rw [powerCorrectionCoefficient, if_neg hn0]
      exact Real.one_le_rpow (by exact_mod_cast hn1) hepsilon.le
    have hobsn := hobs n hnN
    nlinarith [mul_le_mul_of_nonneg_left hpone hB]
  obtain ⟨D, hD, hglobal⟩ := exists_global_power_lower_of_eventual
    (fun n => xiRectangularRightDirichletCoefficientReal L n)
    hepsilon.le (add_nonneg hC hB) hevent
  exact ⟨D, hD, hglobal⟩

end

end RHTower
