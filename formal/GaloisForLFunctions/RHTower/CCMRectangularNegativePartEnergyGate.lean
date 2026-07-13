import GaloisForLFunctions.RHTower.CCMRectangularPowerLowerZeroFree

/-!
# Summable negative rectangular energy proves RH

Pointwise subpower control is stronger than the local Landau mechanism needs.  It is enough that
the negative part of the rectangular divisor carrier have an L-series convergent at every real
point strictly to the right of one.  Adding that negative part makes the coefficients
nonnegative, while its own L-series remains holomorphic on the Landau ball around the rightmost
transverse Xi pole.
-/

open Complex Filter Function Set LSeries

namespace RHTower

noncomputable section

/-- The negative part of the positive-transverse rectangular carrier. -/
def xiRectangularRightNegativePart (L : ℝ) (n : ℕ) : ℝ :=
  (xiRectangularRightDirichletCoefficientReal L n)⁻

theorem xiRectangularRightNegativePart_nonneg (L : ℝ) (n : ℕ) :
    0 ≤ xiRectangularRightNegativePart L n :=
  negPart_nonneg _

/-- Adding the negative part replaces a real coefficient by its positive part. -/
def xiRectangularNegativePartLandauCoefficient (L : ℝ) (n : ℕ) : ℝ :=
  xiRectangularRightDirichletCoefficientReal L n +
    xiRectangularRightNegativePart L n

theorem xiRectangularNegativePartLandauCoefficient_nonneg (L : ℝ) :
    ∀ n, 0 ≤ xiRectangularNegativePartLandauCoefficient L n := by
  intro n
  have hpos := posPart_nonneg (xiRectangularRightDirichletCoefficientReal L n)
  have hdecomp := posPart_sub_negPart
    (xiRectangularRightDirichletCoefficientReal L n)
  dsimp only [xiRectangularNegativePartLandauCoefficient,
    xiRectangularRightNegativePart]
  linarith

/-- Dirichlet-energy hypothesis: the negative carrier has absolute L-series convergence at every
real abscissa `1 + ε`, `ε > 0`. -/
def XiRectangularRightNegativePartEnergy (L : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    LSeriesSummable
      (fun n => ((xiRectangularRightNegativePart L n : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ))

theorem xiRectangularNegativePartLandauCoefficient_LSeriesSummable
    (L : ℝ) {delta : ℝ}
    (hupper : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ delta)
    {s : ℂ} (hsdelta : 1 + delta < s.re)
    (hcorr : LSeriesSummable
      (fun n => ((xiRectangularRightNegativePart L n : ℝ) : ℂ)) s) :
    LSeriesSummable
      (fun n => ((xiRectangularNegativePartLandauCoefficient L n : ℝ) : ℂ)) s := by
  have hfull := xiRectangularRightDirichletComplex_LSeriesSummable L hupper hsdelta
  have hadd : LSeriesSummable
      ((fun n => xiRectangularRightDirichletComplex L n) +
        (fun n => ((xiRectangularRightNegativePart L n : ℝ) : ℂ))) s :=
    hfull.add hcorr
  change Summable (LSeries.term
    (fun n => ((xiRectangularNegativePartLandauCoefficient L n : ℝ) : ℂ)) s)
  change Summable (LSeries.term _ s) at hadd
  apply hadd.congr
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [LSeries.term_zero]
  · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
    simp only [Pi.add_apply, xiRectangularNegativePartLandauCoefficient,
      ofReal_add, ofReal_xiRectangularRightDirichletCoefficientReal]

def xiRectangularNegativePartLandauContinuation (L : ℝ) (s : ℂ) : ℂ :=
  2 * xiRectangularShiftedZetaSeries L s +
    LSeries (fun n => ((xiRectangularRightNegativePart L n : ℝ) : ℂ)) s

theorem LSeries_xiRectangularNegativePartLandauCoefficient_eq_continuation
    (L : ℝ) {delta : ℝ}
    (hupper : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ delta)
    {s : ℂ} (hsdelta : 1 + delta < s.re)
    (hcorr : LSeriesSummable
      (fun n => ((xiRectangularRightNegativePart L n : ℝ) : ℂ)) s) :
    LSeries
        (fun n => ((xiRectangularNegativePartLandauCoefficient L n : ℝ) : ℂ)) s =
      xiRectangularNegativePartLandauContinuation L s := by
  have hfull := xiRectangularRightDirichletComplex_LSeriesSummable L hupper hsdelta
  calc
    LSeries
        (fun n => ((xiRectangularNegativePartLandauCoefficient L n : ℝ) : ℂ)) s =
        LSeries ((fun n => xiRectangularRightDirichletComplex L n) +
          (fun n => ((xiRectangularRightNegativePart L n : ℝ) : ℂ))) s := by
      apply LSeries_congr
      intro n hn
      simp only [Pi.add_apply, xiRectangularNegativePartLandauCoefficient,
        ofReal_add, ofReal_xiRectangularRightDirichletCoefficientReal]
    _ = LSeries (fun n => xiRectangularRightDirichletComplex L n) s +
        LSeries (fun n => ((xiRectangularRightNegativePart L n : ℝ) : ℂ)) s :=
      LSeries_add hfull hcorr
    _ = xiRectangularNegativePartLandauContinuation L s := by
      rw [LSeries_xiRectangularRightDirichletComplex_eq_shiftedZeta L hupper hsdelta]
      rfl

theorem differentiableOn_xiRectangularNegativePartLandauContinuation_landauBall
    (L beta : ℝ) {delta eta r : ℝ}
    (hdelta0 : 0 ≤ delta) (hdeltahalf : delta ≤ 1 / 2)
    (heta : 0 < eta) (hr : 0 < r)
    (hrquarter : r ≤ 1 / 4) (hreta : r ≤ eta / 2)
    (hbeta : beta + r < delta)
    (hupper : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ delta)
    (hordinate : ∀ q : XiRightZeroCopy,
      eta ≤ |(xiRightCenteredZero q).im|)
    (hcorr : LSeriesSummable
      (fun n => ((xiRectangularRightNegativePart L n : ℝ) : ℂ))
      (((1 + beta : ℝ) : ℂ))) :
    DifferentiableOn ℂ (xiRectangularNegativePartLandauContinuation L)
      (Metric.ball (((1 + delta : ℝ) : ℂ)) r) := by
  have hshift := differentiableOn_xiRectangularShiftedZetaSeries_landauBall L
    hdelta0 hdeltahalf heta hr hrquarter hreta hupper hordinate
  have habsc : abscissaOfAbsConv
      (fun n => ((xiRectangularRightNegativePart L n : ℝ) : ℂ)) ≤
      ((1 + beta : ℝ) : EReal) := hcorr.abscissaOfAbsConv_le
  intro s hs
  have hdist : ‖s - (((1 + delta : ℝ) : ℂ))‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hs
  have hre : 1 + beta < s.re := by
    have habs := Complex.abs_re_le_norm (s - (((1 + delta : ℝ) : ℂ)))
    rw [Complex.sub_re, ofReal_re] at habs
    have hlower : -r < s.re - (1 + delta) := by
      have := lt_of_le_of_lt habs hdist
      rw [abs_lt] at this
      exact this.1
    linarith
  have habslt : abscissaOfAbsConv
      (fun n => ((xiRectangularRightNegativePart L n : ℝ) : ℂ)) <
      (s.re : EReal) := by
    refine habsc.trans_lt ?_
    exact_mod_cast hre
  have hcorrDiff : DifferentiableAt ℂ
      (LSeries (fun n => ((xiRectangularRightNegativePart L n : ℝ) : ℂ))) s :=
    (LSeries_hasDerivAt habslt).differentiableAt
  simpa only [xiRectangularNegativePartLandauContinuation] using
    ((hshift s hs).const_mul (2 : ℂ)).add hcorrDiff.differentiableWithinAt

theorem exists_xiRectangularNegativePartLandauCoefficient_summable_left_of_boundary
    (L : ℝ) (hne : Nonempty XiRightZeroCopy)
    (henergy : XiRectangularRightNegativePartEnergy L) :
    ∃ beta sigma : ℝ,
      0 < beta ∧
      1 + beta < sigma ∧
      sigma < 1 + xiRightTransverseSup ∧
      LSeriesSummable
        (fun n => ((xiRectangularNegativePartLandauCoefficient L n : ℝ) : ℂ))
        (sigma : ℂ) := by
  let delta : ℝ := xiRightTransverseSup
  let beta : ℝ := delta / 4
  have hdelta : 0 < delta := xiRightTransverseSup_pos hne
  have hdeltahalf : delta ≤ 1 / 2 := xiRightTransverseSup_le_half hne
  have hbeta0 : 0 < beta := by dsimp only [beta]; positivity
  have hbetaDelta : beta < delta := by dsimp only [beta]; linarith
  have hupper : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ delta :=
    fun q => xiRightCenteredZero_re_le_sup q
  obtain ⟨eta, heta, hordinate⟩ :=
    exists_xiRightCenteredZero_abs_im_lower_bound
  have hcorrBase : LSeriesSummable
      (fun n => ((xiRectangularRightNegativePart L n : ℝ) : ℂ))
      (((1 + beta : ℝ) : ℂ)) := henergy beta hbeta0
  let r : ℝ := min (min (1 / 8) (eta / 4)) ((delta - beta) / 4)
  have hr : 0 < r := by
    dsimp only [r]
    exact lt_min
      (lt_min (by norm_num) (div_pos heta (by norm_num)))
      (div_pos (sub_pos.mpr hbetaDelta) (by norm_num))
  have hrquarter : r ≤ 1 / 4 :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (by norm_num))
  have hreta : r ≤ eta / 2 :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (by linarith))
  have hrgap : r ≤ (delta - beta) / 4 := min_le_right _ _
  have hbetaGap : beta + r < delta := by
    have hgap : 0 < delta - beta := sub_pos.mpr hbetaDelta
    linarith
  have hcont :=
    differentiableOn_xiRectangularNegativePartLandauContinuation_landauBall
      L beta hdelta.le hdeltahalf heta hr hrquarter hreta hbetaGap
      hupper hordinate hcorrBase
  let sigma1 : ℝ := 1 + delta + r / 8
  let h : ℝ := r / 8
  let R : NNReal := ⟨r / 2, div_nonneg hr.le (by norm_num)⟩
  let sigma : ℝ := 1 + delta - r / 8
  have hh : 0 < h := by dsimp only [h]; positivity
  have hsigma1delta : 1 + delta < sigma1 := by
    dsimp only [sigma1]
    linarith
  have hsigma1beta : 1 + beta < sigma1 := by
    dsimp only [sigma1]
    linarith
  have hcorrSigma1 : LSeriesSummable
      (fun n => ((xiRectangularRightNegativePart L n : ℝ) : ℂ))
      (sigma1 : ℂ) :=
    hcorrBase.of_re_le_re (by simpa only [ofReal_re] using hsigma1beta.le)
  have hsum : LSeriesSummable
      (fun n => ((xiRectangularNegativePartLandauCoefficient L n : ℝ) : ℂ))
      (sigma1 : ℂ) := by
    apply xiRectangularNegativePartLandauCoefficient_LSeriesSummable L hupper
    · simpa only [ofReal_re] using hsigma1delta
    · exact hcorrSigma1
  have hGd : DifferentiableOn ℂ
      (xiRectangularNegativePartLandauContinuation L)
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
      xiRectangularNegativePartLandauContinuation L s =
        LSeries
          (fun n => ((xiRectangularNegativePartLandauCoefficient L n : ℝ) : ℂ)) s := by
    intro s hsright
    have hcorrS : LSeriesSummable
        (fun n => ((xiRectangularRightNegativePart L n : ℝ) : ℂ)) s :=
      hcorrBase.of_re_le_re (by
        simp only [ofReal_re]
        exact (hsigma1beta.trans hsright).le)
    symm
    apply LSeries_xiRectangularNegativePartLandauCoefficient_eq_continuation
      L hupper
    · dsimp only [sigma1] at hsright
      linarith
    · exact hcorrS
  have hineq : sigma1 + h - (R : ℝ) < sigma := by
    change sigma1 + h - r / 2 < sigma
    dsimp only [sigma1, h, sigma]
    linarith
  have htransfer := landau_local_summability_transfer
    (a := xiRectangularNegativePartLandauCoefficient L)
    (xiRectangularNegativePartLandauCoefficient_nonneg L)
    hh hsum (R := R)
    (G := xiRectangularNegativePartLandauContinuation L) hGd hagree hineq
  refine ⟨beta, sigma, hbeta0, ?_, ?_, ?_⟩
  · dsimp only [sigma]
    have hgap : 0 < delta - beta := sub_pos.mpr hbetaDelta
    linarith
  · dsimp only [sigma, delta]
    linarith
  · simpa only [delta] using htransfer

/-- Summable negative Dirichlet energy of one rectangular carrier proves RH. -/
theorem riemannHypothesis_of_xiRectangularRightNegativePartEnergy
    {L : ℝ} (hL : 0 < L)
    (henergy : XiRectangularRightNegativePartEnergy L) :
    RiemannHypothesis := by
  by_contra hRH
  have hne : Nonempty XiRightZeroCopy :=
    nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
  obtain ⟨beta, sigma, hbeta, hsigmaBeta, hsigmaDelta, hsumCorrected⟩ :=
    exists_xiRectangularNegativePartLandauCoefficient_summable_left_of_boundary
      L hne henergy
  have hcorr : LSeriesSummable
      (fun n => ((xiRectangularRightNegativePart L n : ℝ) : ℂ))
      (sigma : ℂ) :=
    (henergy beta hbeta).of_re_le_re
      (by simpa only [ofReal_re] using hsigmaBeta.le)
  have hdiff := hsumCorrected.sub hcorr
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
      simp only [Pi.sub_apply, xiRectangularNegativePartLandauCoefficient,
        xiRectangularLandauCoefficient, if_pos (Nat.zero_le n)]
      push_cast
      ring
  have hsigma : 1 < sigma := by linarith
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

/-! ## Observable negative energy -/

/-- The negative-part map is one-Lipschitz in the one-sided form needed to absorb a bounded
observable remainder. -/
theorem negPart_le_negPart_add_of_abs_sub_le
    (x y B : ℝ) (h : |x - y| ≤ B) :
    x⁻ ≤ y⁻ + B := by
  change max (-x) 0 ≤ max (-y) 0 + B
  rcases le_total 0 (-x) with hx | hx
  · rw [max_eq_left hx]
    rcases le_total 0 (-y) with hy | hy
    · rw [max_eq_left hy]
      rw [abs_le] at h
      linarith
    · rw [max_eq_right hy]
      rw [abs_le] at h
      linarith
  · rw [max_eq_right hx]
    exact add_nonneg (negPart_nonneg y) (by
      rw [abs_le] at h
      linarith)

/-- Pointwise domination between nonnegative real coefficients preserves real-abscissa L-series
summability. -/
theorem LSeriesSummable_of_nonneg_of_le
    {f g : ℕ → ℝ} {sigma : ℝ}
    (hf : ∀ n, 0 ≤ f n) (hg0 : ∀ n, 0 ≤ g n)
    (hle : ∀ n, f n ≤ g n)
    (hg : LSeriesSummable (fun n => ((g n : ℝ) : ℂ)) (sigma : ℂ)) :
    LSeriesSummable (fun n => ((f n : ℝ) : ℂ)) (sigma : ℂ) := by
  change Summable (LSeries.term (fun n => ((f n : ℝ) : ℂ)) (sigma : ℂ))
  have hgnorm := hg.norm
  apply hgnorm.of_norm_bounded
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero, norm_zero, le_refl]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      norm_div, norm_div, norm_real, norm_real,
      Real.norm_of_nonneg (hf n), Real.norm_of_nonneg (hg0 n)]
    exact div_le_div_of_nonneg_right (hle n) (norm_nonneg _)

/-- Negative part of the actual rectangular Weil tail after deleting its finite prefix. -/
def xiRectangularWeilTailNegativePart (L : ℝ) (N n : ℕ) : ℝ :=
  ((xiRectangularWeilTailCoefficient L N n).re)⁻

theorem xiRectangularWeilTailNegativePart_nonneg (L : ℝ) (N n : ℕ) :
    0 ≤ xiRectangularWeilTailNegativePart L N n :=
  negPart_nonneg _

/-- Source-facing negative-energy condition for one observable rectangular family. -/
def XiRectangularWeilTailNegativePartEnergy (L : ℝ) (N : ℕ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    LSeriesSummable
      (fun n => ((xiRectangularWeilTailNegativePart L N n : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ))

private def xiRectangularObservableNegativePartMajorant
    (L : ℝ) (N n : ℕ) : ℝ :=
  xiRectangularWeilTailNegativePart L N n +
    ‖xiRectangularLandauPrefixCoefficient L 0 N n‖ +
      ‖xiRectangularWeilRemainderCoefficient L N n‖

private theorem xiRectangularObservableNegativePartMajorant_nonneg
    (L : ℝ) (N n : ℕ) :
    0 ≤ xiRectangularObservableNegativePartMajorant L N n := by
  unfold xiRectangularObservableNegativePartMajorant
  exact add_nonneg
    (add_nonneg (xiRectangularWeilTailNegativePart_nonneg L N n) (norm_nonneg _))
    (norm_nonneg _)

private theorem xiRectangularRightNegativePart_le_observableMajorant
    (L : ℝ) (N n : ℕ) :
    xiRectangularRightNegativePart L n ≤
      xiRectangularObservableNegativePartMajorant L N n := by
  have heq :=
    xiRectangularWeilTailCoefficient_eq_carrier_sub_prefix_add_remainder L N n
  have hreEq := congrArg Complex.re heq
  simp only [Complex.add_re, Complex.sub_re] at hreEq
  change (xiRectangularWeilTailCoefficient L N n).re =
    xiRectangularRightDirichletCoefficientReal L n -
      (xiRectangularLandauPrefixCoefficient L 0 N n).re +
        (xiRectangularWeilRemainderCoefficient L N n).re at hreEq
  have hdist :
      |xiRectangularRightDirichletCoefficientReal L n -
          (xiRectangularWeilTailCoefficient L N n).re| ≤
        ‖xiRectangularLandauPrefixCoefficient L 0 N n‖ +
          ‖xiRectangularWeilRemainderCoefficient L N n‖ := by
    calc
      |xiRectangularRightDirichletCoefficientReal L n -
          (xiRectangularWeilTailCoefficient L N n).re| =
          |(xiRectangularLandauPrefixCoefficient L 0 N n).re -
            (xiRectangularWeilRemainderCoefficient L N n).re| := by
              congr 1
              linarith
      _ ≤ |(xiRectangularLandauPrefixCoefficient L 0 N n).re| +
          |(xiRectangularWeilRemainderCoefficient L N n).re| :=
        abs_sub _ _
      _ ≤ ‖xiRectangularLandauPrefixCoefficient L 0 N n‖ +
          ‖xiRectangularWeilRemainderCoefficient L N n‖ :=
        add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _)
  simpa only [xiRectangularRightNegativePart,
    xiRectangularObservableNegativePartMajorant,
    xiRectangularWeilTailNegativePart, add_assoc] using
      negPart_le_negPart_add_of_abs_sub_le _ _ _ hdist

private theorem xiRectangularLandauPrefixNorm_LSeriesSummable
    (L : ℝ) (N : ℕ) (s : ℂ) :
    LSeriesSummable
      (fun n => ((‖xiRectangularLandauPrefixCoefficient L 0 N n‖ : ℝ) : ℂ)) s := by
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro n hn
  have hNn : N ≤ n := by
    simpa only [Finset.mem_range, not_lt] using hn
  rcases n.eq_zero_or_pos with rfl | hnpos
  · exact LSeries.term_zero _ _
  · rw [LSeries.term_of_ne_zero hnpos.ne',
      xiRectangularLandauPrefixCoefficient, if_neg (not_lt.mpr hNn),
      norm_zero, ofReal_zero, zero_div]

private theorem xiRectangularWeilRemainderNorm_LSeriesSummable
    {L : ℝ} {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable
      (fun n => ((‖xiRectangularWeilRemainderCoefficient L N n‖ : ℝ) : ℂ)) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re
    (m := rectangularTwoEdgeRemainderBound L *
      ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) _ hs
  intro n hn
  rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact norm_xiRectangularWeilRemainderCoefficient_le hN n

private theorem xiRectangularObservableNegativePartMajorant_LSeriesSummable
    {L : ℝ} {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (henergy : XiRectangularWeilTailNegativePartEnergy L N)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    LSeriesSummable
      (fun n => ((xiRectangularObservableNegativePartMajorant L N n : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ)) := by
  have hobs := henergy epsilon hepsilon
  have hprefix := xiRectangularLandauPrefixNorm_LSeriesSummable
    L N (((1 + epsilon : ℝ) : ℂ))
  have hrem := xiRectangularWeilRemainderNorm_LSeriesSummable hN
    (s := (((1 + epsilon : ℝ) : ℂ))) (by simp only [ofReal_re]; linarith)
  have hadd := (hobs.add hprefix).add hrem
  change Summable (LSeries.term
    (fun n => ((xiRectangularObservableNegativePartMajorant L N n : ℝ) : ℂ))
    (((1 + epsilon : ℝ) : ℂ)))
  change Summable (LSeries.term _ (((1 + epsilon : ℝ) : ℂ))) at hadd
  apply hadd.congr
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [LSeries.term_zero]
  · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
    simp only [Pi.add_apply, xiRectangularObservableNegativePartMajorant,
      ofReal_add]

/-- The finite prefix and bounded observable remainder transport negative-part summability at
one specified real abscissa.  This is the quantitative form of the all-abscissa energy bridge. -/
theorem xiRectangularRightNegativePart_LSeriesSummable_at_one_add_of_tailNegativePart_summable
    {L : ℝ} {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    {alpha : ℝ} (halpha : 0 < alpha)
    (htail : LSeriesSummable
      (fun n => ((xiRectangularWeilTailNegativePart L N n : ℝ) : ℂ))
      (((1 + alpha : ℝ) : ℂ))) :
    LSeriesSummable
      (fun n => ((xiRectangularRightNegativePart L n : ℝ) : ℂ))
      (((1 + alpha : ℝ) : ℂ)) := by
  have hprefix := xiRectangularLandauPrefixNorm_LSeriesSummable
    L N (((1 + alpha : ℝ) : ℂ))
  have hrem := xiRectangularWeilRemainderNorm_LSeriesSummable hN
    (s := (((1 + alpha : ℝ) : ℂ))) (by simp only [ofReal_re]; linarith)
  have hadd := (htail.add hprefix).add hrem
  have hmajorant : LSeriesSummable
      (fun n => ((xiRectangularObservableNegativePartMajorant L N n : ℝ) : ℂ))
      (((1 + alpha : ℝ) : ℂ)) := by
    change Summable (LSeries.term
      (fun n => ((xiRectangularObservableNegativePartMajorant L N n : ℝ) : ℂ))
      (((1 + alpha : ℝ) : ℂ)))
    change Summable (LSeries.term _ (((1 + alpha : ℝ) : ℂ))) at hadd
    exact hadd.congr fun n => by
      rcases n.eq_zero_or_pos with rfl | hn
      · simp only [LSeries.term_zero]
      · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
        rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
        simp only [Pi.add_apply, xiRectangularObservableNegativePartMajorant,
          ofReal_add]
  exact LSeriesSummable_of_nonneg_of_le
    (xiRectangularRightNegativePart_nonneg L)
    (xiRectangularObservableNegativePartMajorant_nonneg L N)
    (xiRectangularRightNegativePart_le_observableMajorant L N)
    hmajorant

/-- The bounded observable remainder and finite deleted prefix transport negative Dirichlet energy
from the actual rectangular Weil values to the positive-transverse divisor carrier. -/
theorem xiRectangularRightNegativePartEnergy_of_xiRectangularWeilTailNegativePartEnergy
    {L : ℝ} {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (henergy : XiRectangularWeilTailNegativePartEnergy L N) :
    XiRectangularRightNegativePartEnergy L := by
  intro epsilon hepsilon
  exact LSeriesSummable_of_nonneg_of_le
    (xiRectangularRightNegativePart_nonneg L)
    (xiRectangularObservableNegativePartMajorant_nonneg L N)
    (xiRectangularRightNegativePart_le_observableMajorant L N)
    (xiRectangularObservableNegativePartMajorant_LSeriesSummable
      hN henergy hepsilon)

/-- Summable negative Dirichlet energy of one actual rectangular Weil family proves RH. -/
theorem riemannHypothesis_of_xiRectangularWeilTailNegativePartEnergy
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (henergy : XiRectangularWeilTailNegativePartEnergy L N) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_xiRectangularRightNegativePartEnergy hL
    (xiRectangularRightNegativePartEnergy_of_xiRectangularWeilTailNegativePartEnergy
      hN henergy)

end

end RHTower
