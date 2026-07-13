import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowExcessEnergyGate

/-!
# The positive-excess energy abscissa bounds every transverse Xi zero

The all-epsilon positive-excess criterion can be made quantitative.  Absolute convergence of
the negative sharp-source correction at one real abscissa `1 + alpha` already places every
positive-transverse Xi zero in the half-plane with centered real part at most `alpha`.

For the dyadic weighted prime window this says that convergence of

`sum E(n) / n^(1 + alpha)`

for `E(n) = (W(n) - 2 * (1 - 1 / sqrt 2) * sqrt n)^+` forces
`Re rho <= 1/2 + alpha`.  Thus the Dirichlet-energy abscissa of the positive overshoot is a
quantitative upper bound for the horizontal Xi divisor.
-/

open Complex Filter Function Set LSeries

noncomputable section

namespace RHTower

/-- One-abscissa Landau transfer for the negative-part-corrected sharp source.  The correction
need only converge at `1 + beta`, provided that abscissa lies strictly left of the hypothetical
rightmost transverse Xi boundary. -/
theorem exists_dyadicSharpNegativePartLandauCoefficient_summable_left_of_boundary_of_one_abscissa
    (beta : ℝ) (hne : Nonempty XiRightZeroCopy)
    (hbetaDelta : beta < xiRightTransverseSup)
    (hcorrBase : LSeriesSummable
      (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ))
      (((1 + beta : ℝ) : ℂ))) :
    ∃ sigma : ℝ,
      1 + beta < sigma ∧
      sigma < 1 + xiRightTransverseSup ∧
      LSeriesSummable
        (fun n => ((dyadicSharpNegativePartLandauCoefficient n : ℝ) : ℂ))
        (sigma : ℂ) := by
  let delta : ℝ := xiRightTransverseSup
  have hdelta : 0 < delta := xiRightTransverseSup_pos hne
  have hdeltahalf : delta ≤ 1 / 2 := xiRightTransverseSup_le_half hne
  have hupper : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ delta :=
    fun q => xiRightCenteredZero_re_le_sup q
  obtain ⟨eta, heta, hordinate⟩ := exists_xiDivisorSupport_abs_im_lower_bound
  let r : ℝ := min (min (1 / 8) (eta / 4)) ((delta - beta) / 4)
  have hr : 0 < r := by
    dsimp only [r]
    exact lt_min
      (lt_min (by norm_num) (div_pos heta (by norm_num)))
      (div_pos (sub_pos.mpr (by simpa only [delta] using hbetaDelta)) (by norm_num))
  have hrquarter : r ≤ 1 / 4 :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (by norm_num))
  have hreta : r ≤ eta / 2 :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (by linarith))
  have hrgap : r ≤ (delta - beta) / 4 := min_le_right _ _
  have hbetaGap : beta + r < delta := by
    have hgap : 0 < delta - beta := by
      simpa only [delta] using sub_pos.mpr hbetaDelta
    linarith
  let sigmaFar : ℝ := 2
  have hcorrFar : LSeriesSummable
      (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ))
      (sigmaFar : ℂ) :=
    hcorrBase.of_re_le_re (by
      simp only [ofReal_re]
      dsimp only [sigmaFar]
      linarith)
  have hsumFar : LSeriesSummable
      (fun n => ((dyadicSharpNegativePartLandauCoefficient n : ℝ) : ℂ))
      (sigmaFar : ℂ) := by
    apply dyadicSharpNegativePartLandauCoefficient_LSeriesSummable
    · norm_num [sigmaFar]
    · exact hcorrFar
  let Rfar : NNReal :=
    ⟨2 - delta - r / 16, by
      linarith [hdeltahalf, hrquarter]⟩
  have hGfar : DifferentiableOn ℂ
      dyadicSharpNegativePartLandauContinuation
      (Metric.closedBall (((sigmaFar + 1 : ℝ) : ℂ)) (Rfar : ℝ)) := by
    apply (differentiableOn_dyadicSharpNegativePartLandauContinuation_rightOf
      beta delta hdelta.le hdelta
        (by simpa only [delta] using hbetaDelta) hupper hcorrBase).mono
    intro s hs
    rw [Metric.mem_closedBall, dist_eq_norm] at hs
    change 1 + delta < s.re
    have habs := Complex.abs_re_le_norm
      (s - (((sigmaFar + 1 : ℝ) : ℂ)))
    rw [Complex.sub_re, ofReal_re] at habs
    have hlower : -(Rfar : ℝ) ≤ s.re - (sigmaFar + 1) := by
      have := le_trans habs hs
      rw [abs_le] at this
      exact this.1
    change -(2 - delta - r / 16) ≤ s.re - (sigmaFar + 1) at hlower
    dsimp only [sigmaFar] at hlower
    linarith
  have hagreeFar : ∀ s : ℂ, sigmaFar < s.re →
      dyadicSharpNegativePartLandauContinuation s =
        LSeries
          (fun n => ((dyadicSharpNegativePartLandauCoefficient n : ℝ) : ℂ)) s := by
    intro s hs
    have hcorrS : LSeriesSummable
        (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ)) s :=
      hcorrBase.of_re_le_re (by
        simp only [ofReal_re]
        dsimp only [sigmaFar] at hs
        linarith)
    symm
    apply LSeries_dyadicSharpNegativePartLandauCoefficient_eq_continuation
    · dsimp only [sigmaFar] at hs
      linarith
    · exact hcorrS
  let sigmaNear : ℝ := 1 + delta + r / 8
  have hsumNear : LSeriesSummable
      (fun n => ((dyadicSharpNegativePartLandauCoefficient n : ℝ) : ℂ))
      (sigmaNear : ℂ) := by
    apply landau_local_summability_transfer
      dyadicSharpNegativePartLandauCoefficient_nonneg
      (h := 1) (by norm_num) hsumFar (R := Rfar)
      (G := dyadicSharpNegativePartLandauContinuation)
      hGfar hagreeFar
    change sigmaFar + 1 - (2 - delta - r / 16) < sigmaNear
    dsimp only [sigmaFar, sigmaNear]
    linarith
  have hsigmaNear : 1 + delta < sigmaNear := by
    dsimp only [sigmaNear]
    linarith
  have heqNear := dyadicSharpNegativePartLandauContinuation_eq_LSeries_rightOf
    beta delta hdelta.le hdelta (by simpa only [delta] using hbetaDelta)
      hupper hcorrBase hsigmaNear hsumNear
  have hcont :=
    differentiableOn_dyadicSharpNegativePartLandauContinuation_landauBall
      beta hdelta.le hr hrquarter hreta hbetaGap hordinate hcorrBase
  let h : ℝ := r / 8
  let R : NNReal := ⟨r / 2, div_nonneg hr.le (by norm_num)⟩
  have hh : 0 < h := by dsimp only [h]; positivity
  have hGlocal : DifferentiableOn ℂ
      dyadicSharpNegativePartLandauContinuation
      (Metric.closedBall (((sigmaNear + h : ℝ) : ℂ)) (R : ℝ)) := by
    apply hcont.mono
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm]
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hcenter :
        ‖(((sigmaNear + h : ℝ) : ℂ) - (((1 + delta : ℝ) : ℂ)))‖ =
          r / 4 := by
      have heq :
          (((sigmaNear + h : ℝ) : ℂ) - (((1 + delta : ℝ) : ℂ))) =
            ((r / 4 : ℝ) : ℂ) := by
        dsimp only [sigmaNear, h]
        push_cast
        ring
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
      positivity
    calc
      ‖z - (((1 + delta : ℝ) : ℂ))‖ ≤
          ‖z - (((sigmaNear + h : ℝ) : ℂ))‖ +
            ‖(((sigmaNear + h : ℝ) : ℂ) - (((1 + delta : ℝ) : ℂ)))‖ := by
        have := norm_add_le
          (z - (((sigmaNear + h : ℝ) : ℂ)))
          ((((sigmaNear + h : ℝ) : ℂ)) - (((1 + delta : ℝ) : ℂ)))
        simpa only [sub_add_sub_cancel] using this
      _ ≤ r / 2 + r / 4 := by
        rw [hcenter]
        exact add_le_add hz le_rfl
      _ < r := by linarith
  let sigma : ℝ := 1 + delta - r / 8
  have hsum : LSeriesSummable
      (fun n => ((dyadicSharpNegativePartLandauCoefficient n : ℝ) : ℂ))
      (sigma : ℂ) := by
    apply landau_local_summability_transfer
      dyadicSharpNegativePartLandauCoefficient_nonneg hh hsumNear
      (R := R) (G := dyadicSharpNegativePartLandauContinuation)
      hGlocal
    · intro s hs
      exact heqNear hs
    · change sigmaNear + h - r / 2 < sigma
      dsimp only [sigmaNear, h, sigma]
      linarith
  refine ⟨sigma, ?_, ?_, hsum⟩
  · dsimp only [sigma]
    have hgap : 0 < delta - beta := sub_pos.mpr
      (by simpa only [delta] using hbetaDelta)
    linarith [hrgap]
  · dsimp only [sigma, delta]
    linarith

/-- **Fixed-abscissa energy zero-free law.**  If the negative part of the exact sharp source has
an absolutely convergent Dirichlet series at `1 + alpha`, then every positive-transverse Xi zero
has centered real part at most `alpha`. -/
theorem xiRightCenteredZero_re_le_of_dyadicSharpPrimeSourceNegativePart_summable
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hcorr : LSeriesSummable
      (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ))
      (((1 + alpha : ℝ) : ℂ)))
    (q : XiRightZeroCopy) :
    (xiRightCenteredZero q).re ≤ alpha := by
  by_contra hnot
  have hqalpha : alpha < (xiRightCenteredZero q).re := lt_of_not_ge hnot
  have hne : Nonempty XiRightZeroCopy := ⟨q⟩
  have halphaSup : alpha < xiRightTransverseSup :=
    hqalpha.trans_le (xiRightCenteredZero_re_le_sup q)
  obtain ⟨sigma, hsigmaAlpha, hsigmaDelta, hsumCorrected⟩ :=
    exists_dyadicSharpNegativePartLandauCoefficient_summable_left_of_boundary_of_one_abscissa
      alpha hne halphaSup hcorr
  have hcorrSigma : LSeriesSummable
      (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ))
      (sigma : ℂ) :=
    hcorr.of_re_le_re (by simpa only [ofReal_re] using hsigmaAlpha.le)
  have hdiff := hsumCorrected.sub hcorrSigma
  have hsource : LSeriesSummable
      (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ))
      (sigma : ℂ) := by
    change Summable (LSeries.term
      (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ))
      (sigma : ℂ))
    change Summable (LSeries.term _ (sigma : ℂ)) at hdiff
    exact hdiff.congr fun n => by
      rcases n.eq_zero_or_pos with rfl | hn
      · simp only [LSeries.term_zero]
      · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
        rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
        simp only [Pi.sub_apply, dyadicSharpNegativePartLandauCoefficient,
          ofReal_add]
        ring
  have hsigmaHalf : 1 / 2 < sigma := by linarith
  have hpoleBound : ∀ r : XiRightZeroCopy,
      (xiRightShiftedPole r).re ≤ sigma :=
    xiRightShiftedPole_re_le_of_dyadicSharpSource_summable
      hsigmaHalf hsource
  have hcenterBound : ∀ r : XiRightZeroCopy,
      (xiRightCenteredZero r).re ≤ sigma - 1 := by
    intro r
    have hr := hpoleBound r
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re] at hr
    linarith
  have hsupBound : xiRightTransverseSup ≤ sigma - 1 := by
    apply csSup_le (Set.range_nonempty _)
    intro x hx
    obtain ⟨r, rfl⟩ := hx
    exact hcenterBound r
  linarith

/-- Direct prime-window form of the fixed-abscissa energy spectrum.  Convergence of the positive
overshoot energy at `1 + alpha` gives the zero-free region `Re rho <= 1/2 + alpha`. -/
theorem xiRightCenteredZero_re_le_of_dyadicWeightedPrimeWindowPositiveExcess_summable
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (henergy : LSeriesSummable
      (fun n => ((dyadicWeightedPrimeWindowPositiveExcess n : ℝ) : ℂ))
      (((1 + alpha : ℝ) : ℂ)))
    (q : XiRightZeroCopy) :
    (xiRightCenteredZero q).re ≤ alpha := by
  have hscaled := henergy.smul (2 : ℂ)
  have hcorr : LSeriesSummable
      (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ))
      (((1 + alpha : ℝ) : ℂ)) := by
    change Summable (LSeries.term
      (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ))
      (((1 + alpha : ℝ) : ℂ)))
    change Summable (LSeries.term _ (((1 + alpha : ℝ) : ℂ))) at hscaled
    exact hscaled.congr fun n => by
      rcases n.eq_zero_or_pos with rfl | hn
      · simp only [LSeries.term_zero]
      · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
        rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
        simp only [Pi.smul_apply, smul_eq_mul,
          dyadicSharpPrimeSourceNegativePart_eq_two_mul_positiveExcess,
          ofReal_mul]
        norm_num
  exact xiRightCenteredZero_re_le_of_dyadicSharpPrimeSourceNegativePart_summable
    halpha hcorr q

/-- The same one-abscissa energy bound controls every multiplicity copy of the Xi divisor,
including copies on or to the left of the critical line. -/
theorem re_I_mul_xiSpectralPoint_le_of_dyadicWeightedPrimeWindowPositiveExcess_summable
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (henergy : LSeriesSummable
      (fun n => ((dyadicWeightedPrimeWindowPositiveExcess n : ℝ) : ℂ))
      (((1 + alpha : ℝ) : ℂ)))
    (q : XiZeroCopy) :
    (I * xiSpectralPoint q).re ≤ alpha := by
  by_cases hright : 0 < (I * xiSpectralPoint q).re
  · let qr : XiRightZeroCopy := ⟨q, hright⟩
    simpa only [xiRightCenteredZero] using
      xiRightCenteredZero_re_le_of_dyadicWeightedPrimeWindowPositiveExcess_summable
        halpha henergy qr
  · exact (le_of_not_gt hright).trans halpha

/-- **Prime-window energy zero-free region.**  Convergence of the positive overshoot energy at
the single abscissa `1 + alpha` forces every Xi zero into
`Re rho <= 1/2 + alpha`. -/
theorem xi_zero_re_le_half_add_of_dyadicWeightedPrimeWindowPositiveExcess_summable
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (henergy : LSeriesSummable
      (fun n => ((dyadicWeightedPrimeWindowPositiveExcess n : ℝ) : ℂ))
      (((1 + alpha : ℝ) : ℂ)))
    {rho : ℂ} (hzero : xi rho = 0) :
    rho.re ≤ 1 / 2 + alpha := by
  let support : XiDivisorSupport :=
    ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hpos := xi_divisor_pos_on_support support
  have hn : 0 < Int.toNat
      ((MeromorphicOn.divisor xi Set.univ) (support : ℂ)) := by
    omega
  let q : XiZeroCopy := ⟨support, ⟨0, hn⟩⟩
  have hq :=
    re_I_mul_xiSpectralPoint_le_of_dyadicWeightedPrimeWindowPositiveExcess_summable
      halpha henergy q
  have hcoord : I * xiSpectralPoint q = rho - 1 / 2 := by
    simpa only [q, support] using I_mul_xiSpectralPoint q
  rw [hcoord] at hq
  norm_num [Complex.sub_re] at hq ⊢
  linarith

/-- Equivalent open-half-plane form of the fixed-abscissa energy theorem. -/
theorem xi_ne_zero_of_half_add_alpha_lt_re_of_dyadicWeightedPrimeWindowPositiveExcess_summable
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (henergy : LSeriesSummable
      (fun n => ((dyadicWeightedPrimeWindowPositiveExcess n : ℝ) : ℂ))
      (((1 + alpha : ℝ) : ℂ)))
    {rho : ℂ} (hrho : 1 / 2 + alpha < rho.re) :
    xi rho ≠ 0 := by
  intro hzero
  exact (not_lt_of_ge
    (xi_zero_re_le_half_add_of_dyadicWeightedPrimeWindowPositiveExcess_summable
      halpha henergy hzero)) hrho

end RHTower
