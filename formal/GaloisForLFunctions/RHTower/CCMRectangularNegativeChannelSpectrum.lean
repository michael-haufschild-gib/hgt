import GaloisForLFunctions.RHTower.CCMRectangularNegativeChannelSplitCompleteness
import GaloisForLFunctions.RHTower.CCMRectangularOneSidedTransverseExponent

/-!
# The full horizontal spectrum of every positive rectangular negative-mass split

The RH endpoint of the positive-channel theorem is the zero member of a complete quantitative
spectrum.  Fix `alpha >= 0` and an exact nonnegative split

`q^-(n) = a(n) + b(n)`.

Then the supremal transverse displacement of the Xi divisor is at most `alpha` if and only if

* `a` has finite Dirichlet energy at every abscissa `1 + alpha + epsilon`, and
* `b` has a pointwise envelope of order `n^(alpha + delta)` for every `delta > 0`.

The proof first factors the rectangular negative-energy Landau argument at one abscissa.  This
turns convergence at `1 + alpha` into the zero-free region `Re rho <= 1/2 + alpha`.  The channel
spectrum then follows without any global amplitude hypothesis.  At `alpha = 0` it specializes
exactly to the RH positive-channel completeness theorem.
-/

open Complex Filter Function Set LSeries

namespace RHTower

noncomputable section

set_option maxHeartbeats 1000000

/-! ## One-abscissa rectangular negative-energy transfer -/

/-- Convergence of the positive-transverse negative rectangular carrier at the one abscissa
`1 + alpha` bounds every positive-transverse Xi zero by `alpha`. -/
theorem xiRightCenteredZero_re_le_of_xiRectangularRightNegativePart_summable
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 ≤ alpha)
    (hcorr : LSeriesSummable
      (fun n => ((xiRectangularRightNegativePart L n : ℝ) : ℂ))
      (((1 + alpha : ℝ) : ℂ)))
    (q : XiRightZeroCopy) :
    (xiRightCenteredZero q).re ≤ alpha := by
  by_contra hnot
  have hqalpha : alpha < (xiRightCenteredZero q).re := lt_of_not_ge hnot
  have hne : Nonempty XiRightZeroCopy := ⟨q⟩
  have halphaSup : alpha < xiRightTransverseSup :=
    hqalpha.trans_le (xiRightCenteredZero_re_le_sup q)
  obtain ⟨sigma, hsigmaAlpha, hsigmaDelta, hsumCorrected⟩ :=
    exists_xiRectangularNegativePartLandauCoefficient_summable_left_of_boundary_of_one_abscissa
      L alpha hne halphaSup hcorr
  have hcorrSigma : LSeriesSummable
      (fun n => ((xiRectangularRightNegativePart L n : ℝ) : ℂ))
      (sigma : ℂ) :=
    hcorr.of_re_le_re (by simpa only [ofReal_re] using hsigmaAlpha.le)
  have hdiff := hsumCorrected.sub hcorrSigma
  have horiginal : LSeriesSummable
      (fun n => ((xiRectangularLandauCoefficient L 0 0 n : ℝ) : ℂ))
      (sigma : ℂ) := by
    change Summable (LSeries.term
      (fun n => ((xiRectangularLandauCoefficient L 0 0 n : ℝ) : ℂ))
      (sigma : ℂ))
    change Summable (LSeries.term _ (sigma : ℂ)) at hdiff
    exact hdiff.congr fun n => by
      rcases n.eq_zero_or_pos with rfl | hn
      · simp only [LSeries.term_zero]
      · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
        rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
        simp only [Pi.sub_apply, xiRectangularNegativePartLandauCoefficient,
          xiRectangularLandauCoefficient, if_pos (Nat.zero_le n)]
        push_cast
        ring
  have hsigma : 1 < sigma := by linarith
  have hpoleBound : ∀ r : XiRightZeroCopy,
      (xiRightShiftedPole r).re ≤ sigma :=
    xiRightShiftedPole_re_le_of_landau_summable hL 0 0 hsigma
      (xiRightTransverseSup_pos hne).le
      (fun r => xiRightCenteredZero_re_le_sup r) horiginal
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

/-- One-abscissa negative energy of the actual fixed-window observable gives the corresponding
horizontal bound for every positive-transverse Xi zero. -/
theorem xiRightCenteredZero_re_le_of_xiRectangularWeilTailNegativePart_summable
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 < alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (htail : LSeriesSummable
      (fun n => ((xiRectangularWeilTailNegativePart L N n : ℝ) : ℂ))
      (((1 + alpha : ℝ) : ℂ)))
    (q : XiRightZeroCopy) :
    (xiRightCenteredZero q).re ≤ alpha := by
  apply xiRightCenteredZero_re_le_of_xiRectangularRightNegativePart_summable
    hL halpha.le
  exact
    xiRectangularRightNegativePart_LSeriesSummable_at_one_add_of_tailNegativePart_summable
      hN halpha htail

/-- The one-abscissa observable energy bound controls every multiplicity copy of the Xi divisor,
including copies on or to the left of the critical line. -/
theorem re_I_mul_xiSpectralPoint_le_of_xiRectangularWeilTailNegativePart_summable
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 < alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (htail : LSeriesSummable
      (fun n => ((xiRectangularWeilTailNegativePart L N n : ℝ) : ℂ))
      (((1 + alpha : ℝ) : ℂ)))
    (q : XiZeroCopy) :
    (I * xiSpectralPoint q).re ≤ alpha := by
  by_cases hright : 0 < (I * xiSpectralPoint q).re
  · let qr : XiRightZeroCopy := ⟨q, hright⟩
    simpa only [xiRightCenteredZero] using
      xiRightCenteredZero_re_le_of_xiRectangularWeilTailNegativePart_summable
        hL halpha hN htail qr
  · exact (le_of_not_gt hright).trans halpha.le

/-- **One-abscissa observable zero-free region.**  Convergence of the actual negative
fixed-window energy at `1 + alpha` forces every Xi zero into
`Re rho <= 1/2 + alpha`. -/
theorem xi_zero_re_le_half_add_of_xiRectangularWeilTailNegativePart_summable
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 < alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (htail : LSeriesSummable
      (fun n => ((xiRectangularWeilTailNegativePart L N n : ℝ) : ℂ))
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
    re_I_mul_xiSpectralPoint_le_of_xiRectangularWeilTailNegativePart_summable
      hL halpha hN htail q
  have hcoord : I * xiSpectralPoint q = rho - 1 / 2 := by
    simpa only [q, support] using I_mul_xiSpectralPoint q
  rw [hcoord] at hq
  norm_num [Complex.sub_re] at hq ⊢
  linarith

/-! ## The exact positive-channel transverse spectrum -/

/-- Dirichlet energy of a positive carrier channel above the transverse exponent `alpha`. -/
def XiRectangularNegativeChannelEnergyAbove
    (alpha : ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    LSeriesSummable (fun n => ((a n : ℝ) : ℂ))
      (((1 + alpha + epsilon : ℝ) : ℂ))

/-- A residual positive channel has transverse order at most `alpha` when it has an
`n^(alpha + delta)` envelope for every positive `delta`. -/
def XiRectangularSubpowerChannelAbove
    (alpha : ℝ) (b : ℕ → ℝ) : Prop :=
  ∀ delta : ℝ, 0 < delta →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      b n ≤ C * powerCorrectionCoefficient (alpha + delta) n

private theorem xiRectangularWeilTailNegativePart_powerEnvelope_of_transverseSup_le
    {L alpha : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (hsup : xiRightTransverseSup ≤ alpha) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      xiRectangularWeilTailNegativePart L N n ≤
        C * powerCorrectionCoefficient alpha n := by
  by_cases hne : Nonempty XiRightZeroCopy
  · let K : ℝ :=
      2 * xiRectangularRightCoefficientNormSum L +
        rectangularTwoEdgeRemainderBound L *
          ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
    have hK : 0 ≤ K := by
      dsimp only [K]
      exact add_nonneg
        (mul_nonneg (by norm_num)
          (tsum_nonneg fun q : XiRightZeroCopy => norm_nonneg _))
        (mul_nonneg
          (by unfold rectangularTwoEdgeRemainderBound; positivity)
          (tsum_nonneg fun q : XiZeroCopy => by positivity))
    refine ⟨K, hK, fun n => ?_⟩
    by_cases hnN : N ≤ n
    · obtain ⟨hn1, hLa⟩ := hN n hnN
      have hn0 : n ≠ 0 := by omega
      have hnorm :=
        norm_xiWeilPolarization_rectangular_logSample_le_transverse_power
          hne hn1 hLa
      have hbase : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hpow : (n : ℝ) ^ xiRightTransverseSup ≤ (n : ℝ) ^ alpha :=
        Real.rpow_le_rpow_of_exponent_le hbase hsup
      have hnegativeNorm :
          ((xiRectangularWeilLogCoefficient L n).re)⁻ ≤
            ‖xiRectangularWeilLogCoefficient L n‖ := by
        change max (-(xiRectangularWeilLogCoefficient L n).re) 0 ≤
          ‖xiRectangularWeilLogCoefficient L n‖
        exact max_le
          ((neg_le_abs _).trans (Complex.abs_re_le_norm _))
          (norm_nonneg _)
      rw [xiRectangularWeilTailNegativePart,
        xiRectangularWeilTailCoefficient, if_pos hnN,
        powerCorrectionCoefficient, if_neg hn0]
      exact hnegativeNorm.trans
        (hnorm.trans (mul_le_mul_of_nonneg_left hpow hK))
    · rw [xiRectangularWeilTailNegativePart,
        xiRectangularWeilTailCoefficient, if_neg hnN, Complex.zero_re,
        negPart_zero]
      exact mul_nonneg hK (powerCorrectionCoefficient_nonneg _ _)
  · have hRH : RiemannHypothesis := by
      by_contra hnot
      exact hne (nonempty_xiRightZeroCopy_of_not_riemannHypothesis hnot)
    refine ⟨0, le_rfl, fun n => ?_⟩
    rw [xiRectangularWeilTailNegativePart_eq_zero_of_riemannHypothesis
      hL hRH, zero_mul]

private theorem channel_le_negativePart
    {L : ℝ} {N : ℕ} {a b : ℕ → ℝ}
    (hsplit : XiRectangularNegativeChannelSplit L N a b) :
    (∀ n, a n ≤ xiRectangularWeilTailNegativePart L N n) ∧
      (∀ n, b n ≤ xiRectangularWeilTailNegativePart L N n) := by
  constructor
  · intro n
    have hs := hsplit n
    linarith
  · intro n
    have hs := hsplit n
    linarith

private theorem powerCorrectionCoefficient_mono_exponent
    {alpha beta : ℝ} (hab : alpha ≤ beta) (n : ℕ) :
    powerCorrectionCoefficient alpha n ≤
      powerCorrectionCoefficient beta n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · norm_num [powerCorrectionCoefficient]
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [powerCorrectionCoefficient, if_neg (Nat.ne_of_gt hn),
      powerCorrectionCoefficient, if_neg (Nat.ne_of_gt hn)]
    exact Real.rpow_le_rpow_of_exponent_le hn1 hab

private theorem channelEnergyAbove_of_powerEnvelope
    {alpha C : ℝ} (hC : 0 ≤ C) {a : ℕ → ℝ}
    (ha0 : ∀ n, 0 ≤ a n)
    (ha : ∀ n, a n ≤ C * powerCorrectionCoefficient alpha n) :
    XiRectangularNegativeChannelEnergyAbove alpha a := by
  intro epsilon hepsilon
  have hpower := powerCorrectionCoefficient_LSeriesSummable
    (alpha := alpha) (s := (((1 + alpha + epsilon : ℝ) : ℂ))) (by
      simp only [ofReal_re]
      linarith)
  have hscaled := hpower.smul (C : ℂ)
  have hmajorant : LSeriesSummable
      (fun n => ((C * powerCorrectionCoefficient alpha n : ℝ) : ℂ))
      (((1 + alpha + epsilon : ℝ) : ℂ)) := by
    change Summable (LSeries.term
      (fun n => ((C * powerCorrectionCoefficient alpha n : ℝ) : ℂ))
      (((1 + alpha + epsilon : ℝ) : ℂ)))
    change Summable (LSeries.term _ (((1 + alpha + epsilon : ℝ) : ℂ)))
      at hscaled
    exact hscaled.congr fun n => by
      rcases n.eq_zero_or_pos with rfl | hn
      · simp only [LSeries.term_zero]
      · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
        rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
        simp only [Pi.smul_apply, smul_eq_mul, ofReal_mul]
  exact LSeriesSummable_of_nonneg_of_le ha0
    (fun n => mul_nonneg hC (powerCorrectionCoefficient_nonneg alpha n))
    ha hmajorant

/-- **Exact positive-channel transverse spectrum.**  Every nonnegative allocation of the actual
negative rectangular mass carries the complete horizontal Xi-divisor exponent. -/
theorem xiRightTransverseSup_le_iff_negativeChannelSpectrum
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    {a b : ℕ → ℝ}
    (hsplit : XiRectangularNegativeChannelSplit L N a b) :
    xiRightTransverseSup ≤ alpha ↔
      XiRectangularNegativeChannelEnergyAbove alpha a ∧
        XiRectangularSubpowerChannelAbove alpha b := by
  constructor
  · intro hsup
    obtain ⟨C, hC, hq⟩ :=
      xiRectangularWeilTailNegativePart_powerEnvelope_of_transverseSup_le
        hL hN hsup
    obtain ⟨haq, hbq⟩ := channel_le_negativePart hsplit
    constructor
    · exact channelEnergyAbove_of_powerEnvelope hC
        (fun n => (hsplit n).1) (fun n => (haq n).trans (hq n))
    · intro delta hdelta
      refine ⟨C, hC, fun n => ?_⟩
      have hmono := powerCorrectionCoefficient_mono_exponent
        (alpha := alpha) (beta := alpha + delta) (by linarith) n
      exact (hbq n).trans ((hq n).trans
        (mul_le_mul_of_nonneg_left hmono hC))
  · rintro ⟨haEnergy, hbGrowth⟩
    have hright : ∀ q : XiRightZeroCopy,
        (xiRightCenteredZero q).re ≤ alpha := by
      intro q
      by_contra hnot
      have hqalpha : alpha < (xiRightCenteredZero q).re := lt_of_not_ge hnot
      let epsilon : ℝ := ((xiRightCenteredZero q).re - alpha) / 2
      have hepsilon : 0 < epsilon := by
        dsimp only [epsilon]
        linarith
      let delta : ℝ := epsilon / 2
      have hdelta : 0 < delta := by dsimp only [delta]; positivity
      obtain ⟨C, hC, hb⟩ := hbGrowth delta hdelta
      have hpower := powerCorrectionCoefficient_LSeriesSummable
        (alpha := alpha + delta)
        (s := (((1 + (alpha + epsilon) : ℝ) : ℂ))) (by
          simp only [ofReal_re]
          dsimp only [delta]
          linarith)
      have hscaled := hpower.smul (C : ℂ)
      have hmajorant : LSeriesSummable
          (fun n => ((a n + C * powerCorrectionCoefficient (alpha + delta) n : ℝ) : ℂ))
          (((1 + (alpha + epsilon) : ℝ) : ℂ)) := by
        have haSum : LSeriesSummable (fun n => ((a n : ℝ) : ℂ))
            (((1 + (alpha + epsilon) : ℝ) : ℂ)) := by
          simpa only [add_assoc] using haEnergy epsilon hepsilon
        have hadd := haSum.add hscaled
        change Summable (LSeries.term
          (fun n => ((a n + C * powerCorrectionCoefficient (alpha + delta) n : ℝ) : ℂ))
          (((1 + (alpha + epsilon) : ℝ) : ℂ)))
        change Summable (LSeries.term _ (((1 + (alpha + epsilon) : ℝ) : ℂ)))
          at hadd
        exact hadd.congr fun n => by
          rcases n.eq_zero_or_pos with rfl | hn
          · simp only [LSeries.term_zero]
          · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
            rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
              ofReal_add, ofReal_mul]
      have htail : LSeriesSummable
          (fun n => ((xiRectangularWeilTailNegativePart L N n : ℝ) : ℂ))
          (((1 + (alpha + epsilon) : ℝ) : ℂ)) := by
        apply LSeriesSummable_of_nonneg_of_le
          (xiRectangularWeilTailNegativePart_nonneg L N)
          (fun n => add_nonneg (hsplit n).1
            (mul_nonneg hC (powerCorrectionCoefficient_nonneg _ _)))
          (fun n => by
            rw [(hsplit n).2.2]
            exact add_le_add_right (hb n) (a n))
          hmajorant
      have hbound :=
        xiRightCenteredZero_re_le_of_xiRectangularWeilTailNegativePart_summable
          hL (by linarith [halpha]) hN htail q
      dsimp only [epsilon] at hbound
      linarith
    by_cases hne : Nonempty XiRightZeroCopy
    · apply csSup_le (Set.range_nonempty _)
      intro x hx
      obtain ⟨q, rfl⟩ := hx
      exact hright q
    · letI : IsEmpty XiRightZeroCopy := ⟨fun q => hne ⟨q⟩⟩
      rw [xiRightTransverseSup, xiRightTransverseSet]
      have hrange : Set.range (fun q : XiRightZeroCopy =>
          (xiRightCenteredZero q).re) = ∅ := Set.range_eq_empty_iff.mpr inferInstance
      rw [hrange, Real.sSup_empty]
      exact halpha

/-- Zero-free-half-plane form of the positive-channel spectrum. -/
theorem all_xiZeros_re_le_iff_negativeChannelSpectrum
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    {a b : ℕ → ℝ}
    (hsplit : XiRectangularNegativeChannelSplit L N a b) :
    (∀ rho : ℂ, xi rho = 0 → rho.re ≤ 1 / 2 + alpha) ↔
      XiRectangularNegativeChannelEnergyAbove alpha a ∧
        XiRectangularSubpowerChannelAbove alpha b := by
  have hzeroSup :
      (∀ rho : ℂ, xi rho = 0 → rho.re ≤ 1 / 2 + alpha) ↔
        xiRightTransverseSup ≤ alpha := by
    constructor
    · intro hzeros
      exact (xiRectangularWeilTailPowerLower_iff_transverseSup_le_global
        hL halpha).1
          ((xiRectangularWeilTailPowerLower_iff_all_xiZeros_re_le
            hL halpha).2 hzeros)
    · intro hsup
      exact (xiRectangularWeilTailPowerLower_iff_all_xiZeros_re_le
        hL halpha).1
          ((xiRectangularWeilTailPowerLower_iff_transverseSup_le_global
            hL halpha).2 hsup)
  exact hzeroSup.trans
    (xiRightTransverseSup_le_iff_negativeChannelSpectrum
      hL halpha hN hsplit)

/-- At transverse exponent zero, the spectrum theorem is exactly the RH positive-channel
completeness theorem. -/
theorem riemannHypothesis_iff_negativeChannelSpectrum_zero
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    {a b : ℕ → ℝ}
    (hsplit : XiRectangularNegativeChannelSplit L N a b) :
    RiemannHypothesis ↔
      XiRectangularNegativeChannelEnergyAbove 0 a ∧
        XiRectangularSubpowerChannelAbove 0 b := by
  simpa only [XiRectangularNegativeChannelEnergyAbove,
    XiRectangularSubpowerChannelAbove, zero_add, add_zero] using
      riemannHypothesis_iff_negativeChannelEnergy_and_subpowerChannel
        hL hN hsplit

end

end RHTower
