import GaloisForLFunctions.RHTower.PrimeArchOffLineQuartetKMSMaster

/-!
# Exact off-line-quartet accretive band

The four FE--Schwarz copies of an off-line Xi zero consume four equal endpoint cross charges.
Keeping the exact completed curvature instead of replacing it immediately by `2 / 43` gives the
natural central-band condition

`C * ((R + 1 / 2)^2 + 1) < 4`.

On every such band the continued prime--Gamma response is unconditionally anti-Herglotz in the
upper half-strip.  The rational certificates already available for Euler's constant and
`log (4 * pi)` sharpen the clean discharged radius from `87 / 10` to `218 / 25`.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- The rational bounds used for `C < 2 / 43` in fact prove the sharper displayed fraction. -/
theorem xiEndpointCompletedCurvature_lt_ninetyThree_over_twoThousand :
    xiEndpointCompletedCurvature < 93 / 2000 := by
  rw [xiEndpointCompletedCurvature_eq_eulerMascheroni_log]
  nlinarith
    [eulerMascheroniConstant_lt_twoThousandEightHundredEightySeven_over_fiveThousand,
      twoThousandFiveHundredThirtyNine_over_thousand_lt_log_four_mul_pi]

/-- Exact endpoint condition under which every off-line quartet lies beyond the central response
band. -/
def XiOffLineQuartetAccretiveBand (R : ℝ) : Prop :=
  0 ≤ R ∧
    xiEndpointCompletedCurvature * ((R + 1 / 2) ^ 2 + 1) < 4

/-- Exact four-charge height law before replacing the completed endpoint curvature by a rational
upper bound. -/
theorem four_le_endpointCurvature_mul_one_add_im_sq_of_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    4 ≤ xiEndpointCompletedCurvature * ((q.1 : ℂ).im ^ 2 + 1) := by
  have hlower := endpoint_cross_term_re_ge_inv_one_add_im_sq q
  have horbit := four_mul_xiEndpointCrossCharge_le_curvature_of_offLine q hoff
  have hden : 0 < (q.1 : ℂ).im ^ 2 + 1 := by positivity
  have hcharge : 4 / ((q.1 : ℂ).im ^ 2 + 1) ≤
      4 * xiEndpointCrossCharge q := by
    calc
      4 / ((q.1 : ℂ).im ^ 2 + 1) =
          4 * (1 / ((q.1 : ℂ).im ^ 2 + 1)) := by ring
      _ ≤ 4 * xiEndpointCrossCharge q :=
        mul_le_mul_of_nonneg_left hlower (by norm_num)
  have hbudget : 4 / ((q.1 : ℂ).im ^ 2 + 1) ≤
      xiEndpointCompletedCurvature := hcharge.trans horbit
  rw [div_le_iff₀ hden] at hbudget
  simpa [mul_comm] using hbudget

/-- **Sharpened rational off-line height gap.**  The exact quartet budget together with the
available rational endpoint-curvature certificate forces every off-critical Xi zero above the
squared ordinate `7907 / 93`. -/
theorem xiZeroCopy_offLine_sevenThousandNineHundredSeven_over_ninetyThree_lt_im_sq
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    7907 / 93 < (q.1 : ℂ).im ^ 2 := by
  have hbudget :=
    four_le_endpointCurvature_mul_one_add_im_sq_of_offLine q hoff
  have hC := xiEndpointCompletedCurvature_lt_ninetyThree_over_twoThousand
  nlinarith [sq_nonneg (q.1 : ℂ).im]

/-- Upper-half centered Xi is zero-free on every exact quartet-admissible band.  On-line zeros
lie on the boundary `Im z = 0`; a zero in the open upper half would be off-line and would violate
the four-charge height law. -/
theorem XiC_ne_zero_of_upperHalf_exactOffLineQuartetBand
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (z : ℂ) (hzIm : 0 < z.im) (hzRe : |z.re| ≤ R) :
    XiC z ≠ 0 := by
  intro hzero
  have hxi : xi (1 / 2 + z * I) = 0 := by
    simpa only [XiC] using hzero
  let rho : XiDivisorSupport :=
    ⟨1 / 2 + z * I, mem_xi_divisor_support_of_eq_zero hxi⟩
  let q : XiZeroCopy := by
    have hpos := xi_divisor_pos_on_support rho
    have hn : 0 < Int.toNat
        ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by
      omega
    exact ⟨rho, ⟨0, hn⟩⟩
  have hoff : (q.1 : ℂ).re ≠ 1 / 2 := by
    dsimp only [q, rho]
    simp only [add_re, mul_re, I_re, mul_zero, I_im, mul_one,
      sub_eq_add_neg]
    norm_num at *
    linarith
  have hfour :=
    four_le_endpointCurvature_mul_one_add_im_sq_of_offLine q hoff
  have hCpos : 0 < xiEndpointCompletedCurvature :=
    xiEndpointCompletedCurvature_pos
  have hmul :
      xiEndpointCompletedCurvature * ((R + 1 / 2) ^ 2 + 1) <
        xiEndpointCompletedCurvature * ((q.1 : ℂ).im ^ 2 + 1) :=
    hband.2.trans_le hfour
  have hradius : (R + 1 / 2) ^ 2 < (q.1 : ℂ).im ^ 2 := by
    have := lt_of_mul_lt_mul_left hmul hCpos.le
    linarith
  have him : (q.1 : ℂ).im = z.re := by
    dsimp only [q, rho]
    simp [mul_im]
  rw [him] at hradius
  have hzSq : z.re ^ 2 ≤ R ^ 2 := by
    nlinarith [sq_abs z.re, abs_nonneg z.re]
  nlinarith [hband.1]

/-- Every line-conjugate resolvent pair has the anti-Herglotz sign on an exact
quartet-admissible band. -/
lemma xiRelativeResolventTerm_lineConj_pair_im_nonpos_exactOffLineQuartetBand
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (z : ℂ) (hzIm : 0 < z.im) (hzRe : |z.re| ≤ R)
    (q : XiZeroCopy) :
    (xiRelativeResolventTerm z q +
      xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)).im ≤ 0 := by
  let a : ℂ := xiSpectralPoint q
  have haimMem := xiSpectralPoint_im_mem_openHalf q
  have haimAbs : |a.im| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith [haimMem.1, haimMem.2]
  have hcore : 0 < (z.re - a.re) ^ 2 + z.im ^ 2 - a.im ^ 2 := by
    by_cases hon : a.im = 0
    · rw [hon]
      norm_num
      nlinarith [sq_nonneg (z.re - a.re), sq_pos_of_pos hzIm]
    · have hoff : (q.1 : ℂ).re ≠ 1 / 2 := by
        intro hhalf
        apply hon
        dsimp only [a]
        simp [xiSpectralPoint, mul_im, hhalf]
      have hfour :=
        four_le_endpointCurvature_mul_one_add_im_sq_of_offLine q hoff
      have hCpos : 0 < xiEndpointCompletedCurvature :=
        xiEndpointCompletedCurvature_pos
      have hmul :
          xiEndpointCompletedCurvature * ((R + 1 / 2) ^ 2 + 1) <
            xiEndpointCompletedCurvature * (a.re ^ 2 + 1) := by
        have hfourA :
            4 ≤ xiEndpointCompletedCurvature * (a.re ^ 2 + 1) := by
          simpa [a, xiSpectralPoint, mul_re] using hfour
        exact hband.2.trans_le hfourA
      have hareSq : (R + 1 / 2) ^ 2 < a.re ^ 2 := by
        have := lt_of_mul_lt_mul_left hmul hCpos.le
        linarith
      have hareAbs : R + 1 / 2 < |a.re| := by
        nlinarith [sq_abs a.re, abs_nonneg a.re, hband.1]
      have hdistLower : |a.re| - |z.re| ≤ |a.re - z.re| :=
        abs_sub_abs_le_abs_sub a.re z.re
      have hdistAbs : |a.im| < |z.re - a.re| := by
        rw [abs_sub_comm]
        linarith
      have hdistSq : a.im ^ 2 < (z.re - a.re) ^ 2 := by
        nlinarith [sq_abs a.im, sq_abs (z.re - a.re),
          abs_nonneg a.im, abs_nonneg (z.re - a.re)]
      nlinarith [sq_nonneg z.im]
  have hza : z ≠ a := by
    intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    nlinarith
  have hzac : z ≠ (starRingEnd ℂ) a := by
    intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp only [conj_re, conj_im] at hre him
    nlinarith
  have hdenOne :
      0 < (z.re - a.re) ^ 2 + (z.im - a.im) ^ 2 := by
    have h : z - a ≠ 0 := sub_ne_zero.mpr hza
    simpa only [Complex.normSq_apply, sub_re, sub_im, pow_two] using
      Complex.normSq_pos.mpr h
  have hdenTwo :
      0 < (z.re - a.re) ^ 2 + (z.im + a.im) ^ 2 := by
    have h : z - (starRingEnd ℂ) a ≠ 0 := sub_ne_zero.mpr hzac
    simpa only [Complex.normSq_apply, conj_re, conj_im, sub_re, sub_im,
      sub_neg_eq_add, pow_two] using Complex.normSq_pos.mpr h
  rw [xiRelativeResolventTerm, xiRelativeResolventTerm,
    xiSpectralPoint_lineConj]
  change ((a⁻¹ - (a - z)⁻¹) +
      (((starRingEnd ℂ) a)⁻¹ - ((starRingEnd ℂ) a - z)⁻¹)).im ≤ 0
  rw [relativeResolvent_conj_pair_im_formula z a
    (xiSpectralPoint_ne_zero q) hza (by simpa using hzac)]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by nlinarith [hzIm]) hcore.le)
    (mul_nonneg hdenOne.le hdenTwo.le)

/-- Full relative-resolvent trace sign on every exact quartet-admissible band. -/
theorem xiRelativeResolventTrace_im_nonpos_exactOffLineQuartetBand
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (z : ℂ) (hzIm : 0 < z.im) (hzRe : |z.re| ≤ R) :
    (xiRelativeResolventTrace z).im ≤ 0 := by
  have hXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_upperHalf_exactOffLineQuartetBand R hband z hzIm hzRe
  have hsum := summable_xiRelativeResolventTerm hXi
  have hsumJ : Summable (fun q : XiZeroCopy =>
      xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)) :=
    (xiZeroCopyLineConjEquiv.summable_iff).mpr hsum
  have hpair := hsum.add hsumJ
  have hreindex :
      (∑' q : XiZeroCopy,
        xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)) =
          xiRelativeResolventTrace z := by
    rw [xiRelativeResolventTrace]
    exact xiZeroCopyLineConjEquiv.tsum_eq (xiRelativeResolventTerm z)
  have hpairsum :
      (∑' q : XiZeroCopy,
        (xiRelativeResolventTerm z q +
          xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q))) =
        2 * xiRelativeResolventTrace z := by
    rw [hsum.tsum_add hsumJ, hreindex, xiRelativeResolventTrace]
    ring
  have himsum :
      (∑' q : XiZeroCopy,
        (xiRelativeResolventTerm z q +
          xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)).im) ≤ 0 :=
    tsum_nonpos fun q =>
      xiRelativeResolventTerm_lineConj_pair_im_nonpos_exactOffLineQuartetBand
        R hband z hzIm hzRe q
  have hpairsumIm := congrArg Complex.im hpairsum
  rw [Complex.im_tsum hpair] at hpairsumIm
  norm_num [mul_im] at hpairsumIm
  have himsum' :
      (∑' q : XiZeroCopy,
        ((xiRelativeResolventTerm z q).im +
          (xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)).im)) ≤ 0 := by
    simpa only [add_im] using himsum
  linarith

/-- Source-side form of the exact quartet central-band sign. -/
theorem continuedPrimeArchSourceRelativeTrace_im_nonpos_exactOffLineQuartetBand
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzRe : |z.re| ≤ R) :
    (continuedPrimeArchSourceRelativeTrace z).im ≤ 0 := by
  have hspos : 0 < (1 / 2 + z * I).re := by
    simp [mul_re]
    linarith
  have hs1 : 1 / 2 + z * I ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [mul_re] at hre
    linarith
  have hXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_upperHalf_exactOffLineQuartetBand R hband z hzIm hzRe
  have hzeta : riemannZeta (1 / 2 + z * I) ≠ 0 := by
    exact (xi_eq_zero_iff hspos hs1).not.mp (by simpa only [XiC] using hXi)
  rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    hspos hs1 hzeta]
  exact xiRelativeResolventTrace_im_nonpos_exactOffLineQuartetBand
    R hband z hzIm hzRe

/-- The rational radius `218 / 25` satisfies the exact quartet band inequality. -/
theorem xiOffLineQuartetAccretiveBand_twoHundredEighteen_twentyFifths :
    XiOffLineQuartetAccretiveBand (218 / 25) := by
  refine ⟨by norm_num, ?_⟩
  have hC := xiEndpointCompletedCurvature_lt_ninetyThree_over_twoThousand
  nlinarith

/-- Unconditional source anti-Herglotz sign on the sharpened rational central band. -/
theorem continuedPrimeArchSourceRelativeTrace_im_nonpos_twoHundredEighteen_twentyFifths
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzRe : |z.re| ≤ 218 / 25) :
    (continuedPrimeArchSourceRelativeTrace z).im ≤ 0 :=
  continuedPrimeArchSourceRelativeTrace_im_nonpos_exactOffLineQuartetBand
    (218 / 25) xiOffLineQuartetAccretiveBand_twoHundredEighteen_twentyFifths
    z hzIm hzHalf hzRe

/-- The one-sided positive-frequency response above any exact quartet-admissible radius recovers
the full upper anti-Herglotz condition. -/
theorem continuedPrimeArchUpperAntiHerglotz_of_positiveFrequencyAbove_exactOffLineQuartetBand
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (hhigh : ContinuedPrimeArchPositiveFrequencyAbove R) :
    ContinuedPrimeArchUpperAntiHerglotz := by
  intro z hzIm hzHalf hzeta
  by_cases hlow : |z.re| ≤ R
  · exact continuedPrimeArchSourceRelativeTrace_im_nonpos_exactOffLineQuartetBand
      R hband z hzIm hzHalf hlow
  have habs : R < |z.re| := lt_of_not_ge hlow
  by_cases hpos : R < z.re
  · exact hhigh z hzIm hzHalf hpos hzeta
  have hneg : z.re < -R := by
    have hzle : z.re ≤ R := le_of_not_gt hpos
    by_contra hn
    have hzneg : -R ≤ z.re := le_of_not_gt hn
    exact hlow (abs_le.mpr ⟨hzneg, hzle⟩)
  let w : ℂ := -(starRingEnd ℂ) z
  have hwIm : w.im = z.im := by simp [w]
  have hwRe : w.re = -z.re := by simp [w]
  obtain ⟨hwzeta, htrace⟩ :=
    continuedPrimeArchSourceRelativeTrace_neg_conj_im z hzIm hzHalf hzeta
  have hsign := hhigh w (by rw [hwIm]; exact hzIm)
    (by rw [hwIm]; exact hzHalf) (by rw [hwRe]; linarith)
    (by simpa only [w] using hwzeta)
  rwa [htrace] at hsign

/-- Exact one-sided response criterion at every quartet-admissible radius. -/
theorem continuedPrimeArchPositiveFrequencyAbove_iff_rh_of_exactOffLineQuartetBand
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R) :
    ContinuedPrimeArchPositiveFrequencyAbove R ↔ RiemannHypothesis := by
  constructor
  · intro hhigh
    exact riemannHypothesis_of_continuedPrimeArchUpperAntiHerglotz
      (continuedPrimeArchUpperAntiHerglotz_of_positiveFrequencyAbove_exactOffLineQuartetBand
        R hband hhigh)
  · intro hRH z hzIm hzHalf _hzRe hzeta
    exact (continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis.mpr hRH)
      z hzIm hzHalf hzeta

/-- Clean strengthened one-sided criterion above `218 / 25`. -/
theorem continuedPrimeArchPositiveFrequencyAbove_twoHundredEighteen_twentyFifths_iff_rh :
    ContinuedPrimeArchPositiveFrequencyAbove (218 / 25) ↔ RiemannHypothesis :=
  continuedPrimeArchPositiveFrequencyAbove_iff_rh_of_exactOffLineQuartetBand
    (218 / 25) xiOffLineQuartetAccretiveBand_twoHundredEighteen_twentyFifths

end

end RHTower
