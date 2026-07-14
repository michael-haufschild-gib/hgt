import GaloisForLFunctions.RHTower.PrimeArchHighFrequencyAccretivity

/-!
# Endpoint-optimal central-frequency accretivity

The completed endpoint curvature controls not only a zero-height gap but the exact central
frequency range on which every conjugate-paired Xi resolvent atom has the anti-Herglotz sign.
The admissible radius `R` is characterized by the source inequality

`C * ((R + 1 / 2)^2 + 1) < 1`,

where `C = xiEndpointCompletedCurvature`.  A rational corollary enlarges the previously discharged
band from radius `4` to radius `161 / 40`.  Consequently the remaining RH-bearing response
condition begins strictly above `161 / 40` and only on the positive-frequency side.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- Exact endpoint-source band condition for paired-resolvent accretivity. -/
def XiEndpointAccretiveBand (R : ℝ) : Prop :=
  0 ≤ R ∧ R ≤ 9 / 2 ∧
    xiEndpointCompletedCurvature * ((R + 1 / 2) ^ 2 + 1) < 1

/-- The exact endpoint source-height law makes every conjugate-paired relative-resolvent atom
nonpositive throughout any admissible endpoint band. -/
lemma xiRelativeResolventTerm_lineConj_pair_im_nonpos_of_endpointBand
    (R : ℝ) (hband : XiEndpointAccretiveBand R)
    (z : ℂ) (hzIm : 0 < z.im) (hzRe : |z.re| ≤ R)
    (q : XiZeroCopy) :
    (xiRelativeResolventTerm z q +
      xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)).im ≤ 0 := by
  let a : ℂ := xiSpectralPoint q
  have hCpos : 0 < xiEndpointCompletedCurvature :=
    xiEndpointCompletedCurvature_pos
  have hareSqLower :
      1 / xiEndpointCompletedCurvature - 1 ≤ a.re ^ 2 := by
    simpa [a, xiSpectralPoint, mul_re] using
      xiZeroCopy_im_sq_ge_endpoint_source_inverse_gap q
  have hradiusInv :
      (R + 1 / 2) ^ 2 + 1 < 1 / xiEndpointCompletedCurvature := by
    rw [lt_div_iff₀ hCpos]
    simpa [mul_comm] using hband.2.2
  have hareSq : (R + 1 / 2) ^ 2 < a.re ^ 2 := by
    linarith
  have hareAbs : R + 1 / 2 < |a.re| := by
    nlinarith [sq_abs a.re, abs_nonneg a.re, hband.1]
  have haimMem := xiSpectralPoint_im_mem_openHalf q
  have haimAbs : |a.im| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith [haimMem.1, haimMem.2]
  have hdistLower : |a.re| - |z.re| ≤ |a.re - z.re| :=
    abs_sub_abs_le_abs_sub a.re z.re
  have hdistAbs : 1 / 2 < |z.re - a.re| := by
    rw [abs_sub_comm]
    linarith
  have hdistSq : a.im ^ 2 < (z.re - a.re) ^ 2 := by
    nlinarith [sq_abs a.im, sq_abs (z.re - a.re),
      abs_nonneg a.im, abs_nonneg (z.re - a.re)]
  have hcore : 0 < (z.re - a.re) ^ 2 + z.im ^ 2 - a.im ^ 2 := by
    nlinarith [sq_nonneg z.im]
  have hza : z ≠ a := by
    intro h
    have hre := congrArg Complex.re h
    have : z.re - a.re = 0 := by linarith
    rw [this, abs_zero] at hdistAbs
    linarith
  have hzac : z ≠ (starRingEnd ℂ) a := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.conj_re] at hre
    have : z.re - a.re = 0 := by linarith
    rw [this, abs_zero] at hdistAbs
    linarith
  have hdenOne :
      0 < (z.re - a.re) ^ 2 + (z.im - a.im) ^ 2 := by
    nlinarith [sq_nonneg (z.im - a.im)]
  have hdenTwo :
      0 < (z.re - a.re) ^ 2 + (z.im + a.im) ^ 2 := by
    nlinarith [sq_nonneg (z.im + a.im)]
  rw [xiRelativeResolventTerm, xiRelativeResolventTerm,
    xiSpectralPoint_lineConj]
  change ((a⁻¹ - (a - z)⁻¹) +
      (((starRingEnd ℂ) a)⁻¹ - ((starRingEnd ℂ) a - z)⁻¹)).im ≤ 0
  rw [relativeResolvent_conj_pair_im_formula z a
    (xiSpectralPoint_ne_zero q) hza (by simpa using hzac)]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by nlinarith [hzIm]) hcore.le)
    (mul_nonneg hdenOne.le hdenTwo.le)

/-- The full Xi relative-resolvent trace is anti-Herglotz on every endpoint-admissible central
frequency band. -/
theorem xiRelativeResolventTrace_im_nonpos_of_endpointBand
    (R : ℝ) (hband : XiEndpointAccretiveBand R)
    (z : ℂ) (hzIm : 0 < z.im) (hzRe : |z.re| ≤ R) :
    (xiRelativeResolventTrace z).im ≤ 0 := by
  have hXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_abs_re_le_nine_halves (hzRe.trans hband.2.1)
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
      xiRelativeResolventTerm_lineConj_pair_im_nonpos_of_endpointBand
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

/-- Source-side form of the endpoint-optimal central-band sign. -/
theorem continuedPrimeArchSourceRelativeTrace_im_nonpos_of_endpointBand
    (R : ℝ) (hband : XiEndpointAccretiveBand R)
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
    XiC_ne_zero_of_abs_re_le_nine_halves (hzRe.trans hband.2.1)
  have hzeta : riemannZeta (1 / 2 + z * I) ≠ 0 := by
    exact (xi_eq_zero_iff hspos hs1).not.mp (by simpa only [XiC] using hXi)
  rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    hspos hs1 hzeta]
  exact xiRelativeResolventTrace_im_nonpos_of_endpointBand
    R hband z hzIm hzRe

/-- The explicit rational radius `161 / 40` satisfies the exact endpoint band inequality. -/
theorem xiEndpointAccretiveBand_oneSixtyOne_fortieths :
    XiEndpointAccretiveBand (161 / 40) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  have hCpos : 0 < xiEndpointCompletedCurvature :=
    xiEndpointCompletedCurvature_pos
  have hC := xiEndpointCompletedCurvature_lt_two_over_fortyThree
  nlinarith

/-- Unconditional source anti-Herglotz sign on the enlarged rational central band
`|Re z| ≤ 161 / 40`. -/
theorem continuedPrimeArchSourceRelativeTrace_im_nonpos_oneSixtyOne_fortieths
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzRe : |z.re| ≤ 161 / 40) :
    (continuedPrimeArchSourceRelativeTrace z).im ≤ 0 :=
  continuedPrimeArchSourceRelativeTrace_im_nonpos_of_endpointBand
    (161 / 40) xiEndpointAccretiveBand_oneSixtyOne_fortieths
    z hzIm hzHalf hzRe

/-- The only source sign remaining above an endpoint-admissible radius: positive frequencies
strictly beyond that radius. -/
def ContinuedPrimeArchPositiveFrequencyAbove (R : ℝ) : Prop :=
  ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 → R < z.re →
    riemannZeta (1 / 2 + z * I) ≠ 0 →
      (continuedPrimeArchSourceRelativeTrace z).im ≤ 0

/-- The one-sided response condition above any endpoint-admissible radius, together with the
unconditional central band, recovers the full source anti-Herglotz condition. -/
theorem continuedPrimeArchUpperAntiHerglotz_of_positiveFrequencyAbove_endpointBand
    (R : ℝ) (hband : XiEndpointAccretiveBand R)
    (hhigh : ContinuedPrimeArchPositiveFrequencyAbove R) :
    ContinuedPrimeArchUpperAntiHerglotz := by
  intro z hzIm hzHalf hzeta
  by_cases hlow : |z.re| ≤ R
  · exact continuedPrimeArchSourceRelativeTrace_im_nonpos_of_endpointBand
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

/-- **Endpoint-frequency response criterion for RH.**  For every endpoint-admissible radius,
RH is equivalent to the completed prime--Gamma response sign only at positive frequencies above
that radius. -/
theorem continuedPrimeArchPositiveFrequencyAbove_iff_riemannHypothesis
    (R : ℝ) (hband : XiEndpointAccretiveBand R) :
    ContinuedPrimeArchPositiveFrequencyAbove R ↔ RiemannHypothesis := by
  constructor
  · intro hhigh
    exact riemannHypothesis_of_continuedPrimeArchUpperAntiHerglotz
      (continuedPrimeArchUpperAntiHerglotz_of_positiveFrequencyAbove_endpointBand
        R hband hhigh)
  · intro hRH z hzIm hzHalf _hzRe hzeta
    exact (continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis.mpr hRH)
      z hzIm hzHalf hzeta

/-- Clean strengthened one-sided criterion: only positive frequencies above `161 / 40` remain. -/
theorem continuedPrimeArchPositiveFrequencyAbove_oneSixtyOne_fortieths_iff_rh :
    ContinuedPrimeArchPositiveFrequencyAbove (161 / 40) ↔ RiemannHypothesis :=
  continuedPrimeArchPositiveFrequencyAbove_iff_riemannHypothesis
    (161 / 40) xiEndpointAccretiveBand_oneSixtyOne_fortieths

end

end RHTower
