import GaloisForLFunctions.RHTower.PrimeArchEndpointFrequencyAccretivity
import GaloisForLFunctions.RHTower.XiEndpointOffLineQuartetHeightGap

/-!
# Prime--archimedean accretivity after off-line quartet amplification

The endpoint four-orbit height law is needed only for off-line zeros.  On-line atoms have zero
transverse spectral coordinate and their conjugate-paired relative-resolvent contribution already
has the anti-Herglotz sign at every frequency.  Combining the two cases proves the source sign on
every central band satisfying
`C * ((R + 1/2)^2 + 1) < 4`, where `C` is the completed endpoint curvature.  In particular this
holds on `|Re z| ≤ 87/10`.

Reflection removes negative frequencies and Gaussian-rational density removes irrational test
points.  The final capstone is an exact RH criterion involving completed prime--Gamma values only
at positive heights above `87/10`.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- Exact endpoint-source band selected by the fourfold charge of an off-critical orbit. -/
def XiEndpointOffLineQuartetAccretiveBand (R : ℝ) : Prop :=
  0 ≤ R ∧
    xiEndpointCompletedCurvature * ((R + 1 / 2) ^ 2 + 1) < 4

/-- Upper-half centered Xi is zero-free throughout every band controlled by the off-line orbit
budget. Possible on-line zeros live on the boundary `im z = 0`; off-line zeros are excluded by
the quartet height law. -/
theorem XiC_ne_zero_of_upperHalf_offLineOrbitBand
    (R : ℝ) (hband : XiEndpointOffLineQuartetAccretiveBand R)
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
  have hheight := four_le_curvature_mul_one_add_im_sq_of_offLine q hoff
  have him : (q.1 : ℂ).im = z.re := by
    dsimp only [q, rho]
    simp [mul_im]
  rw [him] at hheight
  have hzSq : z.re ^ 2 ≤ R ^ 2 := by
    nlinarith [sq_abs z.re, abs_nonneg z.re]
  have hCpos : 0 < xiEndpointCompletedCurvature :=
    xiEndpointCompletedCurvature_pos
  have hzThreshold : z.re ^ 2 < (R + 1 / 2) ^ 2 := by
    nlinarith [hband.1]
  have hscaled :
      xiEndpointCompletedCurvature * (z.re ^ 2 + 1) <
        xiEndpointCompletedCurvature * ((R + 1 / 2) ^ 2 + 1) :=
    mul_lt_mul_of_pos_left (by linarith) hCpos
  linarith [hband.2]

/-- Every line-conjugate resolvent pair is nonpositive on central bands controlled by the
four-orbit endpoint budget.  On-line atoms are automatic; only off-line atoms consume the height
estimate. -/
lemma xiRelativeResolventTerm_lineConj_pair_im_nonpos_offLineOrbit
    (R : ℝ) (hband : XiEndpointOffLineQuartetAccretiveBand R)
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
      have hheight :
          4 ≤ xiEndpointCompletedCurvature * (a.re ^ 2 + 1) := by
        simpa [a, xiSpectralPoint, mul_re] using
          four_le_curvature_mul_one_add_im_sq_of_offLine q hoff
      have hareSq : (R + 1 / 2) ^ 2 < a.re ^ 2 := by
        have hCpos : 0 < xiEndpointCompletedCurvature :=
          xiEndpointCompletedCurvature_pos
        have hscaled :
            xiEndpointCompletedCurvature * ((R + 1 / 2) ^ 2 + 1) <
              xiEndpointCompletedCurvature * (a.re ^ 2 + 1) :=
          hband.2.trans_le hheight
        have hinner : (R + 1 / 2) ^ 2 + 1 < a.re ^ 2 + 1 :=
          lt_of_mul_lt_mul_left hscaled hCpos.le
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
  exact xiRelativeResolventTerm_lineConj_pair_im_nonpos_of_core z hzIm q hcore

/-- Full relative-resolvent trace sign on the orbit-controlled central band. -/
theorem xiRelativeResolventTrace_im_nonpos_offLineOrbitBand
    (R : ℝ) (hband : XiEndpointOffLineQuartetAccretiveBand R)
    (z : ℂ) (hzIm : 0 < z.im) (hzRe : |z.re| ≤ R) :
    (xiRelativeResolventTrace z).im ≤ 0 := by
  have hXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_upperHalf_offLineOrbitBand R hband z hzIm hzRe
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
      xiRelativeResolventTerm_lineConj_pair_im_nonpos_offLineOrbit
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

/-- Source-side form of the orbit-controlled central-band sign. -/
theorem continuedPrimeArchSourceRelativeTrace_im_nonpos_offLineOrbitBand
    (R : ℝ) (hband : XiEndpointOffLineQuartetAccretiveBand R)
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
    XiC_ne_zero_of_upperHalf_offLineOrbitBand R hband z hzIm hzRe
  have hzeta : riemannZeta (1 / 2 + z * I) ≠ 0 := by
    exact (xi_eq_zero_iff hspos hs1).not.mp (by simpa only [XiC] using hXi)
  rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    hspos hs1 hzeta]
  exact xiRelativeResolventTrace_im_nonpos_offLineOrbitBand
    R hband z hzIm hzRe

/-- The explicit radius `87/10` satisfies the exact four-orbit endpoint band inequality. -/
theorem xiEndpointOffLineQuartetAccretiveBand_eightySeven_tenths :
    XiEndpointOffLineQuartetAccretiveBand (87 / 10) := by
  refine ⟨by norm_num, ?_⟩
  have hCpos : 0 < xiEndpointCompletedCurvature :=
    xiEndpointCompletedCurvature_pos
  have hC := xiEndpointCompletedCurvature_lt_two_over_fortyThree
  nlinarith

/-- The rational central band used by the final one-sided criterion. -/
theorem continuedPrimeArchSourceRelativeTrace_im_nonpos_eightySeven_tenths
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzRe : |z.re| ≤ 87 / 10) :
    (continuedPrimeArchSourceRelativeTrace z).im ≤ 0 := by
  exact continuedPrimeArchSourceRelativeTrace_im_nonpos_offLineOrbitBand
    (87 / 10) xiEndpointOffLineQuartetAccretiveBand_eightySeven_tenths
      z hzIm hzHalf hzRe

/-- The one-sided response above any four-orbit endpoint band recovers the full source sign. -/
theorem continuedPrimeArchUpperAntiHerglotz_of_positiveFrequencyAbove_offLineQuartetBand
    (R : ℝ) (hband : XiEndpointOffLineQuartetAccretiveBand R)
    (hhigh : ContinuedPrimeArchPositiveFrequencyAbove R) :
    ContinuedPrimeArchUpperAntiHerglotz := by
  intro z hzIm hzHalf hzeta
  by_cases hlow : |z.re| ≤ R
  · exact continuedPrimeArchSourceRelativeTrace_im_nonpos_offLineOrbitBand
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

/-- **Exact off-line-quartet response criterion for RH.**  For every radius selected by the
fourfold endpoint source inequality, only positive frequencies above that radius remain. -/
theorem continuedPrimeArchPositiveFrequencyAbove_iff_riemannHypothesis_of_offLineQuartetBand
    (R : ℝ) (hband : XiEndpointOffLineQuartetAccretiveBand R) :
    ContinuedPrimeArchPositiveFrequencyAbove R ↔ RiemannHypothesis := by
  constructor
  · intro hhigh
    exact riemannHypothesis_of_continuedPrimeArchUpperAntiHerglotz
      (continuedPrimeArchUpperAntiHerglotz_of_positiveFrequencyAbove_offLineQuartetBand
        R hband hhigh)
  · intro hRH z hzIm hzHalf _hzRe hzeta
    exact (continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis.mpr hRH)
      z hzIm hzHalf hzeta

/-- After the quartet discharge, only positive frequencies above `87/10` remain. -/
def ContinuedPrimeArchPositiveAboveEightySevenTenthsUpperAntiHerglotz : Prop :=
  ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 → 87 / 10 < z.re →
    riemannZeta (1 / 2 + z * I) ≠ 0 →
      (continuedPrimeArchSourceRelativeTrace z).im ≤ 0

theorem continuedPrimeArchUpperAntiHerglotz_of_positiveAboveEightySevenTenths
    (hhigh : ContinuedPrimeArchPositiveAboveEightySevenTenthsUpperAntiHerglotz) :
    ContinuedPrimeArchUpperAntiHerglotz := by
  intro z hzIm hzHalf hzeta
  by_cases hlow : |z.re| ≤ 87 / 10
  · exact continuedPrimeArchSourceRelativeTrace_im_nonpos_eightySeven_tenths
      z hzIm hzHalf hlow
  have habs : 87 / 10 < |z.re| := lt_of_not_ge hlow
  by_cases hpos : 87 / 10 < z.re
  · exact hhigh z hzIm hzHalf hpos hzeta
  have hneg : z.re < -(87 / 10) := by
    have hzle : z.re ≤ 87 / 10 := le_of_not_gt hpos
    by_contra hn
    have hzneg : -(87 / 10) ≤ z.re := le_of_not_gt hn
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

theorem continuedPrimeArchPositiveAboveEightySevenTenths_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ContinuedPrimeArchPositiveAboveEightySevenTenthsUpperAntiHerglotz := by
  intro z hzIm hzHalf _hzRe hzeta
  exact (continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis.mpr hRH)
    z hzIm hzHalf hzeta

/-- Exact centered source criterion after the off-line quartet discharge. -/
theorem continuedPrimeArchPositiveAboveEightySevenTenths_iff_riemannHypothesis :
    ContinuedPrimeArchPositiveAboveEightySevenTenthsUpperAntiHerglotz ↔
      RiemannHypothesis :=
  ⟨fun h => riemannHypothesis_of_continuedPrimeArchUpperAntiHerglotz
      (continuedPrimeArchUpperAntiHerglotz_of_positiveAboveEightySevenTenths h),
    continuedPrimeArchPositiveAboveEightySevenTenths_of_riemannHypothesis⟩

/-- In original coordinates, completed prime--Gamma accretivity is needed only above height
`87/10` in the left critical half-strip. -/
def CompletedPrimeGammaPositiveAboveEightySevenTenthsAccretive : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → 87 / 10 < s.im →
    riemannZeta s ≠ 0 → 0 ≤ (completedPrimeGammaFlux s).re

theorem continuedPrimeArchPositiveAboveEightySevenTenths_of_completedPrimeGamma
    (hacc : CompletedPrimeGammaPositiveAboveEightySevenTenthsAccretive) :
    ContinuedPrimeArchPositiveAboveEightySevenTenthsUpperAntiHerglotz := by
  intro z hzIm hzHalf hzRe hzeta
  let s : ℂ := 1 / 2 + z * I
  have hsRe : s.re = 1 / 2 - z.im := by
    simp [s, mul_re]
    ring
  have hsIm : s.im = z.re := by simp [s, mul_im]
  have hspos : 0 < s.re := by rw [hsRe]; linarith
  have hshalf : s.re < 1 / 2 := by rw [hsRe]; linarith
  have haccS := hacc s hspos hshalf (by rw [hsIm]; exact hzRe)
    (by simpa only [s] using hzeta)
  rw [continuedPrimeArchSourceRelativeTrace]
  change (-I * (infinitePrimeFlux s - logDeriv archFactor s)).im ≤ 0
  simp only [mul_im, I_re, zero_mul, neg_im, I_im, neg_mul, one_mul]
  dsimp only [completedPrimeGammaFlux] at haccS
  linarith

theorem completedPrimeGammaPositiveAboveEightySevenTenths_of_continuedPrimeArch
    (hsource : ContinuedPrimeArchPositiveAboveEightySevenTenthsUpperAntiHerglotz) :
    CompletedPrimeGammaPositiveAboveEightySevenTenthsAccretive := by
  intro s hspos hshalf hsIm hzeta
  let z : ℂ := (s - 1 / 2) * (-I)
  have hcoord : 1 / 2 + z * I = s := by
    dsimp only [z]
    rw [mul_assoc]
    have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
    rw [hI, mul_one]
    ring
  have hzIm : z.im = 1 / 2 - s.re := by simp [z]
  have hzRe : z.re = s.im := by simp [z, mul_re]
  have hsourceZ := hsource z (by rw [hzIm]; linarith)
    (by rw [hzIm]; linarith) (by rw [hzRe]; exact hsIm)
    (by rw [hcoord]; exact hzeta)
  rw [continuedPrimeArchSourceRelativeTrace, hcoord] at hsourceZ
  change (-I * (infinitePrimeFlux s - logDeriv archFactor s)).im ≤ 0 at hsourceZ
  simp only [mul_im, I_re, zero_mul, neg_im, I_im, neg_mul, one_mul] at hsourceZ
  dsimp only [completedPrimeGammaFlux]
  linarith

/-- Exact original-coordinate criterion after the off-line quartet discharge. -/
theorem completedPrimeGammaPositiveAboveEightySevenTenths_iff_riemannHypothesis :
    CompletedPrimeGammaPositiveAboveEightySevenTenthsAccretive ↔ RiemannHypothesis := by
  rw [show CompletedPrimeGammaPositiveAboveEightySevenTenthsAccretive ↔
      ContinuedPrimeArchPositiveAboveEightySevenTenthsUpperAntiHerglotz from
    ⟨continuedPrimeArchPositiveAboveEightySevenTenths_of_completedPrimeGamma,
      completedPrimeGammaPositiveAboveEightySevenTenths_of_continuedPrimeArch⟩]
  exact continuedPrimeArchPositiveAboveEightySevenTenths_iff_riemannHypothesis

/-- Countable version at Gaussian-rational source values. -/
def CompletedPrimeGammaGaussianRatPositiveAboveEightySevenTenthsAccretive : Prop :=
  ∀ q : ℚ × ℚ, 0 < (gaussianRatPoint q).re →
    (gaussianRatPoint q).re < 1 / 2 →
    87 / 10 < (gaussianRatPoint q).im →
    riemannZeta (gaussianRatPoint q) ≠ 0 →
      0 ≤ (completedPrimeGammaFlux (gaussianRatPoint q)).re

theorem completedPrimeGammaGaussianRatPositiveAboveEightySevenTenths_of_full
    (hfull : CompletedPrimeGammaPositiveAboveEightySevenTenthsAccretive) :
    CompletedPrimeGammaGaussianRatPositiveAboveEightySevenTenthsAccretive := by
  intro q hq0 hqh hqIm hqz
  exact hfull (gaussianRatPoint q) hq0 hqh hqIm hqz

theorem completedPrimeGammaPositiveAboveEightySevenTenths_of_gaussianRat
    (hrat : CompletedPrimeGammaGaussianRatPositiveAboveEightySevenTenthsAccretive) :
    CompletedPrimeGammaPositiveAboveEightySevenTenthsAccretive := by
  intro s hspos hshalf hsIm hzeta
  by_contra hnonneg
  have hneg : (completedPrimeGammaFlux s).re < 0 := lt_of_not_ge hnonneg
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [one_re] at hre
    linarith
  have hcont := continuousAt_completedPrimeGammaFlux hspos hs1 hzeta
  have hrePos : {w : ℂ | 0 < w.re} ∈ nhds s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hspos
  have hreHalf : {w : ℂ | w.re < 1 / 2} ∈ nhds s :=
    (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hshalf
  have himHigh : {w : ℂ | 87 / 10 < w.im} ∈ nhds s :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hsIm
  have hzetaAn : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs1
  have hzetaNe : {w : ℂ | riemannZeta w ≠ 0} ∈ nhds s :=
    hzetaAn.continuousAt.eventually_ne hzeta
  have hfre : ContinuousAt (fun w => (completedPrimeGammaFlux w).re) s :=
    Complex.continuous_re.continuousAt.comp hcont
  have hfluxNeg : {w : ℂ | (completedPrimeGammaFlux w).re < 0} ∈ nhds s :=
    hfre.tendsto (Iio_mem_nhds hneg)
  have hall : {w : ℂ | 0 < w.re} ∩ {w : ℂ | w.re < 1 / 2} ∩
      {w : ℂ | 87 / 10 < w.im} ∩ {w : ℂ | riemannZeta w ≠ 0} ∩
      {w : ℂ | (completedPrimeGammaFlux w).re < 0} ∈ nhds s :=
    inter_mem (inter_mem (inter_mem (inter_mem hrePos hreHalf) himHigh) hzetaNe)
      hfluxNeg
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hall
  obtain ⟨q, hqball⟩ := denseRange_gaussianRatPoint.exists_mem_open isOpen_ball
    ⟨s, mem_ball_self hr⟩
  have hq := hball hqball
  have hqnonneg := hrat q hq.1.1.1.1 hq.1.1.1.2 hq.1.1.2 hq.1.2
  exact (not_lt_of_ge hqnonneg) hq.2

/-- Exact countable positive-height prime--Gamma value criterion after quartet discharge. -/
theorem completedPrimeGammaGaussianRatPositiveAboveEightySevenTenths_iff_riemannHypothesis :
    CompletedPrimeGammaGaussianRatPositiveAboveEightySevenTenthsAccretive ↔
      RiemannHypothesis := by
  constructor
  · intro hrat
    exact completedPrimeGammaPositiveAboveEightySevenTenths_iff_riemannHypothesis.mp
      (completedPrimeGammaPositiveAboveEightySevenTenths_of_gaussianRat hrat)
  · intro hRH
    exact completedPrimeGammaGaussianRatPositiveAboveEightySevenTenths_of_full
      (completedPrimeGammaPositiveAboveEightySevenTenths_iff_riemannHypothesis.mpr hRH)

end

end RHTower
