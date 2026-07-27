import GaloisForLFunctions.RHTower.VerifiedHeightAmplification
import GaloisForLFunctions.RHTower.PrimeArchHighFrequencyAccretivity
import GaloisForLFunctions.RHTower.PrimeArchEndpointFrequencyAccretivity
import GaloisForLFunctions.RHTower.PrimeArchSourceUpperBoundGate

/-!
# Verified Xi height transfers to prime--archimedean frequency accretivity

A certificate that all Xi zeros through height `H` lie on the critical line has a direct
source-side consequence.  On every centered frequency band `|Re z| ≤ R` with
`R + 1 / 2 ≤ H`, each line-conjugate pair of relative-resolvent atoms has nonpositive
imaginary part.  Verified zeros give real centered atoms; every unverified zero is more than
one half-unit away horizontally, which dominates its possible transverse displacement inside
the critical strip.

The resulting theorem leaves only the positive-frequency source tail above `R`.  It is a
top-down transfer of a concrete finite-height certificate, not a new zero-location assumption.
The final constants record the exact paper-certified Platt--Trudgian/Arb endpoint; the external
certificate itself remains an explicit hypothesis until it is imported as a formal proof object.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- A multiplicity copy below a verified absolute height has critical real part.  Negative
ordinates are transferred to positive ordinates by Schwarz conjugation. -/
lemma xiZeroCopy_re_eq_half_of_verifiedThrough_of_abs_im_le
    (H : ℝ) (hverified : RHVerifiedThrough H) (q : XiZeroCopy)
    (hheight : |(q.1 : ℂ).im| ≤ H) :
    (q.1 : ℂ).re = 1 / 2 := by
  have hzero : xi (q.1 : ℂ) = 0 := xi_eq_zero_of_mem_divisor_support q.1
  have hre := xi_divisor_support_re_mem_open_unit q.1
  have himne : (q.1 : ℂ).im ≠ 0 := xi_divisor_support_im_ne_zero q.1
  by_cases himpos : 0 < (q.1 : ℂ).im
  · exact hverified hzero hre.1 hre.2 himpos
      ((le_abs_self (q.1 : ℂ).im).trans hheight)
  · have himneg : (q.1 : ℂ).im < 0 := lt_of_le_of_ne (le_of_not_gt himpos) himne
    have hconjZero : xi ((starRingEnd ℂ) (q.1 : ℂ)) = 0 := by
      rw [xi_conj, hzero, map_zero]
    have hconjImPos : 0 < ((starRingEnd ℂ) (q.1 : ℂ)).im := by
      simp only [conj_im]
      linarith
    have hconjImLe : ((starRingEnd ℂ) (q.1 : ℂ)).im ≤ H := by
      simp only [conj_im]
      rw [abs_of_neg himneg] at hheight
      exact hheight
    have hconjRe := hverified hconjZero (by simpa using hre.1) (by simpa using hre.2)
      hconjImPos hconjImLe
    simpa only [conj_re] using hconjRe

/-- A verified Xi height gives a zero-free centered upper-half band.  A zero in that band
would have ordinate at most `H`, hence would be on the critical line; in centered coordinates
that would force its positive imaginary coordinate to vanish. -/
theorem XiC_ne_zero_of_upperHalf_verifiedHeightBand
    (H R : ℝ) (hverified : RHVerifiedThrough H)
    (hband : R + 1 / 2 ≤ H)
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
  have him : (q.1 : ℂ).im = z.re := by
    dsimp only [q, rho]
    simp [mul_im]
  have hheight : |(q.1 : ℂ).im| ≤ H := by
    rw [him]
    linarith [abs_nonneg z.re]
  have hline :=
    xiZeroCopy_re_eq_half_of_verifiedThrough_of_abs_im_le H hverified q hheight
  have hre : (q.1 : ℂ).re = 1 / 2 - z.im := by
    dsimp only [q, rho]
    simp [mul_re]
    ring
  rw [hre] at hline
  linarith

/-- Every line-conjugate relative-resolvent pair has the anti-Herglotz sign inside the band
supplied by a verified Xi height. -/
lemma xiRelativeResolventTerm_lineConj_pair_im_nonpos_of_verifiedHeight
    (H R : ℝ) (hverified : RHVerifiedThrough H)
    (hband : R + 1 / 2 ≤ H)
    (z : ℂ) (hzIm : 0 < z.im) (hzRe : |z.re| ≤ R)
    (q : XiZeroCopy) :
    (xiRelativeResolventTerm z q +
      xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)).im ≤ 0 := by
  let a : ℂ := xiSpectralPoint q
  have haimMem := xiSpectralPoint_im_mem_openHalf q
  have haimAbs : |a.im| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> dsimp only [a] <;> linarith [haimMem.1, haimMem.2]
  have hcore : 0 < (z.re - a.re) ^ 2 + z.im ^ 2 - a.im ^ 2 := by
    by_cases hheight : |(q.1 : ℂ).im| ≤ H
    · have hline :=
        xiZeroCopy_re_eq_half_of_verifiedThrough_of_abs_im_le H hverified q hheight
      have haim : a.im = 0 := by
        simp [a, xiSpectralPoint, mul_im, hline]
      rw [haim]
      nlinarith [sq_pos_of_pos hzIm, sq_nonneg (z.re - a.re)]
    · have hfar : H < |a.re| := by
        have hqfar : H < |(q.1 : ℂ).im| := lt_of_not_ge hheight
        simpa [a, xiSpectralPoint, mul_re] using hqfar
      have hdistLower : |a.re| - |z.re| ≤ |a.re - z.re| :=
        abs_sub_abs_le_abs_sub a.re z.re
      have hdistAbs : 1 / 2 < |z.re - a.re| := by
        rw [abs_sub_comm]
        linarith
      have hdistSq : a.im ^ 2 < (z.re - a.re) ^ 2 := by
        nlinarith [sq_abs a.im, sq_abs (z.re - a.re),
          abs_nonneg a.im, abs_nonneg (z.re - a.re)]
      nlinarith [sq_nonneg z.im]
  exact xiRelativeResolventTerm_lineConj_pair_im_nonpos_of_core z hzIm q hcore

/-- The full Xi relative-resolvent trace has the anti-Herglotz sign on every frequency band
transferred from a verified Xi height. -/
theorem xiRelativeResolventTrace_im_nonpos_of_verifiedHeight
    (H R : ℝ) (hverified : RHVerifiedThrough H)
    (hband : R + 1 / 2 ≤ H)
    (z : ℂ) (hzIm : 0 < z.im) (hXi : XiC z ≠ 0)
    (hzRe : |z.re| ≤ R) :
    (xiRelativeResolventTrace z).im ≤ 0 := by
  have himsum :
      (∑' q : XiZeroCopy,
        (xiRelativeResolventTerm z q +
          xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)).im) ≤ 0 :=
    tsum_nonpos fun q =>
      xiRelativeResolventTerm_lineConj_pair_im_nonpos_of_verifiedHeight
        H R hverified hband z hzIm hzRe q
  linarith [tsum_lineConj_pair_im_eq_two_mul_xiRelativeResolventTrace_im hXi]

/-- The verified-height band is itself pole-free, so the full anti-Herglotz inequality needs no
separate nonvanishing hypothesis there. -/
theorem xiRelativeResolventTrace_im_nonpos_on_verifiedHeightBand
    (H R : ℝ) (hverified : RHVerifiedThrough H)
    (hband : R + 1 / 2 ≤ H)
    (z : ℂ) (hzIm : 0 < z.im) (hzRe : |z.re| ≤ R) :
    (xiRelativeResolventTrace z).im ≤ 0 := by
  exact xiRelativeResolventTrace_im_nonpos_of_verifiedHeight H R hverified hband z hzIm
    (XiC_ne_zero_of_upperHalf_verifiedHeightBand H R hverified hband z hzIm hzRe) hzRe

/-- Source-side verified-height accretivity on the complete pole-free centered band. -/
theorem continuedPrimeArchSourceRelativeTrace_im_nonpos_on_verifiedHeightBand
    (H R : ℝ) (hverified : RHVerifiedThrough H)
    (hband : R + 1 / 2 ≤ H)
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzRe : |z.re| ≤ R) :
    (continuedPrimeArchSourceRelativeTrace z).im ≤ 0 := by
  have hspos : 0 < (1 / 2 + z * I).re :=
    centeredAbscissa_re_pos (by linarith)
  have hs1 : 1 / 2 + z * I ≠ 1 :=
    centeredAbscissa_ne_one (by linarith)
  have hXi :=
    XiC_ne_zero_of_upperHalf_verifiedHeightBand H R hverified hband z hzIm hzRe
  have hzeta : riemannZeta (1 / 2 + z * I) ≠ 0 := by
    intro hzeta
    apply hXi
    simpa only [XiC] using (xi_eq_zero_iff hspos hs1).mpr hzeta
  rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    hspos hs1 hzeta]
  exact xiRelativeResolventTrace_im_nonpos_on_verifiedHeightBand
    H R hverified hband z hzIm hzRe

/-- Source-side form of verified-height frequency accretivity. -/
theorem continuedPrimeArchSourceRelativeTrace_im_nonpos_of_verifiedHeight
    (H R : ℝ) (hverified : RHVerifiedThrough H)
    (hband : R + 1 / 2 ≤ H)
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzRe : |z.re| ≤ R)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    (continuedPrimeArchSourceRelativeTrace z).im ≤ 0 := by
  have hspos : 0 < (1 / 2 + z * I).re :=
    centeredAbscissa_re_pos (by linarith)
  have hs1 : 1 / 2 + z * I ≠ 1 :=
    centeredAbscissa_ne_one (by linarith)
  have hXi := XiC_ne_zero_of_continuedPrimeArch_domain hspos hs1 hzeta
  rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    hspos hs1 hzeta]
  exact xiRelativeResolventTrace_im_nonpos_of_verifiedHeight
    H R hverified hband z hzIm hXi hzRe

/-- A verified central band plus the positive-frequency source tail recovers the full source
anti-Herglotz condition. -/
theorem continuedPrimeArchUpperAntiHerglotz_of_verifiedHeight_and_positiveFrequencyAbove
    (H R : ℝ) (hverified : RHVerifiedThrough H)
    (hband : R + 1 / 2 ≤ H)
    (hhigh : ContinuedPrimeArchPositiveFrequencyAbove R) :
    ContinuedPrimeArchUpperAntiHerglotz := by
  intro z hzIm hzHalf hzeta
  by_cases hlow : |z.re| ≤ R
  · exact continuedPrimeArchSourceRelativeTrace_im_nonpos_of_verifiedHeight
      H R hverified hband z hzIm hzHalf hlow hzeta
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

/-- Under a verified-height certificate, the sole remaining one-sided source tail is exactly RH. -/
theorem continuedPrimeArchPositiveFrequencyAbove_iff_rh_of_verifiedHeight
    (H R : ℝ) (hverified : RHVerifiedThrough H)
    (hband : R + 1 / 2 ≤ H) :
    ContinuedPrimeArchPositiveFrequencyAbove R ↔ RiemannHypothesis := by
  constructor
  · intro hhigh
    exact riemannHypothesis_of_continuedPrimeArchUpperAntiHerglotz
      (continuedPrimeArchUpperAntiHerglotz_of_verifiedHeight_and_positiveFrequencyAbove
        H R hverified hband hhigh)
  · intro hRH z hzIm hzHalf _hzRe hzeta
    exact (continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis.mpr hRH)
      z hzIm hzHalf hzeta

/-- A finite upper ceiling on the sole positive-frequency tail left by a verified central band.
Unlike `ContinuedPrimeArchPositiveFrequencyAbove`, this asks for no sign. -/
def ContinuedPrimeArchPositiveFrequencyAboveImBoundedAbove (R : ℝ) : Prop :=
  ∃ C : ℝ, ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 → R < z.re →
    riemannZeta (1 / 2 + z * I) ≠ 0 →
      (continuedPrimeArchSourceRelativeTrace z).im ≤ C

/-- Verified central accretivity and any finite ceiling on the positive tail give a finite ceiling
on the full centered upper half-strip.  The negative tail is the reflected positive tail. -/
theorem continuedPrimeArchUpperImBoundedAbove_of_verifiedHeight_and_positiveFrequencyAboveImBoundedAbove
    (H R : ℝ) (hverified : RHVerifiedThrough H)
    (hband : R + 1 / 2 ≤ H)
    (hhigh : ContinuedPrimeArchPositiveFrequencyAboveImBoundedAbove R) :
    ContinuedPrimeArchUpperImBoundedAbove := by
  obtain ⟨C, hC⟩ := hhigh
  refine ⟨max C 0, ?_⟩
  intro z hzIm hzHalf hzeta
  by_cases hlow : |z.re| ≤ R
  · exact (continuedPrimeArchSourceRelativeTrace_im_nonpos_of_verifiedHeight
      H R hverified hband z hzIm hzHalf hlow hzeta).trans (le_max_right C 0)
  by_cases hpos : R < z.re
  · exact (hC z hzIm hzHalf hpos hzeta).trans (le_max_left C 0)
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
  calc
    (continuedPrimeArchSourceRelativeTrace z).im =
        (continuedPrimeArchSourceRelativeTrace w).im := htrace.symm
    _ ≤ C := hC w (by rw [hwIm]; exact hzIm)
      (by rw [hwIm]; exact hzHalf) (by rw [hwRe]; linarith)
      (by simpa only [w] using hwzeta)
    _ ≤ max C 0 := le_max_left C 0

/-- A verified central band plus finite upper boundedness of the remaining positive-frequency tail
proves RH. -/
theorem riemannHypothesis_of_verifiedHeight_and_positiveFrequencyAboveImBoundedAbove
    (H R : ℝ) (hverified : RHVerifiedThrough H)
    (hband : R + 1 / 2 ≤ H)
    (hhigh : ContinuedPrimeArchPositiveFrequencyAboveImBoundedAbove R) :
    RiemannHypothesis :=
  riemannHypothesis_of_continuedPrimeArchUpperImBoundedAbove
    (continuedPrimeArchUpperImBoundedAbove_of_verifiedHeight_and_positiveFrequencyAboveImBoundedAbove
      H R hverified hband hhigh)

/-- RH supplies the sharp tail ceiling zero. -/
theorem continuedPrimeArchPositiveFrequencyAboveImBoundedAbove_of_riemannHypothesis
    (R : ℝ) (hRH : RiemannHypothesis) :
    ContinuedPrimeArchPositiveFrequencyAboveImBoundedAbove R := by
  refine ⟨0, ?_⟩
  intro z hzIm hzHalf _hzRe hzeta
  exact (continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis.mpr hRH)
    z hzIm hzHalf hzeta

/-- Under a verified-height certificate, mere finite upper boundedness of the remaining positive
tail is already exactly RH. -/
theorem continuedPrimeArchPositiveFrequencyAboveImBoundedAbove_iff_rh_of_verifiedHeight
    (H R : ℝ) (hverified : RHVerifiedThrough H)
    (hband : R + 1 / 2 ≤ H) :
    ContinuedPrimeArchPositiveFrequencyAboveImBoundedAbove R ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_verifiedHeight_and_positiveFrequencyAboveImBoundedAbove
      H R hverified hband,
    continuedPrimeArchPositiveFrequencyAboveImBoundedAbove_of_riemannHypothesis R⟩

/-- Positive failure law: after a verified central band, false RH forces arbitrarily high positive
spikes on the unverified source tail.  Thus a hypothetical off-line pole cannot hide behind loss
of the anti-Herglotz sign while retaining any finite tail ceiling. -/
theorem exists_continuedPrimeArchSource_im_gt_above_of_not_rh_verifiedHeight
    (H R : ℝ) (hverified : RHVerifiedThrough H)
    (hband : R + 1 / 2 ≤ H) (hnot : ¬ RiemannHypothesis) (C : ℝ) :
    ∃ z : ℂ, 0 < z.im ∧ z.im < 1 / 2 ∧ R < z.re ∧
      riemannZeta (1 / 2 + z * I) ≠ 0 ∧
        C < (continuedPrimeArchSourceRelativeTrace z).im := by
  by_contra h
  apply hnot
  apply riemannHypothesis_of_verifiedHeight_and_positiveFrequencyAboveImBoundedAbove
    H R hverified hband
  refine ⟨C, ?_⟩
  intro z hzIm hzHalf hzRe hzeta
  exact le_of_not_gt fun hgt => h ⟨z, hzIm, hzHalf, hzRe, hzeta, hgt⟩

/-- The source-pure endpoint height gap supplies an unconditional verified-height certificate
through `9 / 2`: in fact there is no Xi zero in that closed ordinate band. -/
theorem rhVerifiedThrough_nine_halves : RHVerifiedThrough (9 / 2) := by
  intro rho hzero _hrePos _hreOne himPos himLe
  exact False.elim ((xi_ne_zero_of_abs_im_le_nine_halves
    (by rw [abs_of_pos himPos]; exact himLe)) hzero)

/-- Unconditional bounded-tail criterion: after the source-pure central band `|Re z| ≤ 4`, any
finite upper ceiling on the positive-frequency remainder is exactly RH. -/
theorem continuedPrimeArchPositiveFrequencyAboveImBoundedAbove_four_iff_rh :
    ContinuedPrimeArchPositiveFrequencyAboveImBoundedAbove 4 ↔
      RiemannHypothesis := by
  exact continuedPrimeArchPositiveFrequencyAboveImBoundedAbove_iff_rh_of_verifiedHeight
    (9 / 2) 4 rhVerifiedThrough_nine_halves (by norm_num)

/-- Positive unconditional failure law at the source-pure threshold four.  If RH is false, the
positive-frequency tail above four exceeds every prescribed finite ceiling. -/
theorem exists_continuedPrimeArchSource_im_gt_above_four_of_not_rh
    (hnot : ¬ RiemannHypothesis) (C : ℝ) :
    ∃ z : ℂ, 0 < z.im ∧ z.im < 1 / 2 ∧ 4 < z.re ∧
      riemannZeta (1 / 2 + z * I) ≠ 0 ∧
        C < (continuedPrimeArchSourceRelativeTrace z).im := by
  exact exists_continuedPrimeArchSource_im_gt_above_of_not_rh_verifiedHeight
    (9 / 2) 4 rhVerifiedThrough_nine_halves (by norm_num) hnot C

/-- Exact endpoint of the published Platt--Trudgian prefix plus the certified one-zero Arb
extension, represented as a rational real number. -/
def plattTrudgianArbVerifiedHeight : ℝ :=
  768044885196911 / 256

/-- The largest centered frequency radius transferred by that exact height using the elementary
half-strip margin. -/
def plattTrudgianArbAccretiveRadius : ℝ :=
  768044885196783 / 256

theorem plattTrudgianArbAccretiveRadius_nonneg :
    0 ≤ plattTrudgianArbAccretiveRadius := by
  norm_num [plattTrudgianArbAccretiveRadius]

theorem plattTrudgianArbAccretiveRadius_add_half :
    plattTrudgianArbAccretiveRadius + 1 / 2 =
      plattTrudgianArbVerifiedHeight := by
  norm_num [plattTrudgianArbAccretiveRadius, plattTrudgianArbVerifiedHeight]

/-- Conditional Lean specialization of the external certified height.  The theorem consumes the
certificate as `RHVerifiedThrough`; importing the published computation is deliberately separate. -/
theorem continuedPrimeArchPositiveFrequencyAbove_plattTrudgianArbRadius_iff_rh
    (hcertificate : RHVerifiedThrough plattTrudgianArbVerifiedHeight) :
    ContinuedPrimeArchPositiveFrequencyAbove plattTrudgianArbAccretiveRadius ↔
      RiemannHypothesis := by
  exact continuedPrimeArchPositiveFrequencyAbove_iff_rh_of_verifiedHeight
    plattTrudgianArbVerifiedHeight plattTrudgianArbAccretiveRadius hcertificate
    plattTrudgianArbAccretiveRadius_add_half.le

/-- The published verified prefix also reduces RH to any finite upper ceiling on the remaining
positive-frequency tail. -/
theorem continuedPrimeArchPositiveFrequencyAboveImBoundedAbove_plattTrudgianArbRadius_iff_rh
    (hcertificate : RHVerifiedThrough plattTrudgianArbVerifiedHeight) :
    ContinuedPrimeArchPositiveFrequencyAboveImBoundedAbove
        plattTrudgianArbAccretiveRadius ↔ RiemannHypothesis := by
  exact continuedPrimeArchPositiveFrequencyAboveImBoundedAbove_iff_rh_of_verifiedHeight
    plattTrudgianArbVerifiedHeight plattTrudgianArbAccretiveRadius hcertificate
    plattTrudgianArbAccretiveRadius_add_half.le

end

end RHTower

namespace RHTower

/-- Unconditional one-sided endpoint at the source-pure threshold four: after the verified central
band `|Re z| ≤ 4`, the signed positive-frequency source tail is exactly RH.  The verified-height
hypothesis is discharged by the endpoint height gap through `9 / 2`. -/
theorem continuedPrimeArchPositiveFrequencyAbove_four_iff_rh :
    ContinuedPrimeArchPositiveFrequencyAbove 4 ↔ RiemannHypothesis :=
  continuedPrimeArchPositiveFrequencyAbove_iff_rh_of_verifiedHeight
    (9 / 2) 4 rhVerifiedThrough_nine_halves (by norm_num)

end RHTower
