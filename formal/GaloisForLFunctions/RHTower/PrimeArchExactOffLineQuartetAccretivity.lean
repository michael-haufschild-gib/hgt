import GaloisForLFunctions.RHTower.PrimeArchOffLineQuartetKMSMaster

/-!
# Exact off-line-quartet accretive band

The four FE--Schwarz copies of an off-line Xi zero consume four equal endpoint cross charges.
Keeping the exact completed curvature instead of replacing it immediately by `2 / 43` gives the
natural central-band condition

`C * ((R + 1 / 2)^(2 : ℕ) + 1) < 4`.

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
band.  It is the same condition as `XiEndpointOffLineQuartetAccretiveBand`, under the name used by
the exact quartet development. -/
abbrev XiOffLineQuartetAccretiveBand (R : ℝ) : Prop :=
  XiEndpointOffLineQuartetAccretiveBand R
/-- Exact four-charge height law before replacing the completed endpoint curvature by a rational
upper bound. -/
theorem four_le_endpointCurvature_mul_one_add_im_sq_of_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    4 ≤ xiEndpointCompletedCurvature * ((q.1 : ℂ).im ^ (2 : ℕ) + 1) := by
  have hlower := endpoint_cross_term_re_ge_inv_one_add_im_sq q
  have horbit := four_mul_xiEndpointCrossCharge_le_curvature_of_offLine q hoff
  have hden : 0 < (q.1 : ℂ).im ^ (2 : ℕ) + 1 := by positivity
  have hcharge : 4 / ((q.1 : ℂ).im ^ (2 : ℕ) + 1) ≤
      4 * xiEndpointCrossCharge q := by
    calc
      4 / ((q.1 : ℂ).im ^ (2 : ℕ) + 1) =
          4 * (1 / ((q.1 : ℂ).im ^ (2 : ℕ) + 1)) := by ring
      _ ≤ 4 * xiEndpointCrossCharge q :=
        mul_le_mul_of_nonneg_left hlower (by norm_num)
  have hbudget : 4 / ((q.1 : ℂ).im ^ (2 : ℕ) + 1) ≤
      xiEndpointCompletedCurvature := hcharge.trans horbit
  rw [div_le_iff₀ hden] at hbudget
  simpa [mul_comm] using hbudget

/-- **Positive self-exclusion law for the quartet band.**  Every exact accretive-band radius
stays more than one half-unit below the absolute ordinate of every off-line Xi zero.  Thus the
endpoint quartet budget supplies a genuine central prefix, but cannot exclude the same quartet
that pays for the prefix without an additional propagation mechanism. -/
theorem xiOffLineQuartetAccretiveBand_add_half_lt_abs_im_of_offLine
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    R + 1 / 2 < |(q.1 : ℂ).im| := by
  have hfour :=
    four_le_endpointCurvature_mul_one_add_im_sq_of_offLine q hoff
  have hCpos : 0 < xiEndpointCompletedCurvature :=
    xiEndpointCompletedCurvature_pos
  have hmul :
      xiEndpointCompletedCurvature * ((R + 1 / 2) ^ (2 : ℕ) + 1) <
        xiEndpointCompletedCurvature * ((q.1 : ℂ).im ^ (2 : ℕ) + 1) :=
    hband.2.trans_le hfour
  have hsq : (R + 1 / 2) ^ (2 : ℕ) < (q.1 : ℂ).im ^ (2 : ℕ) := by
    have hinner := lt_of_mul_lt_mul_left hmul hCpos.le
    linarith
  have hnonneg : 0 ≤ R + 1 / 2 := by linarith [hband.1]
  nlinarith [sq_abs (q.1 : ℂ).im, abs_nonneg (q.1 : ℂ).im]

/-- In particular, the exact quartet band cannot be closed by choosing the absolute ordinate of
the assumed off-line zero as its own radius. -/
theorem not_xiOffLineQuartetAccretiveBand_at_abs_im_of_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    ¬ XiOffLineQuartetAccretiveBand |(q.1 : ℂ).im| := by
  intro hband
  have hbuffer :=
    xiOffLineQuartetAccretiveBand_add_half_lt_abs_im_of_offLine
      |(q.1 : ℂ).im| hband q hoff
  nlinarith [abs_nonneg (q.1 : ℂ).im]

/-- **Sharpened rational off-line height gap.**  The exact quartet budget together with the
available rational endpoint-curvature certificate forces every off-critical Xi zero above the
squared ordinate `7907 / 93`. -/
theorem xiZeroCopy_offLine_sevenThousandNineHundredSeven_over_ninetyThree_lt_im_sq
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    7907 / 93 < (q.1 : ℂ).im ^ (2 : ℕ) := by
  have hbudget :=
    four_le_endpointCurvature_mul_one_add_im_sq_of_offLine q hoff
  have hC := xiEndpointCompletedCurvature_lt_ninetyThree_over_twoThousand
  nlinarith [sq_nonneg (q.1 : ℂ).im]

/-- **Source-produced critical-line group.** Every Xi zero copy in the closed central squared-height
band `Im(ρ)^(2 : ℕ) ≤ 7907 / 93` lies on the critical line.  This is the direct contrapositive packaging
of the endpoint-curvature quartet gap, with no external zero computation or RH hypothesis. -/
theorem xiZeroCopy_re_eq_half_of_im_sq_le_sevenThousandNineHundredSeven_over_ninetyThree
    (q : XiZeroCopy)
    (hheight : (q.1 : ℂ).im ^ (2 : ℕ) ≤ 7907 / 93) :
    (q.1 : ℂ).re = 1 / 2 := by
  by_contra hoff
  have hgap :=
    xiZeroCopy_offLine_sevenThousandNineHundredSeven_over_ninetyThree_lt_im_sq q hoff
  linarith

/-- Upper-half centered Xi is zero-free on every exact quartet-admissible band.  On-line zeros
lie on the boundary `Im z = 0`; a zero in the open upper half would be off-line and would violate
the four-charge height law. -/
theorem XiC_ne_zero_of_upperHalf_exactOffLineQuartetBand
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (z : ℂ) (hzIm : 0 < z.im) (hzRe : |z.re| ≤ R) :
    XiC z ≠ 0 :=
  XiC_ne_zero_of_upperHalf_offLineOrbitBand R hband z hzIm hzRe
/-- Full relative-resolvent trace sign on every exact quartet-admissible band. -/
theorem xiRelativeResolventTrace_im_nonpos_exactOffLineQuartetBand
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (z : ℂ) (hzIm : 0 < z.im) (hzRe : |z.re| ≤ R) :
    (xiRelativeResolventTrace z).im ≤ 0 :=
  xiRelativeResolventTrace_im_nonpos_offLineOrbitBand R hband z hzIm hzRe
/-- Source-side form of the exact quartet central-band sign. -/
theorem continuedPrimeArchSourceRelativeTrace_im_nonpos_exactOffLineQuartetBand
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzRe : |z.re| ≤ R) :
    (continuedPrimeArchSourceRelativeTrace z).im ≤ 0 :=
  continuedPrimeArchSourceRelativeTrace_im_nonpos_offLineOrbitBand
    R hband z hzIm hzHalf hzRe
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
    ContinuedPrimeArchUpperAntiHerglotz :=
  continuedPrimeArchUpperAntiHerglotz_of_positiveFrequencyAbove_offLineQuartetBand
    R hband hhigh
/-- Exact one-sided response criterion at every quartet-admissible radius. -/
theorem continuedPrimeArchPositiveFrequencyAbove_iff_rh_of_exactOffLineQuartetBand
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R) :
    ContinuedPrimeArchPositiveFrequencyAbove R ↔ RiemannHypothesis :=
  continuedPrimeArchPositiveFrequencyAbove_iff_riemannHypothesis_of_offLineQuartetBand
    R hband
/-- Clean strengthened one-sided criterion above `218 / 25`. -/
theorem continuedPrimeArchPositiveFrequencyAbove_twoHundredEighteen_twentyFifths_iff_rh :
    ContinuedPrimeArchPositiveFrequencyAbove (218 / 25) ↔ RiemannHypothesis :=
  continuedPrimeArchPositiveFrequencyAbove_iff_rh_of_exactOffLineQuartetBand
    (218 / 25) xiOffLineQuartetAccretiveBand_twoHundredEighteen_twentyFifths

end

end RHTower
