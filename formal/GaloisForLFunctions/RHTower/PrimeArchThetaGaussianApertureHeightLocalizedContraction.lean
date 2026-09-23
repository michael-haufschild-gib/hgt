import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureScoreConcentration

open Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

theorem thetaCuspSourceTerm_one_le_four_pi_sq_mul_leadingChannel (x : ℝ) :
    thetaCuspSourceTerm x 1 ≤
      4 * Real.pi ^ 2 * thetaCuspPolynomialAtom (X ^ 4) 1 x := by
  have htwo : 0 ≤ thetaCuspPolynomialAtom (X ^ 2) 1 x := by
    simp only [thetaCuspPolynomialAtom, Nat.cast_one, one_mul, eval_pow, eval_X]
    positivity
  rw [thetaCuspSourceTerm_one_eq_tailChannelDifference]
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 6 * Real.pi) htwo]

theorem thetaCuspHigherAtomExactHeightDamping_nonneg (x : ℝ) :
    0 ≤ thetaCuspHigherAtomExactHeightDamping x := by
  unfold thetaCuspHigherAtomExactHeightDamping
  positivity

theorem thetaCuspHigherAtomExactHeightDamping_le_one
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspHigherAtomExactHeightDamping x ≤ 1 := by
  unfold thetaCuspHigherAtomExactHeightDamping
  rw [Real.exp_le_one_iff]
  have hexp : 1 ≤ Real.exp (2 * x) := by
    simpa using Real.exp_le_exp.mpr (by linarith : 0 ≤ 2 * x)
  nlinarith [Real.pi_pos]

theorem thetaCuspHigherAtomExactHeightDamping_le_of_le
    {x y : ℝ} (hxy : x ≤ y) :
    thetaCuspHigherAtomExactHeightDamping y ≤
      thetaCuspHigherAtomExactHeightDamping x := by
  unfold thetaCuspHigherAtomExactHeightDamping
  apply Real.exp_le_exp.mpr
  have hexp : Real.exp (2 * x) ≤ Real.exp (2 * y) :=
    Real.exp_le_exp.mpr (by linarith)
  nlinarith [Real.pi_pos]

/-- A source-scale damping factor is bounded by its half-saddle value plus a quadratic
penalty measured by the exact response-centered saddle error. -/
theorem thetaCuspHigherAtomExactHeightDamping_le_halfSaddle_add_error
    {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    thetaCuspHigherAtomExactHeightDamping x ≤
      thetaCuspHigherAtomExactHeightDamping (s / 2) +
        (2 / s ^ 4) * (x ^ 2 - s ^ 2) ^ 2 := by
  by_cases hhigh : s / 2 ≤ x
  · have hdamp := thetaCuspHigherAtomExactHeightDamping_le_of_le hhigh
    exact hdamp.trans (le_add_of_nonneg_right (by positivity))
  · have hxlt : x < s / 2 := lt_of_not_ge hhigh
    have hshalf : 0 ≤ s / 2 := by linarith
    have hxsq : x ^ 2 < (s / 2) ^ 2 :=
      (sq_lt_sq₀ hx hshalf).2 hxlt
    have hgap : 3 * s ^ 2 / 4 ≤ s ^ 2 - x ^ 2 := by
      nlinarith
    have hgap0 : 0 ≤ 3 * s ^ 2 / 4 := by positivity
    have herrsq : (3 * s ^ 2 / 4) ^ 2 ≤ (x ^ 2 - s ^ 2) ^ 2 := by
      calc
        (3 * s ^ 2 / 4) ^ 2 ≤ (s ^ 2 - x ^ 2) ^ 2 :=
          (sq_le_sq₀ hgap0 (by linarith)).2 hgap
        _ = (x ^ 2 - s ^ 2) ^ 2 := by ring
    have hs4 : 0 < s ^ 4 := pow_pos hs 4
    have hone : 1 ≤ (2 / s ^ 4) * (x ^ 2 - s ^ 2) ^ 2 := by
      rw [show (2 / s ^ 4) * (x ^ 2 - s ^ 2) ^ 2 =
        (2 * (x ^ 2 - s ^ 2) ^ 2) / s ^ 4 by ring,
        le_div_iff₀ hs4]
      nlinarith
    exact (thetaCuspHigherAtomExactHeightDamping_le_one hx).trans
      (hone.trans (le_add_of_nonneg_left
        (thetaCuspHigherAtomExactHeightDamping_nonneg (s / 2))))

/-- Leading-channel moment with the exact all-higher-atom damping retained. -/
def thetaCuspGaussianApertureLeadingChannelDampedMoment
    (lambda : ℝ) (j : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0,
    thetaCuspHigherAtomExactHeightDamping x *
      (x ^ (2 * j) * thetaCuspGaussianApertureLeadingChannelWeight lambda x)

theorem integrableOn_thetaCuspGaussianApertureLeadingChannelDampedMomentIntegrand
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    IntegrableOn (fun x : ℝ =>
      thetaCuspHigherAtomExactHeightDamping x *
        (x ^ (2 * j) * thetaCuspGaussianApertureLeadingChannelWeight lambda x))
      (Ioi 0) := by
  have hbase :=
    integrableOn_pow_mul_thetaCuspGaussianApertureLeadingChannelWeight
      hlambda (2 * j)
  apply MeasureTheory.Integrable.mono hbase
  · exact Continuous.aestronglyMeasurable
      ((Real.continuous_exp.comp
          (continuous_const.mul
            ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub
              continuous_const))).mul
        ((continuous_id.pow (2 * j)).mul
          (continuous_iff_continuousAt.mpr fun x =>
            (hasDerivAt_thetaCuspGaussianApertureLeadingChannelWeight lambda x).continuousAt)))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hbase0 : 0 ≤
        x ^ (2 * j) * thetaCuspGaussianApertureLeadingChannelWeight lambda x := by
      exact mul_nonneg (pow_nonneg hx.le _) (Real.exp_nonneg _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg
        (thetaCuspHigherAtomExactHeightDamping_nonneg x) hbase0),
      abs_of_nonneg hbase0]
    exact mul_le_of_le_one_left hbase0
      (thetaCuspHigherAtomExactHeightDamping_le_one hx.le)

/-- Exact integrated half-saddle envelope. This turns the pointwise double-exponential
higher-atom damping into a height-localized moment estimate without invoking Laplace asymptotics. -/
theorem thetaCuspGaussianApertureLeadingChannelDampedMoment_le_halfSaddle
    {lambda s : ℝ} (hlambda : lambda ≤ 0) (hs : 0 < s) (j : ℕ) :
    thetaCuspGaussianApertureLeadingChannelDampedMoment lambda j ≤
      thetaCuspHigherAtomExactHeightDamping (s / 2) *
          thetaCuspGaussianApertureTailChannelMoment lambda 4 j +
        (2 / s ^ 4) *
          (∫ x : ℝ in Ioi 0,
            (x ^ 2 - s ^ 2) ^ 2 * x ^ (2 * j) *
              thetaCuspGaussianApertureLeadingChannelWeight lambda x) := by
  let base : ℝ → ℝ := fun x =>
    x ^ (2 * j) * thetaCuspGaussianApertureLeadingChannelWeight lambda x
  let err : ℝ → ℝ := fun x => (x ^ 2 - s ^ 2) ^ 2 * base x
  have hbase :=
    integrableOn_pow_mul_thetaCuspGaussianApertureLeadingChannelWeight
      hlambda (2 * j)
  have hm1 :=
    integrableOn_pow_mul_thetaCuspGaussianApertureLeadingChannelWeight
      hlambda (2 * (j + 1))
  have hm2 :=
    integrableOn_pow_mul_thetaCuspGaussianApertureLeadingChannelWeight
      hlambda (2 * (j + 2))
  have herr : IntegrableOn err (Ioi 0) := by
    have hcomb := (hm2.sub (hm1.const_mul (2 * s ^ 2))).add
      (hbase.const_mul (s ^ 4))
    apply hcomb.congr
    filter_upwards [] with x
    simp only [err, base, Pi.add_apply, Pi.sub_apply]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega,
      show 2 * (j + 2) = 2 * j + 4 by omega, pow_add, pow_add]
    ring
  have hdamped :=
    integrableOn_thetaCuspGaussianApertureLeadingChannelDampedMomentIntegrand
      hlambda j
  have hupper : IntegrableOn (fun x =>
      thetaCuspHigherAtomExactHeightDamping (s / 2) * base x +
        (2 / s ^ 4) * err x) (Ioi 0) :=
    (hbase.const_mul _).add (herr.const_mul _)
  have hmono :
      (∫ x : ℝ in Ioi 0,
        thetaCuspHigherAtomExactHeightDamping x * base x) ≤
        ∫ x : ℝ in Ioi 0,
          thetaCuspHigherAtomExactHeightDamping (s / 2) * base x +
            (2 / s ^ 4) * err x := by
    apply integral_mono_ae hdamped hupper
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hbase0 : 0 ≤ base x := by
      exact mul_nonneg (pow_nonneg hx.le _) (Real.exp_nonneg _)
    have henv :=
      thetaCuspHigherAtomExactHeightDamping_le_halfSaddle_add_error hs hx.le
    calc
      thetaCuspHigherAtomExactHeightDamping x *
          (x ^ (2 * j) * thetaCuspGaussianApertureLeadingChannelWeight lambda x) =
        thetaCuspHigherAtomExactHeightDamping x * base x := rfl
      _ ≤ (thetaCuspHigherAtomExactHeightDamping (s / 2) +
            (2 / s ^ 4) * (x ^ 2 - s ^ 2) ^ 2) * base x :=
        mul_le_mul_of_nonneg_right henv hbase0
      _ = thetaCuspHigherAtomExactHeightDamping (s / 2) * base x +
            (2 / s ^ 4) * err x := by
        simp only [err]
        ring
  calc
    thetaCuspGaussianApertureLeadingChannelDampedMoment lambda j =
        ∫ x : ℝ in Ioi 0,
          thetaCuspHigherAtomExactHeightDamping x * base x := by
      rfl
    _ ≤ ∫ x : ℝ in Ioi 0,
          thetaCuspHigherAtomExactHeightDamping (s / 2) * base x +
            (2 / s ^ 4) * err x := hmono
    _ = thetaCuspHigherAtomExactHeightDamping (s / 2) *
          thetaCuspGaussianApertureTailChannelMoment lambda 4 j +
        (2 / s ^ 4) *
          (∫ x : ℝ in Ioi 0,
            (x ^ 2 - s ^ 2) ^ 2 * x ^ (2 * j) *
              thetaCuspGaussianApertureLeadingChannelWeight lambda x) := by
      rw [integral_add (hbase.const_mul _) (herr.const_mul _),
        integral_const_mul, integral_const_mul,
        integral_pow_leadingChannelWeight_eq_moment]
      simp only [err, base]
      congr 1
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      ring

/-- The exact response-centered saddle turns the damped leading channel into a scaled contraction:
after multiplication by `3*pi*s^(4 : ℕ)`, the only nonsaddle contribution is two adjacent moments. -/
theorem thetaCuspGaussianApertureLeadingChannelDampedMoment_canonical_scaled_le
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    let s := thetaCuspGaussianApertureResponseCenteredSaddleHeight lambda hlambda j
    (3 * Real.pi) * s ^ 4 *
        thetaCuspGaussianApertureLeadingChannelDampedMoment lambda j ≤
      (3 * Real.pi) * s ^ 4 *
          thetaCuspHigherAtomExactHeightDamping (s / 2) *
            thetaCuspGaussianApertureTailChannelMoment lambda 4 j +
        2 * thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) := by
  dsimp only
  let s := thetaCuspGaussianApertureResponseCenteredSaddleHeight lambda hlambda j
  let E : ℝ := ∫ x : ℝ in Ioi 0,
    (x ^ 2 - s ^ 2) ^ 2 * x ^ (2 * j) *
      thetaCuspGaussianApertureLeadingChannelWeight lambda x
  have hs : 0 < s :=
    thetaCuspGaussianApertureResponseCenteredSaddleHeight_pos hlambda j
  have henv :=
    thetaCuspGaussianApertureLeadingChannelDampedMoment_le_halfSaddle
      hlambda hs j
  have hloc : (3 * Real.pi) * E ≤
      thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) := by
    simpa only [E, s] using
      thetaCuspGaussianApertureLeadingChannel_canonicalSaddleError_le hlambda j
  have hscale : 0 ≤ (3 * Real.pi) * s ^ 4 := by positivity
  have hs4ne : s ^ 4 ≠ 0 := (pow_pos hs 4).ne'
  calc
    (3 * Real.pi) * s ^ 4 *
        thetaCuspGaussianApertureLeadingChannelDampedMoment lambda j ≤
      (3 * Real.pi) * s ^ 4 *
        (thetaCuspHigherAtomExactHeightDamping (s / 2) *
            thetaCuspGaussianApertureTailChannelMoment lambda 4 j +
          (2 / s ^ 4) * E) := mul_le_mul_of_nonneg_left henv hscale
    _ = (3 * Real.pi) * s ^ 4 *
          thetaCuspHigherAtomExactHeightDamping (s / 2) *
            thetaCuspGaussianApertureTailChannelMoment lambda 4 j +
        2 * ((3 * Real.pi) * E) := by
      field_simp [hs4ne]
    _ ≤ (3 * Real.pi) * s ^ 4 *
          thetaCuspHigherAtomExactHeightDamping (s / 2) *
            thetaCuspGaussianApertureTailChannelMoment lambda 4 j +
        2 * thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) := by
      have htwo := mul_le_mul_of_nonneg_left hloc (show (0 : ℝ) ≤ 2 by norm_num)
      exact add_le_add_right htwo _

/-- The completed source with its first theta atom removed, under the physical Gaussian aperture. -/
def thetaCuspGaussianApertureHigherAtomHalfMoment
    (lambda : ℝ) (j : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0,
    x ^ (2 * j) * Real.exp (lambda * x ^ 2) *
      (thetaCuspFullSource x - thetaCuspSourceTerm x 1)

theorem integrableOn_thetaCuspGaussianApertureHigherAtomHalfMomentIntegrand
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    IntegrableOn (fun x : ℝ =>
      x ^ (2 * j) * Real.exp (lambda * x ^ 2) *
        (thetaCuspFullSource x - thetaCuspSourceTerm x 1)) (Ioi 0) := by
  have hfull := integrableOn_thetaCuspGaussianApertureMomentIntegrand hlambda j
  have h4 := integrableOn_thetaCuspGaussianApertureTailChannelMomentIntegrand
    hlambda 4 j
  have h2 := integrableOn_thetaCuspGaussianApertureTailChannelMomentIntegrand
    hlambda 2 j
  have hfirst : IntegrableOn (fun x : ℝ =>
      x ^ (2 * j) * Real.exp (lambda * x ^ 2) *
        thetaCuspSourceTerm x 1) (Ioi 0) := by
    have hcomb := (h4.const_mul (4 * Real.pi ^ 2)).sub
      (h2.const_mul (6 * Real.pi))
    apply hcomb.congr
    filter_upwards [] with x
    simp only [Pi.sub_apply]
    rw [thetaCuspSourceTerm_one_eq_tailChannelDifference]
    ring
  apply (hfull.sub hfirst).congr
  filter_upwards [] with x
  simp only [thetaCuspGaussianApertureDensity, Pi.sub_apply]
  ring

/-- The complete infinite higher-atom aperture tail is bounded by the damped positive leading
channel. This integrates the exact atomwise separation without a graph-saturation constant. -/
theorem thetaCuspGaussianApertureHigherAtomHalfMoment_le_dampedLeading
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureHigherAtomHalfMoment lambda j ≤
      (32 * Real.pi ^ 2 / 2997) *
        thetaCuspGaussianApertureLeadingChannelDampedMoment lambda j := by
  have htail :=
    integrableOn_thetaCuspGaussianApertureHigherAtomHalfMomentIntegrand hlambda j
  have hdamped :=
    integrableOn_thetaCuspGaussianApertureLeadingChannelDampedMomentIntegrand
      hlambda j
  rw [thetaCuspGaussianApertureHigherAtomHalfMoment,
    thetaCuspGaussianApertureLeadingChannelDampedMoment,
    ← integral_const_mul]
  apply integral_mono_ae htail (hdamped.const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  let q : ℝ := x ^ (2 * j) * Real.exp (lambda * x ^ 2)
  have hq : 0 ≤ q := by
    dsimp only [q]
    exact mul_nonneg (pow_nonneg hx.le _) (Real.exp_nonneg _)
  have htailPoint := thetaCuspFullSource_sub_first_le_exactHeight_rational hx.le
  have hfirst := thetaCuspSourceTerm_one_le_four_pi_sq_mul_leadingChannel x
  have hfactor : 0 ≤ (8 / 2997 : ℝ) *
      thetaCuspHigherAtomExactHeightDamping x :=
    mul_nonneg (by norm_num)
      (thetaCuspHigherAtomExactHeightDamping_nonneg x)
  calc
    x ^ (2 * j) * Real.exp (lambda * x ^ 2) *
        (thetaCuspFullSource x - thetaCuspSourceTerm x 1) =
      q * (thetaCuspFullSource x - thetaCuspSourceTerm x 1) := rfl
    _ ≤ q * ((8 / 2997 : ℝ) * thetaCuspHigherAtomExactHeightDamping x *
          thetaCuspSourceTerm x 1) :=
      mul_le_mul_of_nonneg_left htailPoint hq
    _ ≤ q * ((8 / 2997 : ℝ) * thetaCuspHigherAtomExactHeightDamping x *
          (4 * Real.pi ^ 2 * thetaCuspPolynomialAtom (X ^ 4) 1 x)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hfirst hfactor) hq
    _ = (32 * Real.pi ^ 2 / 2997) *
        (thetaCuspHigherAtomExactHeightDamping x *
          (x ^ (2 * j) *
            thetaCuspGaussianApertureLeadingChannelWeight lambda x)) := by
      rw [thetaCuspGaussianApertureLeadingChannelWeight_eq]
      dsimp only [q]
      ring

/-- **Source-derived height-localized infinite contraction.** At the canonical response saddle,
the entire completed higher-atom tail is controlled by a double-exponential half-saddle term and
one adjacent leading-channel moment. No uniform HT graph bound or unresolved saddle asymptotic is
used. -/
theorem thetaCuspGaussianApertureHigherAtomHalfMoment_canonical_scaled_le
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    let s := thetaCuspGaussianApertureResponseCenteredSaddleHeight lambda hlambda j
    (3 * Real.pi) * s ^ 4 *
        thetaCuspGaussianApertureHigherAtomHalfMoment lambda j ≤
      (32 * Real.pi ^ 2 / 2997) *
        ((3 * Real.pi) * s ^ 4 *
            thetaCuspHigherAtomExactHeightDamping (s / 2) *
              thetaCuspGaussianApertureTailChannelMoment lambda 4 j +
          2 * thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1)) := by
  dsimp only
  let s := thetaCuspGaussianApertureResponseCenteredSaddleHeight lambda hlambda j
  have htail :=
    thetaCuspGaussianApertureHigherAtomHalfMoment_le_dampedLeading hlambda j
  have hdamped :=
    thetaCuspGaussianApertureLeadingChannelDampedMoment_canonical_scaled_le
      hlambda j
  have hscale : 0 ≤ (3 * Real.pi) * s ^ 4 := by positivity
  have hconst : 0 ≤ (32 * Real.pi ^ 2 / 2997 : ℝ) := by positivity
  calc
    (3 * Real.pi) * s ^ 4 *
        thetaCuspGaussianApertureHigherAtomHalfMoment lambda j ≤
      (3 * Real.pi) * s ^ 4 *
        ((32 * Real.pi ^ 2 / 2997) *
          thetaCuspGaussianApertureLeadingChannelDampedMoment lambda j) :=
      mul_le_mul_of_nonneg_left htail hscale
    _ = (32 * Real.pi ^ 2 / 2997) *
        ((3 * Real.pi) * s ^ 4 *
          thetaCuspGaussianApertureLeadingChannelDampedMoment lambda j) := by ring
    _ ≤ (32 * Real.pi ^ 2 / 2997) *
        ((3 * Real.pi) * s ^ 4 *
            thetaCuspHigherAtomExactHeightDamping (s / 2) *
              thetaCuspGaussianApertureTailChannelMoment lambda 4 j +
          2 * thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1)) :=
      mul_le_mul_of_nonneg_left hdamped hconst

/-- The signed `p=2` correction never removes half of the positive `p=4` channel. This is the
uniform resolution floor needed to compare the infinite tail with the literal first atom. -/
theorem one_half_lt_thetaCuspGaussianApertureTailAmplitudeFactor
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    (1 / 2 : ℝ) < thetaCuspGaussianApertureTailAmplitudeFactor lambda j := by
  have hratio0 :=
    thetaCuspGaussianApertureTailCorrectionRatio_nonneg hlambda j
  have hratio1 :=
    thetaCuspGaussianApertureTailCorrectionRatio_le_one hlambda j
  have hcoeff0 : 0 ≤ (3 / (2 * Real.pi) : ℝ) := by positivity
  have hcoeff : (3 / (2 * Real.pi) : ℝ) < 1 / 2 := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith [Real.pi_gt_three]
  have hmul : (3 / (2 * Real.pi) : ℝ) *
      thetaCuspGaussianApertureTailCorrectionRatio lambda j ≤
        3 / (2 * Real.pi) :=
    mul_le_of_le_one_right hcoeff0 hratio1
  rw [thetaCuspGaussianApertureTailAmplitudeFactor]
  linarith

/-- Literal first-atom mass retains at least `2*pi^(2 : ℕ)` times the positive leading-channel mass. -/
theorem two_pi_sq_mul_leadingChannelMoment_lt_firstAtomHalfMoment
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    2 * Real.pi ^ 2 *
        thetaCuspGaussianApertureTailChannelMoment lambda 4 j <
      thetaCuspGaussianApertureFirstAtomHalfMoment lambda j := by
  rw [thetaCuspGaussianApertureFirstAtomHalfMoment_eq_leading_mul_amplitude
    hlambda]
  have hmass := thetaCuspGaussianApertureTailChannelMoment_pos hlambda 4 j
  have hamp := one_half_lt_thetaCuspGaussianApertureTailAmplitudeFactor
    hlambda j
  have hscale : 0 < 4 * Real.pi ^ 2 *
      thetaCuspGaussianApertureTailChannelMoment lambda 4 j := by positivity
  have hmul := mul_lt_mul_of_pos_left hamp hscale
  nlinarith

/-- **Resolution-safe height-localized infinite contraction.** The higher-atom tail is now
measured directly against the literal signed first atom. The `p=2` resolution loss has disappeared
into the sharp uniform half-amplitude floor, leaving rational constants `16/2997` and `32/2997`. -/
theorem thetaCuspGaussianApertureHigherAtomHalfMoment_canonical_scaled_le_firstAtom
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    let s := thetaCuspGaussianApertureResponseCenteredSaddleHeight lambda hlambda j
    (3 * Real.pi) * s ^ 4 *
        thetaCuspGaussianApertureHigherAtomHalfMoment lambda j ≤
      (16 / 2997 : ℝ) * (3 * Real.pi) * s ^ 4 *
          thetaCuspHigherAtomExactHeightDamping (s / 2) *
            thetaCuspGaussianApertureFirstAtomHalfMoment lambda j +
        (32 / 2997 : ℝ) *
          thetaCuspGaussianApertureFirstAtomHalfMoment lambda (j + 1) := by
  dsimp only
  let s := thetaCuspGaussianApertureResponseCenteredSaddleHeight lambda hlambda j
  let scale : ℝ := (3 * Real.pi) * s ^ 4
  let damp : ℝ := thetaCuspHigherAtomExactHeightDamping (s / 2)
  let C0 := thetaCuspGaussianApertureTailChannelMoment lambda 4 j
  let C1 := thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1)
  let F0 := thetaCuspGaussianApertureFirstAtomHalfMoment lambda j
  let F1 := thetaCuspGaussianApertureFirstAtomHalfMoment lambda (j + 1)
  have htail :=
    thetaCuspGaussianApertureHigherAtomHalfMoment_canonical_scaled_le
      hlambda j
  have hF0 : 2 * Real.pi ^ 2 * C0 ≤ F0 := by
    exact (two_pi_sq_mul_leadingChannelMoment_lt_firstAtomHalfMoment
      hlambda j).le
  have hF1 : 2 * Real.pi ^ 2 * C1 ≤ F1 := by
    exact (two_pi_sq_mul_leadingChannelMoment_lt_firstAtomHalfMoment
      hlambda (j + 1)).le
  have hscale : 0 ≤ scale := by
    dsimp only [scale, s]
    positivity
  have hdamp : 0 ≤ damp := by
    exact thetaCuspHigherAtomExactHeightDamping_nonneg _
  have hterm0 :
      (32 * Real.pi ^ 2 / 2997) * (scale * damp * C0) ≤
        (16 / 2997 : ℝ) * scale * damp * F0 := by
    have hmul := mul_le_mul_of_nonneg_left hF0
      (mul_nonneg
        (mul_nonneg (show (0 : ℝ) ≤ 16 / 2997 by norm_num) hscale) hdamp)
    nlinarith
  have hterm1 :
      (32 * Real.pi ^ 2 / 2997) * (2 * C1) ≤
        (32 / 2997 : ℝ) * F1 := by
    have hmul := mul_le_mul_of_nonneg_left hF1 (by norm_num : (0 : ℝ) ≤ 32 / 2997)
    nlinarith
  calc
    scale * thetaCuspGaussianApertureHigherAtomHalfMoment lambda j ≤
      (32 * Real.pi ^ 2 / 2997) * (scale * damp * C0 + 2 * C1) := by
      simpa only [scale, damp, C0, C1, s] using htail
    _ = (32 * Real.pi ^ 2 / 2997) * (scale * damp * C0) +
        (32 * Real.pi ^ 2 / 2997) * (2 * C1) := by ring
    _ ≤ (16 / 2997 : ℝ) * scale * damp * F0 +
        (32 / 2997 : ℝ) * F1 := add_le_add hterm0 hterm1
    _ = (16 / 2997 : ℝ) * (3 * Real.pi) * s ^ 4 *
          thetaCuspHigherAtomExactHeightDamping (s / 2) *
          thetaCuspGaussianApertureFirstAtomHalfMoment lambda j +
        (32 / 2997 : ℝ) *
          thetaCuspGaussianApertureFirstAtomHalfMoment lambda (j + 1) := by
      dsimp only [scale, damp, F0, F1]
      ring

/-- Cauchy--Schwarz converts the unnormalized response-saddle error into control of the
displacement of the adjacent leading moment from the squared saddle height. -/
theorem thetaCuspGaussianApertureLeadingChannel_centeredMomentError_sq_le
    {lambda s : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    (thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) -
        s ^ 2 * thetaCuspGaussianApertureTailChannelMoment lambda 4 j) ^ 2 ≤
      thetaCuspGaussianApertureTailChannelMoment lambda 4 j *
        (∫ x : ℝ in Ioi 0,
          (x ^ 2 - s ^ 2) ^ 2 * x ^ (2 * j) *
            thetaCuspGaussianApertureLeadingChannelWeight lambda x) := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let base : ℝ → ℝ := fun x =>
    x ^ (2 * j) * thetaCuspGaussianApertureLeadingChannelWeight lambda x
  let f : ℝ → ℝ := fun x => (x ^ 2 - s ^ 2) * Real.sqrt (base x)
  let g : ℝ → ℝ := fun x => Real.sqrt (base x)
  have hbaseInt :=
    integrableOn_pow_mul_thetaCuspGaussianApertureLeadingChannelWeight
      hlambda (2 * j)
  have hm1 :=
    integrableOn_pow_mul_thetaCuspGaussianApertureLeadingChannelWeight
      hlambda (2 * (j + 1))
  have hm2 :=
    integrableOn_pow_mul_thetaCuspGaussianApertureLeadingChannelWeight
      hlambda (2 * (j + 2))
  have hbase0 : ∀ᵐ x : ℝ ∂mu, 0 ≤ base x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (pow_nonneg hx.le _) (Real.exp_nonneg _)
  have hbaseCont : Continuous base := by
    exact (continuous_id.pow _).mul
      (continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_thetaCuspGaussianApertureLeadingChannelWeight lambda x).continuousAt)
  have hfmeas : AEStronglyMeasurable f mu := by
    exact Continuous.aestronglyMeasurable
      (((continuous_id.pow 2).sub continuous_const).mul
        (Real.continuous_sqrt.comp hbaseCont))
  have hgmeas : AEStronglyMeasurable g mu := by
    exact Continuous.aestronglyMeasurable (Real.continuous_sqrt.comp hbaseCont)
  have herr : IntegrableOn (fun x : ℝ =>
      (x ^ 2 - s ^ 2) ^ 2 * base x) (Ioi 0) := by
    have hcomb := (hm2.sub (hm1.const_mul (2 * s ^ 2))).add
      (hbaseInt.const_mul (s ^ 4))
    apply hcomb.congr
    filter_upwards [] with x
    simp only [base, Pi.add_apply, Pi.sub_apply]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega,
      show 2 * (j + 2) = 2 * j + 4 by omega, pow_add, pow_add]
    ring
  have hfSq : Integrable (fun x => f x ^ 2) mu := by
    apply herr.congr
    filter_upwards [hbase0] with x hx
    simp only [f, mul_pow, Real.sq_sqrt hx]
  have hgSq : Integrable (fun x => g x ^ 2) mu := by
    apply hbaseInt.congr
    filter_upwards [hbase0] with x hx
    simp only [g, Real.sq_sqrt hx, base]
  have hcs := HTGeometry.sq_integral_mul_le_integral_sq_mul_integral_sq
    hfmeas hgmeas hfSq hgSq
  have hfg : (∫ x, f x * g x ∂mu) =
      thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) -
        s ^ 2 * thetaCuspGaussianApertureTailChannelMoment lambda 4 j := by
    have hshift : IntegrableOn (fun x : ℝ => x ^ 2 * base x) (Ioi 0) := by
      apply hm1.congr
      filter_upwards [] with x
      simp only [base]
      rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
      ring
    have hshiftValue : (∫ x : ℝ in Ioi 0, x ^ 2 * base x) =
        thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) := by
      rw [← integral_pow_leadingChannelWeight_eq_moment lambda (j + 1)]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [base]
      rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
      ring
    have hbaseValue : (∫ x : ℝ in Ioi 0, base x) =
        thetaCuspGaussianApertureTailChannelMoment lambda 4 j := by
      simpa only [base] using integral_pow_leadingChannelWeight_eq_moment lambda j
    calc
      (∫ x, f x * g x ∂mu) =
          ∫ x : ℝ in Ioi 0, (x ^ 2 - s ^ 2) * base x := by
        apply integral_congr_ae
        filter_upwards [hbase0] with x hx
        simp only [f, g]
        rw [show (x ^ 2 - s ^ 2) * Real.sqrt (base x) * Real.sqrt (base x) =
          (x ^ 2 - s ^ 2) * Real.sqrt (base x) ^ 2 by ring,
          Real.sq_sqrt hx]
      _ = (∫ x : ℝ in Ioi 0, x ^ 2 * base x) -
          s ^ 2 * (∫ x : ℝ in Ioi 0, base x) := by
        rw [← integral_const_mul,
          ← integral_sub hshift (hbaseInt.const_mul (s ^ 2))]
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) -
          s ^ 2 * thetaCuspGaussianApertureTailChannelMoment lambda 4 j := by
        rw [hshiftValue, hbaseValue]
  have hf2 : (∫ x, f x ^ 2 ∂mu) =
      ∫ x : ℝ in Ioi 0,
        (x ^ 2 - s ^ 2) ^ 2 * x ^ (2 * j) *
          thetaCuspGaussianApertureLeadingChannelWeight lambda x := by
    apply integral_congr_ae
    filter_upwards [hbase0] with x hx
    simp only [f, base, mul_pow, Real.sq_sqrt hx]
    ring
  have hg2 : (∫ x, g x ^ 2 ∂mu) =
      thetaCuspGaussianApertureTailChannelMoment lambda 4 j := by
    rw [← integral_pow_leadingChannelWeight_eq_moment lambda j]
    apply integral_congr_ae
    filter_upwards [hbase0] with x hx
    simp only [g, base, Real.sq_sqrt hx]
  rw [hfg, hf2, hg2] at hcs
  simpa only [mul_comm] using hcs

/-- At the exact response center, the adjacent leading moment is at most `2*s^(2 : ℕ)+1` times the
current mass. This is the quantitative conversion from score concentration to moment scale. -/
theorem thetaCuspGaussianApertureTailChannelMoment_succ_le_canonicalScale
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    let s := thetaCuspGaussianApertureResponseCenteredSaddleHeight lambda hlambda j
    thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) ≤
      (2 * s ^ 2 + 1) * thetaCuspGaussianApertureTailChannelMoment lambda 4 j := by
  dsimp only
  let s := thetaCuspGaussianApertureResponseCenteredSaddleHeight lambda hlambda j
  let C0 := thetaCuspGaussianApertureTailChannelMoment lambda 4 j
  let C1 := thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1)
  let E : ℝ := ∫ x : ℝ in Ioi 0,
    (x ^ 2 - s ^ 2) ^ 2 * x ^ (2 * j) *
      thetaCuspGaussianApertureLeadingChannelWeight lambda x
  have hs : 0 < s :=
    thetaCuspGaussianApertureResponseCenteredSaddleHeight_pos hlambda j
  have hC0 : 0 < C0 :=
    thetaCuspGaussianApertureTailChannelMoment_pos hlambda 4 j
  have hC1 : 0 < C1 :=
    thetaCuspGaussianApertureTailChannelMoment_pos hlambda 4 (j + 1)
  have hmean : (C1 - s ^ 2 * C0) ^ 2 ≤ C0 * E := by
    simpa only [C0, C1, E, s] using
      thetaCuspGaussianApertureLeadingChannel_centeredMomentError_sq_le
        hlambda j
  have hloc : (3 * Real.pi) * E ≤ C1 := by
    simpa only [E, C1, s] using
      thetaCuspGaussianApertureLeadingChannel_canonicalSaddleError_le hlambda j
  have hscore : (3 * Real.pi) * (C1 - s ^ 2 * C0) ^ 2 ≤ C0 * C1 := by
    calc
      (3 * Real.pi) * (C1 - s ^ 2 * C0) ^ 2 ≤
          (3 * Real.pi) * (C0 * E) :=
        mul_le_mul_of_nonneg_left hmean (by positivity)
      _ = C0 * ((3 * Real.pi) * E) := by ring
      _ ≤ C0 * C1 := mul_le_mul_of_nonneg_left hloc hC0.le
  by_contra hnot
  have hbig : (2 * s ^ 2 + 1) * C0 < C1 := lt_of_not_ge hnot
  have hC0C1 : C0 < C1 := by
    have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
    nlinarith
  have hdpos : 0 < C1 - s ^ 2 * C0 := by nlinarith
  have hhalf : C1 / 2 < C1 - s ^ 2 * C0 := by nlinarith
  have hsq : (C1 / 2) ^ 2 < (C1 - s ^ 2 * C0) ^ 2 :=
    (sq_lt_sq₀ (by positivity) hdpos.le).2 hhalf
  have hpi : (9 : ℝ) < 3 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hstrict : 9 * (C1 - s ^ 2 * C0) ^ 2 < C0 * C1 := by
    exact (mul_lt_mul_of_pos_right hpi (sq_pos_of_pos hdpos)).trans_le hscore
  nlinarith [mul_pos hC0 hC1, mul_pos hC1 hC1]

theorem thetaCuspGaussianApertureFirstAtomHalfMoment_succ_le_canonicalScale
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    let s := thetaCuspGaussianApertureResponseCenteredSaddleHeight lambda hlambda j
    thetaCuspGaussianApertureFirstAtomHalfMoment lambda (j + 1) ≤
      2 * (2 * s ^ 2 + 1) *
        thetaCuspGaussianApertureFirstAtomHalfMoment lambda j := by
  dsimp only
  let s := thetaCuspGaussianApertureResponseCenteredSaddleHeight lambda hlambda j
  let C0 := thetaCuspGaussianApertureTailChannelMoment lambda 4 j
  let C1 := thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1)
  let F0 := thetaCuspGaussianApertureFirstAtomHalfMoment lambda j
  let F1 := thetaCuspGaussianApertureFirstAtomHalfMoment lambda (j + 1)
  have hC := thetaCuspGaussianApertureTailChannelMoment_succ_le_canonicalScale
    hlambda j
  have hfactor1 : thetaCuspGaussianApertureTailAmplitudeFactor lambda (j + 1) ≤ 1 := by
    have hnonneg := thetaCuspGaussianApertureTailCorrectionRatio_nonneg hlambda (j + 1)
    have hcoeff : 0 ≤ (3 / (2 * Real.pi) : ℝ) := by positivity
    rw [thetaCuspGaussianApertureTailAmplitudeFactor]
    nlinarith [mul_nonneg hcoeff hnonneg]
  have hF1 : F1 ≤ 4 * Real.pi ^ 2 * C1 := by
    dsimp only [F1, C1]
    rw [thetaCuspGaussianApertureFirstAtomHalfMoment_eq_leading_mul_amplitude
      hlambda]
    exact mul_le_of_le_one_right
      (mul_nonneg (by positivity)
        (thetaCuspGaussianApertureTailChannelMoment_pos hlambda 4 (j + 1)).le)
      hfactor1
  have hF0 : 2 * Real.pi ^ 2 * C0 ≤ F0 :=
    (two_pi_sq_mul_leadingChannelMoment_lt_firstAtomHalfMoment hlambda j).le
  have hscale0 : 0 ≤ 4 * Real.pi ^ 2 := by positivity
  have hscaleS : 0 ≤ 2 * (2 * s ^ 2 + 1) := by positivity
  calc
    F1 ≤ 4 * Real.pi ^ 2 * C1 := hF1
    _ ≤ 4 * Real.pi ^ 2 * ((2 * s ^ 2 + 1) * C0) :=
      mul_le_mul_of_nonneg_left hC hscale0
    _ = 2 * (2 * s ^ 2 + 1) * (2 * Real.pi ^ 2 * C0) := by ring
    _ ≤ 2 * (2 * s ^ 2 + 1) * F0 :=
      mul_le_mul_of_nonneg_left hF0 hscaleS

/-- **Strict source-side infinite contraction.** Once the canonical response saddle has height at
least one, the complete `n>=2` aperture tail is less than `1/80` of the literal signed first atom. -/
theorem thetaCuspGaussianApertureHigherAtomHalfMoment_lt_firstAtom_div_eighty
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ)
    (hsone : 1 ≤
      thetaCuspGaussianApertureResponseCenteredSaddleHeight lambda hlambda j) :
    thetaCuspGaussianApertureHigherAtomHalfMoment lambda j <
      thetaCuspGaussianApertureFirstAtomHalfMoment lambda j / 80 := by
  let s := thetaCuspGaussianApertureResponseCenteredSaddleHeight lambda hlambda j
  let scale : ℝ := (3 * Real.pi) * s ^ 4
  let damp : ℝ := thetaCuspHigherAtomExactHeightDamping (s / 2)
  let H := thetaCuspGaussianApertureHigherAtomHalfMoment lambda j
  let F0 := thetaCuspGaussianApertureFirstAtomHalfMoment lambda j
  let F1 := thetaCuspGaussianApertureFirstAtomHalfMoment lambda (j + 1)
  have hs : 0 < s :=
    thetaCuspGaussianApertureResponseCenteredSaddleHeight_pos hlambda j
  have htail :=
    thetaCuspGaussianApertureHigherAtomHalfMoment_canonical_scaled_le_firstAtom
      hlambda j
  have hsucc :=
    thetaCuspGaussianApertureFirstAtomHalfMoment_succ_le_canonicalScale
      hlambda j
  have hdamp : damp ≤ 1 := by
    exact thetaCuspHigherAtomExactHeightDamping_le_one (by dsimp only [s]; linarith)
  have hF0 : 0 < F0 :=
    thetaCuspGaussianApertureFirstAtomHalfMoment_pos hlambda j
  have hscale : 0 < scale := by
    dsimp only [scale]
    positivity
  have hsquad : 2 * s ^ 2 + 1 ≤ 3 * s ^ 4 := by
    have hs2 : 1 ≤ s ^ 2 := by nlinarith [sq_nonneg (s - 1)]
    have hs4 : s ^ 2 ≤ s ^ 4 := by
      nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs2)]
    nlinarith
  have hcoeff :
      (16 / 2997 : ℝ) * scale +
          (64 / 2997 : ℝ) * (2 * s ^ 2 + 1) < scale / 80 := by
    have hpis4 : 3 * s ^ 4 < Real.pi * s ^ 4 :=
      mul_lt_mul_of_pos_right Real.pi_gt_three (pow_pos hs 4)
    dsimp only [scale]
    nlinarith
  have hscaled : scale * H < scale * (F0 / 80) := by
    calc
      scale * H ≤
          (16 / 2997 : ℝ) * scale * damp * F0 +
            (32 / 2997 : ℝ) * F1 := by
        dsimp only [scale, damp, H, F0, F1, s]
        convert htail using 1
        all_goals ring
      _ ≤ (16 / 2997 : ℝ) * scale * F0 +
            (32 / 2997 : ℝ) *
              (2 * (2 * s ^ 2 + 1) * F0) := by
        have hdampedTerm :
            (16 / 2997 : ℝ) * scale * damp ≤
              (16 / 2997 : ℝ) * scale := by
          simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left hdamp
              (mul_nonneg (show (0 : ℝ) ≤ 16 / 2997 by norm_num) hscale.le))
        exact add_le_add
          (mul_le_mul_of_nonneg_right
            hdampedTerm hF0.le)
          (mul_le_mul_of_nonneg_left hsucc
            (show (0 : ℝ) ≤ 32 / 2997 by norm_num))
      _ = ((16 / 2997 : ℝ) * scale +
            (64 / 2997 : ℝ) * (2 * s ^ 2 + 1)) * F0 := by ring
      _ < (scale / 80) * F0 := mul_lt_mul_of_pos_right hcoeff hF0
      _ = scale * (F0 / 80) := by ring
  exact lt_of_mul_lt_mul_left hscaled hscale.le

end

end RHTower
