import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspReflectedLikelihoodInterferenceFactorization

/-!
# Reflected likelihood cumulant obstruction

The higher theta tail is already represented by one fixed positive Laplace measure.  Its tilted
mean, variance, and third cumulant give the literal first three jets of the likelihood partition
in the logarithmic source coordinate.  These jets isolate the exact non-diagonal correction to
the strictly positive first-atom reflected Riccati margin.
-/

open MeasureTheory Set Filter

namespace RHTower

noncomputable section

/-- Every tilted likelihood moment differentiates to minus its successor. -/
theorem hasDerivAt_thetaCuspHigherLikelihoodSpectralMoment
    (m : ℕ) {B : ℝ} (hB : 0 < B) :
    HasDerivAt (fun q => thetaCuspHigherLikelihoodSpectralMoment q m)
      (-thetaCuspHigherLikelihoodSpectralMoment B (m + 1)) B := by
  let s : Set ℝ := Metric.ball B (B / 2)
  let bound : ℝ → ℝ := fun t =>
    t ^ (m + 1) * Real.exp (-(B / 2) * t)
  have hs : s ∈ nhds B := Metric.ball_mem_nhds B (half_pos hB)
  have hpositive : ∀ z ∈ s, B / 2 < z := by
    intro z hz
    have habs : |z - B| < B / 2 := by
      simpa [s, Real.dist_eq] using hz
    have hneg : -(B / 2) < z - B := neg_lt_of_abs_lt habs
    linarith
  have hFmeas : ∀ᶠ z in nhds B,
      AEStronglyMeasurable
        (fun t : ℝ => t ^ m * Real.exp (-z * t))
        thetaCuspHigherLikelihoodSpectralMeasure := by
    filter_upwards with z
    exact (by fun_prop : Continuous
      (fun t : ℝ => t ^ m * Real.exp (-z * t))).aestronglyMeasurable
  have hF'meas :
      AEStronglyMeasurable
        (fun t : ℝ => -(t ^ (m + 1)) * Real.exp (-B * t))
        thetaCuspHigherLikelihoodSpectralMeasure :=
    (by fun_prop : Continuous
      (fun t : ℝ => -(t ^ (m + 1)) * Real.exp (-B * t))).aestronglyMeasurable
  have hboundInt : Integrable bound thetaCuspHigherLikelihoodSpectralMeasure := by
    simpa [bound] using
      integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure
        (m + 1) (half_pos hB)
  have hdom : ∀ᵐ t ∂thetaCuspHigherLikelihoodSpectralMeasure,
      ∀ z ∈ s,
        ‖-(t ^ (m + 1)) * Real.exp (-z * t)‖ ≤ bound t := by
    filter_upwards
      [ae_nonneg_thetaCuspHigherLikelihoodSpectralMeasure] with t ht
    intro z hz
    have hzLower := hpositive z hz
    have hexp : Real.exp (-z * t) ≤ Real.exp (-(B / 2) * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    rw [Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_nonneg (pow_nonneg ht _), abs_of_pos (Real.exp_pos _)]
    dsimp [bound]
    exact mul_le_mul_of_nonneg_left hexp (pow_nonneg ht _)
  have hdiff : ∀ᵐ t ∂thetaCuspHigherLikelihoodSpectralMeasure,
      ∀ z ∈ s,
        HasDerivAt (fun q : ℝ => t ^ m * Real.exp (-q * t))
          (-(t ^ (m + 1)) * Real.exp (-z * t)) z := by
    filter_upwards with t z hz
    have hinner : HasDerivAt (fun q : ℝ => -q * t) (-t) z := by
      simpa using (hasDerivAt_id z).neg.mul_const t
    have hexp : HasDerivAt (fun q : ℝ => Real.exp (-q * t))
        (-t * Real.exp (-z * t)) z := by
      simpa [Function.comp_def, mul_comm] using
        (Real.hasDerivAt_exp (-z * t)).comp z hinner
    have hmul := (hasDerivAt_const z (t ^ m)).mul hexp
    exact hmul.congr_deriv (by rw [pow_succ]; ring)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := thetaCuspHigherLikelihoodSpectralMeasure)
    (F := fun z t : ℝ => t ^ m * Real.exp (-z * t))
    (F' := fun z t : ℝ => -(t ^ (m + 1)) * Real.exp (-z * t))
    (bound := bound) hs hFmeas
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure m hB)
    hF'meas hdom hboundInt hdiff
  have hfun : (fun q => thetaCuspHigherLikelihoodSpectralMoment q m) = fun n =>
      ∫ (a : ℝ), a ^ m * Real.exp (-n * a)
        ∂thetaCuspHigherLikelihoodSpectralMeasure := by
    funext q
    exact thetaCuspHigherLikelihoodSpectralMoment_eq_integral q m
  rw [hfun]
  exact hmain.2.congr_deriv (by
    rw [thetaCuspHigherLikelihoodSpectralMoment_eq_integral, ← integral_neg]
    apply integral_congr_ae
    filter_upwards with t
    ring)

/-- Mean of the total likelihood state, including the first-atom mass at spectral coordinate
zero. -/
def thetaCuspLikelihoodMean (B : ℝ) : ℝ :=
  thetaCuspHigherLikelihoodSpectralMoment B 1 /
    thetaCuspLikelihoodPartition B

/-- Variance of the total likelihood state. -/
def thetaCuspLikelihoodVariance (B : ℝ) : ℝ :=
  thetaCuspHigherLikelihoodSpectralMoment B 2 /
      thetaCuspLikelihoodPartition B -
    thetaCuspLikelihoodMean B ^ (2 : ℕ)

/-- Third cumulant of the total likelihood state. -/
def thetaCuspLikelihoodThirdCumulant (B : ℝ) : ℝ :=
  thetaCuspHigherLikelihoodSpectralMoment B 3 /
      thetaCuspLikelihoodPartition B -
    3 * thetaCuspLikelihoodMean B *
      (thetaCuspHigherLikelihoodSpectralMoment B 2 /
        thetaCuspLikelihoodPartition B) +
    2 * thetaCuspLikelihoodMean B ^ (3 : ℕ)

theorem hasDerivAt_thetaCuspLikelihoodPartition
    {B : ℝ} (hB : 0 < B) :
    HasDerivAt thetaCuspLikelihoodPartition
      (-thetaCuspHigherLikelihoodSpectralMoment B 1) B := by
  unfold thetaCuspLikelihoodPartition
  exact (hasDerivAt_thetaCuspHigherLikelihoodSpectralResponse hB).const_add 1

theorem hasDerivAt_thetaCuspLikelihoodMean
    {B : ℝ} (hB : 0 < B) :
    HasDerivAt thetaCuspLikelihoodMean
      (-thetaCuspLikelihoodVariance B) B := by
  have hpart := hasDerivAt_thetaCuspLikelihoodPartition hB
  have hpartPos := thetaCuspLikelihoodPartition_pos hB
  have hmOne :=
    hasDerivAt_thetaCuspHigherLikelihoodSpectralMoment 1 hB
  exact (hmOne.div hpart hpartPos.ne').congr_deriv (by
    norm_num
    unfold thetaCuspLikelihoodVariance thetaCuspLikelihoodMean
    field_simp [hpartPos.ne']
    ring)

theorem hasDerivAt_thetaCuspLikelihoodVariance
    {B : ℝ} (hB : 0 < B) :
    HasDerivAt thetaCuspLikelihoodVariance
      (-thetaCuspLikelihoodThirdCumulant B) B := by
  have hpart := hasDerivAt_thetaCuspLikelihoodPartition hB
  have hpartPos := thetaCuspLikelihoodPartition_pos hB
  have hmTwo :=
    hasDerivAt_thetaCuspHigherLikelihoodSpectralMoment 2 hB
  have hmean := hasDerivAt_thetaCuspLikelihoodMean hB
  exact ((hmTwo.div hpart hpartPos.ne').sub (hmean.pow 2)).congr_deriv (by
    norm_num
    unfold thetaCuspLikelihoodThirdCumulant thetaCuspLikelihoodVariance
      thetaCuspLikelihoodMean
    field_simp [hpartPos.ne']
    ring)

/-- First logarithmic partition jet in likelihood temperature. -/
def thetaCuspLikelihoodLogPartitionJetOne (B : ℝ) : ℝ :=
  -thetaCuspLikelihoodMean B

/-- Second logarithmic partition jet in likelihood temperature. -/
def thetaCuspLikelihoodLogPartitionJetTwo (B : ℝ) : ℝ :=
  thetaCuspLikelihoodVariance B

/-- Third logarithmic partition jet in likelihood temperature. -/
def thetaCuspLikelihoodLogPartitionJetThree (B : ℝ) : ℝ :=
  -thetaCuspLikelihoodThirdCumulant B

theorem hasDerivAt_log_thetaCuspLikelihoodPartition_cumulant
    {B : ℝ} (hB : 0 < B) :
    HasDerivAt (fun q => Real.log (thetaCuspLikelihoodPartition q))
      (thetaCuspLikelihoodLogPartitionJetOne B) B := by
  simpa only [thetaCuspLikelihoodLogPartitionJetOne,
    thetaCuspLikelihoodMean, thetaCuspLikelihoodSeamMean] using
      hasDerivAt_log_thetaCuspLikelihoodPartition hB

theorem hasDerivAt_thetaCuspLikelihoodLogPartitionJetOne
    {B : ℝ} (hB : 0 < B) :
    HasDerivAt thetaCuspLikelihoodLogPartitionJetOne
      (thetaCuspLikelihoodLogPartitionJetTwo B) B := by
  have h := (hasDerivAt_thetaCuspLikelihoodMean hB).neg
  rw [neg_neg] at h
  exact h

theorem hasDerivAt_thetaCuspLikelihoodLogPartitionJetTwo
    {B : ℝ} (hB : 0 < B) :
    HasDerivAt thetaCuspLikelihoodLogPartitionJetTwo
      (thetaCuspLikelihoodLogPartitionJetThree B) B := by
  unfold thetaCuspLikelihoodLogPartitionJetTwo
    thetaCuspLikelihoodLogPartitionJetThree
  exact hasDerivAt_thetaCuspLikelihoodVariance hB

/-- Logarithmic likelihood partition pulled back to the theta source coordinate. -/
def thetaCuspLikelihoodSourceLogPartition (x : ℝ) : ℝ :=
  Real.log (thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x))

/-- First source-coordinate jet of the logarithmic likelihood partition. -/
def thetaCuspLikelihoodSourceLogPartitionJetOne (x : ℝ) : ℝ :=
  -2 * thetaCuspSingleAtomReflectionScale 1 x *
    thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)

/-- Second source-coordinate jet of the logarithmic likelihood partition. -/
def thetaCuspLikelihoodSourceLogPartitionJetTwo (x : ℝ) : ℝ :=
  4 * thetaCuspSingleAtomReflectionScale 1 x ^ (2 : ℕ) *
      thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate x) -
    4 * thetaCuspSingleAtomReflectionScale 1 x *
      thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)

/-- Third source-coordinate jet of the logarithmic likelihood partition. -/
def thetaCuspLikelihoodSourceLogPartitionJetThree (x : ℝ) : ℝ :=
  -8 * thetaCuspSingleAtomReflectionScale 1 x ^ (3 : ℕ) *
      thetaCuspLikelihoodThirdCumulant (thetaCuspLikelihoodCoordinate x) +
    24 * thetaCuspSingleAtomReflectionScale 1 x ^ (2 : ℕ) *
      thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate x) -
    8 * thetaCuspSingleAtomReflectionScale 1 x *
      thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)

theorem hasDerivAt_thetaCuspLikelihoodCoordinate (x : ℝ) :
    HasDerivAt thetaCuspLikelihoodCoordinate
      (2 * thetaCuspSingleAtomReflectionScale 1 x) x := by
  unfold thetaCuspLikelihoodCoordinate thetaCuspSingleAtomReflectionScale
  simp only [Nat.cast_one, one_pow]
  exact ((((Real.hasDerivAt_exp x).pow 2).const_mul Real.pi).sub_const
    (3 / 2)).congr_deriv (by
      rw [show Real.exp (2 * x) = Real.exp x ^ (2 : ℕ) by
        rw [show 2 * x = x + x by ring, Real.exp_add]
        ring]
      ring)

theorem hasDerivAt_thetaCuspSingleAtomReflectionScale_one (x : ℝ) :
    HasDerivAt (thetaCuspSingleAtomReflectionScale 1)
      (2 * thetaCuspSingleAtomReflectionScale 1 x) x := by
  unfold thetaCuspSingleAtomReflectionScale
  simp only [Nat.cast_one, one_pow, mul_one]
  refine (((Real.hasDerivAt_exp (2 * x)).comp x
    ((hasDerivAt_id x).const_mul 2)).const_mul Real.pi).congr_deriv ?_
  ring

theorem hasDerivAt_thetaCuspLikelihoodSourceLogPartition
    {x : ℝ} (hB : 0 < thetaCuspLikelihoodCoordinate x) :
    HasDerivAt thetaCuspLikelihoodSourceLogPartition
      (thetaCuspLikelihoodSourceLogPartitionJetOne x) x := by
  have hlog := hasDerivAt_log_thetaCuspLikelihoodPartition_cumulant hB
  have hcoord := hasDerivAt_thetaCuspLikelihoodCoordinate x
  exact (hlog.comp x hcoord).congr_deriv (by
    unfold thetaCuspLikelihoodSourceLogPartitionJetOne
      thetaCuspLikelihoodLogPartitionJetOne
    ring)

theorem hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetOne
    {x : ℝ} (hB : 0 < thetaCuspLikelihoodCoordinate x) :
    HasDerivAt thetaCuspLikelihoodSourceLogPartitionJetOne
      (thetaCuspLikelihoodSourceLogPartitionJetTwo x) x := by
  have hscale := hasDerivAt_thetaCuspSingleAtomReflectionScale_one x
  have hmean := (hasDerivAt_thetaCuspLikelihoodMean hB).comp x
    (hasDerivAt_thetaCuspLikelihoodCoordinate x)
  have hfun : thetaCuspLikelihoodSourceLogPartitionJetOne = fun y =>
      -2 * (thetaCuspSingleAtomReflectionScale 1 y *
        thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate y)) := by
    funext y
    unfold thetaCuspLikelihoodSourceLogPartitionJetOne
    ring
  rw [hfun]
  exact ((hscale.mul hmean).const_mul (-2)).congr_deriv (by
    simp only [Function.comp_apply]
    unfold thetaCuspLikelihoodSourceLogPartitionJetTwo
    ring)

theorem hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo
    {x : ℝ} (hB : 0 < thetaCuspLikelihoodCoordinate x) :
    HasDerivAt thetaCuspLikelihoodSourceLogPartitionJetTwo
      (thetaCuspLikelihoodSourceLogPartitionJetThree x) x := by
  have hscale := hasDerivAt_thetaCuspSingleAtomReflectionScale_one x
  have hmean := (hasDerivAt_thetaCuspLikelihoodMean hB).comp x
    (hasDerivAt_thetaCuspLikelihoodCoordinate x)
  have hvariance := (hasDerivAt_thetaCuspLikelihoodVariance hB).comp x
    (hasDerivAt_thetaCuspLikelihoodCoordinate x)
  have hfirst := ((hscale.pow 2).mul hvariance).const_mul 4
  have hsecond := (hscale.mul hmean).const_mul 4
  have hfun : thetaCuspLikelihoodSourceLogPartitionJetTwo = fun y =>
      4 * (thetaCuspSingleAtomReflectionScale 1 y ^ (2 : ℕ) *
          thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate y)) -
        4 * (thetaCuspSingleAtomReflectionScale 1 y *
          thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate y)) := by
    funext y
    unfold thetaCuspLikelihoodSourceLogPartitionJetTwo
    ring
  rw [hfun]
  exact (hfirst.sub hsecond).congr_deriv (by
    norm_num
    unfold thetaCuspLikelihoodSourceLogPartitionJetThree
    ring)

/-- Reflected likelihood action written entirely in source-coordinate cumulant variables. -/
def thetaCuspReflectedLikelihoodCumulantAction (u t : ℝ) : ℝ :=
  2 * thetaCuspLikelihoodSourceLogPartition u -
    thetaCuspLikelihoodSourceLogPartition (u + t) -
    thetaCuspLikelihoodSourceLogPartition (u - t)

/-- First displacement jet of the reflected likelihood action. -/
def thetaCuspReflectedLikelihoodCumulantJetOne (u t : ℝ) : ℝ :=
  thetaCuspLikelihoodSourceLogPartitionJetOne (u - t) -
    thetaCuspLikelihoodSourceLogPartitionJetOne (u + t)

/-- Second displacement jet of the reflected likelihood action. -/
def thetaCuspReflectedLikelihoodCumulantJetTwo (u t : ℝ) : ℝ :=
  -thetaCuspLikelihoodSourceLogPartitionJetTwo (u + t) -
    thetaCuspLikelihoodSourceLogPartitionJetTwo (u - t)

/-- Third displacement jet of the reflected likelihood action. -/
def thetaCuspReflectedLikelihoodCumulantJetThree (u t : ℝ) : ℝ :=
  thetaCuspLikelihoodSourceLogPartitionJetThree (u - t) -
    thetaCuspLikelihoodSourceLogPartitionJetThree (u + t)

/-- The cumulant action is exactly the previously isolated likelihood-interference action. -/
theorem thetaCuspReflectedLikelihoodInterferenceAction_eq_cumulantAction
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    thetaCuspReflectedLikelihoodInterferenceAction u t =
      thetaCuspReflectedLikelihoodCumulantAction u t := by
  have hplus : 0 < thetaCuspLikelihoodCoordinate (u + t) :=
    thetaCuspLikelihoodCoordinate_pos (by linarith)
  have hminus : 0 < thetaCuspLikelihoodCoordinate (u - t) :=
    thetaCuspLikelihoodCoordinate_pos (by linarith)
  have hcenter : 0 < thetaCuspLikelihoodCoordinate u :=
    thetaCuspLikelihoodCoordinate_pos (le_trans ht htu)
  have hpPlus := thetaCuspLikelihoodPartition_pos hplus
  have hpMinus := thetaCuspLikelihoodPartition_pos hminus
  have hpCenter := thetaCuspLikelihoodPartition_pos hcenter
  unfold thetaCuspReflectedLikelihoodInterferenceAction
    thetaCuspReflectedLikelihoodInterference
    thetaCuspReflectedLikelihoodCumulantAction
    thetaCuspLikelihoodSourceLogPartition
  rw [Real.log_div (mul_ne_zero hpPlus.ne' hpMinus.ne')
      (pow_ne_zero 2 hpCenter.ne'),
    Real.log_mul hpPlus.ne' hpMinus.ne',
    Real.log_pow]
  norm_num
  ring

theorem hasDerivAt_thetaCuspReflectedLikelihoodCumulantAction
    {u t : ℝ}
    (hplus : 0 < thetaCuspLikelihoodCoordinate (u + t))
    (hminus : 0 < thetaCuspLikelihoodCoordinate (u - t)) :
    HasDerivAt (thetaCuspReflectedLikelihoodCumulantAction u)
      (thetaCuspReflectedLikelihoodCumulantJetOne u t) t := by
  have hp := (hasDerivAt_thetaCuspLikelihoodSourceLogPartition hplus).comp t
    ((hasDerivAt_id t).const_add u)
  have hm := (hasDerivAt_thetaCuspLikelihoodSourceLogPartition hminus).comp t
    ((hasDerivAt_id t).const_sub u)
  have hconst := hasDerivAt_const t (2 * thetaCuspLikelihoodSourceLogPartition u)
  exact ((hconst.sub hp).sub hm).congr_deriv (by
    unfold thetaCuspReflectedLikelihoodCumulantJetOne
    ring)

theorem hasDerivAt_thetaCuspReflectedLikelihoodCumulantJetOne
    {u t : ℝ}
    (hplus : 0 < thetaCuspLikelihoodCoordinate (u + t))
    (hminus : 0 < thetaCuspLikelihoodCoordinate (u - t)) :
    HasDerivAt (thetaCuspReflectedLikelihoodCumulantJetOne u)
      (thetaCuspReflectedLikelihoodCumulantJetTwo u t) t := by
  have hp := (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetOne hplus).comp t
    ((hasDerivAt_id t).const_add u)
  have hm := (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetOne hminus).comp t
    ((hasDerivAt_id t).const_sub u)
  exact (hm.sub hp).congr_deriv (by
    unfold thetaCuspReflectedLikelihoodCumulantJetTwo
    ring)

theorem hasDerivAt_thetaCuspReflectedLikelihoodCumulantJetTwo
    {u t : ℝ}
    (hplus : 0 < thetaCuspLikelihoodCoordinate (u + t))
    (hminus : 0 < thetaCuspLikelihoodCoordinate (u - t)) :
    HasDerivAt (thetaCuspReflectedLikelihoodCumulantJetTwo u)
      (thetaCuspReflectedLikelihoodCumulantJetThree u t) t := by
  have hp := (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo hplus).comp t
    ((hasDerivAt_id t).const_add u)
  have hm := (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo hminus).comp t
    ((hasDerivAt_id t).const_sub u)
  exact (hp.neg.sub hm).congr_deriv (by
    unfold thetaCuspReflectedLikelihoodCumulantJetThree
    ring)

/-- Exact completed reflected logarithmic action in atom-plus-cumulant coordinates. -/
def thetaCuspCompletedReflectedCumulantAction (u t : ℝ) : ℝ :=
  thetaCuspSingleAtomReflectedAction
      (thetaCuspSingleAtomReflectionScale 1 u) t +
    thetaCuspReflectedLikelihoodCumulantAction u t

/-- The completed normalized source action is literally the atom-plus-cumulant action. -/
theorem neg_log_thetaCuspFullSource_reflected_normalized_eq_completedCumulantAction
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    -Real.log
        (thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) /
          thetaCuspFullSource u ^ (2 : ℕ)) =
      thetaCuspCompletedReflectedCumulantAction u t := by
  rw [thetaCuspFullSource_reflected_action_eq_singleAtom_add_interference ht htu,
    thetaCuspReflectedLikelihoodInterferenceAction_eq_cumulantAction ht htu]
  rfl

/-- Riccati margin of the likelihood-interference action. -/
def thetaCuspReflectedLikelihoodCumulantRiccatiMargin (u t : ℝ) : ℝ :=
  2 * thetaCuspReflectedLikelihoodCumulantJetOne u t *
      thetaCuspReflectedLikelihoodCumulantJetTwo u t -
    thetaCuspReflectedLikelihoodCumulantJetThree u t

/-- Exact non-diagonal correction to the first-atom Riccati margin. -/
def thetaCuspReflectedLikelihoodCumulantCorrection (u t : ℝ) : ℝ :=
  thetaCuspReflectedLikelihoodCumulantRiccatiMargin u t +
    2 * (thetaCuspSingleAtomReflectedActionJetOne
          (thetaCuspSingleAtomReflectionScale 1 u)
          (thetaCuspSingleAtomReflectionDefect t)
          (2 * Real.sinh (2 * t)) *
        thetaCuspReflectedLikelihoodCumulantJetTwo u t +
      thetaCuspReflectedLikelihoodCumulantJetOne u t *
        thetaCuspSingleAtomReflectedActionJetTwo
          (thetaCuspSingleAtomReflectionScale 1 u)
          (thetaCuspSingleAtomReflectionDefect t))

/-- Riccati margin of the exact completed atom-plus-cumulant jet. -/
def thetaCuspCompletedReflectedCumulantRiccatiMargin (u t : ℝ) : ℝ :=
  2 *
      (thetaCuspSingleAtomReflectedActionJetOne
          (thetaCuspSingleAtomReflectionScale 1 u)
          (thetaCuspSingleAtomReflectionDefect t)
          (2 * Real.sinh (2 * t)) +
        thetaCuspReflectedLikelihoodCumulantJetOne u t) *
      (thetaCuspSingleAtomReflectedActionJetTwo
          (thetaCuspSingleAtomReflectionScale 1 u)
          (thetaCuspSingleAtomReflectionDefect t) +
        thetaCuspReflectedLikelihoodCumulantJetTwo u t) -
    (thetaCuspSingleAtomReflectedActionJetThree
        (thetaCuspSingleAtomReflectionScale 1 u)
        (thetaCuspSingleAtomReflectionDefect t)
        (2 * Real.sinh (2 * t)) +
      thetaCuspReflectedLikelihoodCumulantJetThree u t)

/-- **Exact cumulant obstruction law.**  The completed margin is the strict first-atom margin plus
the unique mean--variance--third-cumulant interference correction. -/
theorem thetaCuspCompletedReflectedCumulantRiccatiMargin_eq_atom_add_correction
    (u t : ℝ) :
    thetaCuspCompletedReflectedCumulantRiccatiMargin u t =
      thetaCuspSingleAtomReflectedRiccatiMargin
          (thetaCuspSingleAtomReflectionScale 1 u)
          (thetaCuspSingleAtomReflectionDefect t)
          (2 * Real.sinh (2 * t)) +
        thetaCuspReflectedLikelihoodCumulantCorrection u t := by
  unfold thetaCuspCompletedReflectedCumulantRiccatiMargin
    thetaCuspSingleAtomReflectedRiccatiMargin
    thetaCuspReflectedLikelihoodCumulantCorrection
    thetaCuspReflectedLikelihoodCumulantRiccatiMargin
  ring

/-- The completed same-half-line Riccati sign is exactly a lower bound on the likelihood cumulant
correction by the negative strict atom margin. -/
theorem thetaCuspCompletedReflectedCumulantRiccatiMargin_pos_iff
    (u t : ℝ) :
    0 < thetaCuspCompletedReflectedCumulantRiccatiMargin u t ↔
      -thetaCuspSingleAtomReflectedRiccatiMargin
          (thetaCuspSingleAtomReflectionScale 1 u)
          (thetaCuspSingleAtomReflectionDefect t)
          (2 * Real.sinh (2 * t)) <
        thetaCuspReflectedLikelihoodCumulantCorrection u t := by
  rw [thetaCuspCompletedReflectedCumulantRiccatiMargin_eq_atom_add_correction]
  constructor <;> intro h <;> linarith

/-- A nonnegative likelihood cumulant correction is sufficient for strict completed-source
Riccati contraction because the first-atom margin is already strictly positive. -/
theorem thetaCuspCompletedReflectedCumulantRiccatiMargin_pos_of_correction_nonneg
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hcorrection : 0 ≤ thetaCuspReflectedLikelihoodCumulantCorrection u t) :
    0 < thetaCuspCompletedReflectedCumulantRiccatiMargin u t := by
  rw [thetaCuspCompletedReflectedCumulantRiccatiMargin_eq_atom_add_correction]
  exact add_pos_of_pos_of_nonneg
    (thetaCuspSourceTerm_reflectedRiccatiMargin_pos
      (n := 1) (by norm_num) ht htu)
    hcorrection

end

end RHTower
