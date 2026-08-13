import GaloisForLFunctions.RHTower.CCMZeroExtendedFourierCorrelation

/-!
# The exact CCM real Fourier block and the `w02` correction

Connes--Consani, *Weil positivity and trace formula, the archimedean place and the
prolate projections* (2021), Lemma `w02`, computes the polar contribution to the
restricted Weil matrix in the centered real Fourier basis.  Starting from the literal
zero-extended real modes, this file proves the bilateral exponential correlation
factorization and evaluates both parity blocks.

The odd formula in the paper is exact.  The displayed even formula is missing a factor
of two: the normalized cosine modes give coefficient `16`, not `8`.  This is already
forced by the paper's preceding correlation table.  We prove the corrected equality and
prove that the published even right-hand side is unequal to the literal source pairing.
-/

open MeasureTheory Set
open scoped Convolution

noncomputable section

namespace RHTower

/-! ## Bilateral exponential moments of correlations -/

/-- Literal additive correlation `f * g^*` for real functions. -/
def ccmRealCorrelation (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, f x * g (x - t)

/-- Literal complex correlation `f * g^*` used in CCM Lemma `polarize`. -/
def ccmComplexCorrelation (f g : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, f x * (starRingEnd ℂ) (g (x - t))

/-- Exponential tilt used by the polar terms at `s = ±1/2`. -/
def ccmRealExponentialTilt (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f x * Real.exp (a * x)

/-- Reflected exponential tilt occurring after the correlation change of variables. -/
def ccmRealReflectedExponentialTilt (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f (-x) * Real.exp (a * x)

/-- Bilateral exponential moment. -/
def ccmRealExponentialMoment (a : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, ccmRealExponentialTilt a f x

/-- The weighted literal correlation is a convolution of oppositely oriented tilts. -/
theorem ccmRealCorrelation_mul_exp_eq_convolution
    (a : ℝ) (f g : ℝ → ℝ) :
    (fun t => ccmRealCorrelation f g t * Real.exp (a * t)) =
      ccmRealReflectedExponentialTilt a g ⋆[ContinuousLinearMap.mul ℝ ℝ]
        ccmRealExponentialTilt a f := by
  funext t
  rw [ccmRealCorrelation, MeasureTheory.convolution_def]
  rw [← integral_sub_left_eq_self
    (fun x : ℝ => f x * g (x - t)) volume t]
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ccmRealReflectedExponentialTilt, ccmRealExponentialTilt]
  change (f (t - x) * g ((t - x) - t)) * Real.exp (a * t) =
    (g (-x) * Real.exp (a * x)) *
      (f (t - x) * Real.exp (a * (t - x)))
  have hexp : Real.exp (a * t) =
      Real.exp (a * x) * Real.exp (a * (t - x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring_nf

/-- Reflection turns a positive exponential tilt into the negative exponential moment. -/
theorem integral_ccmRealReflectedExponentialTilt
    (a : ℝ) (f : ℝ → ℝ) :
    (∫ x : ℝ, ccmRealReflectedExponentialTilt a f x) =
      ccmRealExponentialMoment (-a) f := by
  rw [ccmRealExponentialMoment]
  rw [← integral_neg_eq_self (ccmRealExponentialTilt (-a) f) volume]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ccmRealReflectedExponentialTilt, ccmRealExponentialTilt]
  ring_nf

private theorem integrable_reflectedTilt
    {a : ℝ} {f : ℝ → ℝ} (hf : Integrable (ccmRealExponentialTilt (-a) f)) :
    Integrable (ccmRealReflectedExponentialTilt a f) := by
  have hneg := hf.comp_neg
  apply hneg.congr
  filter_upwards [] with x
  rw [ccmRealReflectedExponentialTilt, ccmRealExponentialTilt]
  ring_nf

/-- **Exponential correlation factorization.**  No parity or smoothness is required: compact
support enters only later to discharge the two integrability facts. -/
theorem integral_ccmRealCorrelation_mul_exp
    (a : ℝ) (f g : ℝ → ℝ)
    (hf : Integrable (ccmRealExponentialTilt a f))
    (hg : Integrable (ccmRealExponentialTilt (-a) g)) :
    (∫ t : ℝ, ccmRealCorrelation f g t * Real.exp (a * t)) =
      ccmRealExponentialMoment a f * ccmRealExponentialMoment (-a) g := by
  rw [ccmRealCorrelation_mul_exp_eq_convolution]
  rw [MeasureTheory.integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
    (integrable_reflectedTilt hg) hf]
  rw [integral_ccmRealReflectedExponentialTilt]
  change ccmRealExponentialMoment (-a) g *
      (∫ x : ℝ, ccmRealExponentialTilt a f x) = _
  simp only [ccmRealExponentialMoment]
  ring

/-- Literal `W_{0,2}` correlation pairing in logarithmic coordinates. -/
def ccmW02CorrelationPairing (f g : ℝ → ℝ) : ℝ :=
  ∫ t : ℝ, ccmRealCorrelation f g t *
    (Real.exp (t / 2) + Real.exp (-t / 2))

/-- Conceptual rank-one law behind Lemma `w02`: each parity block is the sum of two outer
products of exponential-moment vectors. -/
theorem ccmW02CorrelationPairing_eq_moments
    (f g : ℝ → ℝ)
    (hfplus : Integrable (ccmRealExponentialTilt (1 / 2) f))
    (hfminus : Integrable (ccmRealExponentialTilt (-(1 / 2)) f))
    (hgplus : Integrable (ccmRealExponentialTilt (1 / 2) g))
    (hgminus : Integrable (ccmRealExponentialTilt (-(1 / 2)) g)) :
    ccmW02CorrelationPairing f g =
      ccmRealExponentialMoment (1 / 2) f *
          ccmRealExponentialMoment (-(1 / 2)) g +
        ccmRealExponentialMoment (-(1 / 2)) f *
          ccmRealExponentialMoment (1 / 2) g := by
  have hplus : Integrable (fun t : ℝ =>
      ccmRealCorrelation f g t * Real.exp ((1 / 2) * t)) := by
    rw [ccmRealCorrelation_mul_exp_eq_convolution]
    exact (integrable_reflectedTilt hgminus).integrable_convolution
      (ContinuousLinearMap.mul ℝ ℝ) hfplus
  have hminus : Integrable (fun t : ℝ =>
      ccmRealCorrelation f g t * Real.exp ((-(1 / 2)) * t)) := by
    rw [ccmRealCorrelation_mul_exp_eq_convolution]
    exact (integrable_reflectedTilt (by simpa using hgplus)).integrable_convolution
      (ContinuousLinearMap.mul ℝ ℝ) hfminus
  rw [ccmW02CorrelationPairing]
  have hpoint : (fun t : ℝ => ccmRealCorrelation f g t *
      (Real.exp (t / 2) + Real.exp (-t / 2))) =
      fun t : ℝ =>
        ccmRealCorrelation f g t * Real.exp ((1 / 2) * t) +
          ccmRealCorrelation f g t * Real.exp ((-(1 / 2)) * t) := by
    funext t
    ring_nf
  rw [hpoint, integral_add hplus hminus,
    integral_ccmRealCorrelation_mul_exp (1 / 2) f g hfplus hgminus,
    integral_ccmRealCorrelation_mul_exp (-(1 / 2)) f g hfminus
      (by simpa using hgplus)]
  norm_num

/-! ## Elementary compact exponential moments -/

def ccmExpCosPrimitive (a b x : ℝ) : ℝ :=
  Real.exp (a * x) * (a * Real.cos (b * x) + b * Real.sin (b * x)) /
    (a ^ 2 + b ^ 2)

def ccmExpSinPrimitive (a b x : ℝ) : ℝ :=
  Real.exp (a * x) * (a * Real.sin (b * x) - b * Real.cos (b * x)) /
    (a ^ 2 + b ^ 2)

theorem hasDerivAt_ccmExpCosPrimitive
    {a b : ℝ} (hden : a ^ 2 + b ^ 2 ≠ 0) (x : ℝ) :
    HasDerivAt (ccmExpCosPrimitive a b)
      (Real.exp (a * x) * Real.cos (b * x)) x := by
  have hE : HasDerivAt (fun y : ℝ => Real.exp (a * y))
      (a * Real.exp (a * x)) x := by
    convert! (Real.hasDerivAt_exp (a * x)).comp x
      ((hasDerivAt_id x).const_mul a) using 1
    all_goals ring
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (b * y))
      (-b * Real.sin (b * x)) x := by
    convert! (Real.hasDerivAt_cos (b * x)).comp x
      ((hasDerivAt_id x).const_mul b) using 1
    all_goals ring
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (b * y))
      (b * Real.cos (b * x)) x := by
    convert! (Real.hasDerivAt_sin (b * x)).comp x
      ((hasDerivAt_id x).const_mul b) using 1
    all_goals ring
  convert! (hE.mul ((hcos.const_mul a).add (hsin.const_mul b))).div_const
    (a ^ 2 + b ^ 2) using 1
  field_simp [hden]
  simp only [Pi.add_apply]
  rw [show x * b = b * x by ring]
  ring

theorem hasDerivAt_ccmExpSinPrimitive
    {a b : ℝ} (hden : a ^ 2 + b ^ 2 ≠ 0) (x : ℝ) :
    HasDerivAt (ccmExpSinPrimitive a b)
      (Real.exp (a * x) * Real.sin (b * x)) x := by
  have hE : HasDerivAt (fun y : ℝ => Real.exp (a * y))
      (a * Real.exp (a * x)) x := by
    convert! (Real.hasDerivAt_exp (a * x)).comp x
      ((hasDerivAt_id x).const_mul a) using 1
    all_goals ring
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (b * y))
      (-b * Real.sin (b * x)) x := by
    convert! (Real.hasDerivAt_cos (b * x)).comp x
      ((hasDerivAt_id x).const_mul b) using 1
    all_goals ring
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (b * y))
      (b * Real.cos (b * x)) x := by
    convert! (Real.hasDerivAt_sin (b * x)).comp x
      ((hasDerivAt_id x).const_mul b) using 1
    all_goals ring
  convert! (hE.mul ((hsin.const_mul a).sub (hcos.const_mul b))).div_const
    (a ^ 2 + b ^ 2) using 1
  field_simp [hden]
  simp only [Pi.sub_apply]
  rw [show x * b = b * x by ring]
  ring

theorem intervalIntegral_exp_mul_cos
    {a b c d : ℝ} (hden : a ^ 2 + b ^ 2 ≠ 0) :
    (∫ x in c..d, Real.exp (a * x) * Real.cos (b * x)) =
      ccmExpCosPrimitive a b d - ccmExpCosPrimitive a b c := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    exact hasDerivAt_ccmExpCosPrimitive hden x
  · exact (by fun_prop : Continuous (fun x : ℝ =>
      Real.exp (a * x) * Real.cos (b * x))).intervalIntegrable c d

theorem intervalIntegral_exp_mul_sin
    {a b c d : ℝ} (hden : a ^ 2 + b ^ 2 ≠ 0) :
    (∫ x in c..d, Real.exp (a * x) * Real.sin (b * x)) =
      ccmExpSinPrimitive a b d - ccmExpSinPrimitive a b c := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    exact hasDerivAt_ccmExpSinPrimitive hden x
  · exact (by fun_prop : Continuous (fun x : ℝ =>
      Real.exp (a * x) * Real.sin (b * x))).intervalIntegrable c d

/-! ## The literal centered real Fourier modes -/

/-- Positive Fourier frequency `2πn/L`. -/
def ccmCenteredModeFrequency (L : CCMPositiveAperture) (n : ℕ) : ℝ :=
  2 * Real.pi * n / (L : ℝ)

/-- Full-period compact cosine integral.  Endpoint parity is retained explicitly. -/
theorem intervalIntegral_exp_mul_cos_centeredMode
    (L : CCMPositiveAperture) (n : ℕ) (a : ℝ)
    (hden : a ^ 2 + ccmCenteredModeFrequency L n ^ 2 ≠ 0) :
    (∫ x in (-(L : ℝ) / 2)..((L : ℝ) / 2),
      Real.exp (a * x) * Real.cos (ccmCenteredModeFrequency L n * x)) =
      (-1 : ℝ) ^ n * a *
        (Real.exp (a * (L : ℝ) / 2) - Real.exp (-(a * (L : ℝ) / 2))) /
          (a ^ 2 + ccmCenteredModeFrequency L n ^ 2) := by
  rw [intervalIntegral_exp_mul_cos hden]
  have hpos : ccmCenteredModeFrequency L n * ((L : ℝ) / 2) =
      (n : ℝ) * Real.pi := by
    rw [ccmCenteredModeFrequency]
    field_simp [ne_of_gt L.property]
  have hneg : ccmCenteredModeFrequency L n * (-(L : ℝ) / 2) =
      -((n : ℝ) * Real.pi) := by
    rw [ccmCenteredModeFrequency]
    field_simp [ne_of_gt L.property]
  rw [ccmExpCosPrimitive, ccmExpCosPrimitive, hpos, hneg,
    Real.sin_neg, Real.cos_neg, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
  simp only [mul_zero, add_zero]
  rw [show a * (-(L : ℝ) / 2) = -(a * (L : ℝ) / 2) by ring]
  ring_nf

/-- Full-period compact sine integral for the paper's negative-index mode `ξ_{-n}`. -/
theorem intervalIntegral_exp_mul_sin_centeredNegativeMode
    (L : CCMPositiveAperture) (n : ℕ) (a : ℝ)
    (hden : a ^ 2 + ccmCenteredModeFrequency L n ^ 2 ≠ 0) :
    (∫ x in (-(L : ℝ) / 2)..((L : ℝ) / 2),
      Real.exp (a * x) * Real.sin (-(ccmCenteredModeFrequency L n) * x)) =
      (-1 : ℝ) ^ n * ccmCenteredModeFrequency L n *
        (Real.exp (a * (L : ℝ) / 2) - Real.exp (-(a * (L : ℝ) / 2))) /
          (a ^ 2 + ccmCenteredModeFrequency L n ^ 2) := by
  rw [intervalIntegral_exp_mul_sin]
  · have hpos : -(ccmCenteredModeFrequency L n) * ((L : ℝ) / 2) =
        -((n : ℝ) * Real.pi) := by
      rw [ccmCenteredModeFrequency]
      field_simp [ne_of_gt L.property]
    have hneg : -(ccmCenteredModeFrequency L n) * (-(L : ℝ) / 2) =
        (n : ℝ) * Real.pi := by
      rw [ccmCenteredModeFrequency]
      field_simp [ne_of_gt L.property]
    rw [ccmExpSinPrimitive, ccmExpSinPrimitive, hpos, hneg,
      Real.sin_neg, Real.cos_neg, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
    simp only [neg_zero, mul_zero, zero_sub]
    rw [show a * (-(L : ℝ) / 2) = -(a * (L : ℝ) / 2) by ring]
    ring_nf
  · simpa only [neg_sq] using hden

/-- Paper basis vector `ξ_n`, `n>0`, extended by zero outside `[-L/2,L/2]`. -/
def ccmCenteredCosineMode (L : CCMPositiveAperture) (n : ℕ) (x : ℝ) : ℝ :=
  (Icc (-(L : ℝ) / 2) ((L : ℝ) / 2)).indicator
    (fun y => (-1 : ℝ) ^ n * Real.sqrt (2 / (L : ℝ)) *
      Real.cos (ccmCenteredModeFrequency L n * y)) x

/-- Paper basis vector `ξ_{-n}`, `n>0`, extended by zero outside `[-L/2,L/2]`. -/
def ccmCenteredNegativeSineMode (L : CCMPositiveAperture) (n : ℕ) (x : ℝ) : ℝ :=
  (Icc (-(L : ℝ) / 2) ((L : ℝ) / 2)).indicator
    (fun y => (-1 : ℝ) ^ n * Real.sqrt (2 / (L : ℝ)) *
      Real.sin (-(ccmCenteredModeFrequency L n) * y)) x

theorem integrable_ccmCenteredCosineMode_tilt
    (L : CCMPositiveAperture) (n : ℕ) (a : ℝ) :
    Integrable (ccmRealExponentialTilt a (ccmCenteredCosineMode L n)) := by
  have heq : ccmRealExponentialTilt a (ccmCenteredCosineMode L n) =
      (Icc (-(L : ℝ) / 2) ((L : ℝ) / 2)).indicator
        (fun x => ((-1 : ℝ) ^ n * Real.sqrt (2 / (L : ℝ)) *
          Real.cos (ccmCenteredModeFrequency L n * x)) * Real.exp (a * x)) := by
    funext x
    by_cases hx : x ∈ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2)
    · simp [ccmRealExponentialTilt, ccmCenteredCosineMode, Set.indicator_of_mem hx]
    · simp [ccmRealExponentialTilt, ccmCenteredCosineMode, Set.indicator_of_notMem hx]
  rw [heq]
  refine (Continuous.integrableOn_Icc ?_).integrable_indicator measurableSet_Icc
  fun_prop

theorem integrable_ccmCenteredNegativeSineMode_tilt
    (L : CCMPositiveAperture) (n : ℕ) (a : ℝ) :
    Integrable (ccmRealExponentialTilt a (ccmCenteredNegativeSineMode L n)) := by
  have heq : ccmRealExponentialTilt a (ccmCenteredNegativeSineMode L n) =
      (Icc (-(L : ℝ) / 2) ((L : ℝ) / 2)).indicator
        (fun x => ((-1 : ℝ) ^ n * Real.sqrt (2 / (L : ℝ)) *
          Real.sin (-(ccmCenteredModeFrequency L n) * x)) * Real.exp (a * x)) := by
    funext x
    by_cases hx : x ∈ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2)
    · simp [ccmRealExponentialTilt, ccmCenteredNegativeSineMode,
        Set.indicator_of_mem hx]
    · simp [ccmRealExponentialTilt, ccmCenteredNegativeSineMode,
        Set.indicator_of_notMem hx]
  rw [heq]
  refine (Continuous.integrableOn_Icc ?_).integrable_indicator measurableSet_Icc
  fun_prop

/-- Exact exponential moment of the literal normalized positive cosine mode. -/
theorem ccmRealExponentialMoment_centeredCosineMode
    (L : CCMPositiveAperture) (n : ℕ) (a : ℝ)
    (hden : a ^ 2 + ccmCenteredModeFrequency L n ^ 2 ≠ 0) :
    ccmRealExponentialMoment a (ccmCenteredCosineMode L n) =
      Real.sqrt (2 / (L : ℝ)) * a *
        (Real.exp (a * (L : ℝ) / 2) - Real.exp (-(a * (L : ℝ) / 2))) /
          (a ^ 2 + ccmCenteredModeFrequency L n ^ 2) := by
  rw [ccmRealExponentialMoment]
  have heq : ccmRealExponentialTilt a (ccmCenteredCosineMode L n) =
      (Icc (-(L : ℝ) / 2) ((L : ℝ) / 2)).indicator
        (fun x => ((-1 : ℝ) ^ n * Real.sqrt (2 / (L : ℝ))) *
          (Real.exp (a * x) * Real.cos (ccmCenteredModeFrequency L n * x))) := by
    funext x
    by_cases hx : x ∈ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2)
    · simp [ccmRealExponentialTilt, ccmCenteredCosineMode, Set.indicator_of_mem hx]
      ring
    · simp [ccmRealExponentialTilt, ccmCenteredCosineMode,
        Set.indicator_of_notMem hx]
  rw [heq, integral_indicator measurableSet_Icc, integral_const_mul,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [L.property]),
    intervalIntegral_exp_mul_cos_centeredMode L n a hden]
  have hp : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← pow_add]
    norm_num [pow_succ]
  rw [show (-1 : ℝ) ^ n * Real.sqrt (2 / (L : ℝ)) *
      ((-1 : ℝ) ^ n * a *
        (Real.exp (a * (L : ℝ) / 2) - Real.exp (-(a * (L : ℝ) / 2))) /
          (a ^ 2 + ccmCenteredModeFrequency L n ^ 2)) =
      ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
        (Real.sqrt (2 / (L : ℝ)) * a *
          (Real.exp (a * (L : ℝ) / 2) - Real.exp (-(a * (L : ℝ) / 2))) /
            (a ^ 2 + ccmCenteredModeFrequency L n ^ 2)) by ring, hp, one_mul]

/-- Exact exponential moment of the literal normalized negative-index sine mode. -/
theorem ccmRealExponentialMoment_centeredNegativeSineMode
    (L : CCMPositiveAperture) (n : ℕ) (a : ℝ)
    (hden : a ^ 2 + ccmCenteredModeFrequency L n ^ 2 ≠ 0) :
    ccmRealExponentialMoment a (ccmCenteredNegativeSineMode L n) =
      Real.sqrt (2 / (L : ℝ)) * ccmCenteredModeFrequency L n *
        (Real.exp (a * (L : ℝ) / 2) - Real.exp (-(a * (L : ℝ) / 2))) /
          (a ^ 2 + ccmCenteredModeFrequency L n ^ 2) := by
  rw [ccmRealExponentialMoment]
  have heq : ccmRealExponentialTilt a (ccmCenteredNegativeSineMode L n) =
      (Icc (-(L : ℝ) / 2) ((L : ℝ) / 2)).indicator
        (fun x => ((-1 : ℝ) ^ n * Real.sqrt (2 / (L : ℝ))) *
          (Real.exp (a * x) * Real.sin (-(ccmCenteredModeFrequency L n) * x))) := by
    funext x
    by_cases hx : x ∈ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2)
    · simp [ccmRealExponentialTilt, ccmCenteredNegativeSineMode,
        Set.indicator_of_mem hx]
      ring
    · simp [ccmRealExponentialTilt, ccmCenteredNegativeSineMode,
        Set.indicator_of_notMem hx]
  rw [heq, integral_indicator measurableSet_Icc, integral_const_mul,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [L.property]),
    intervalIntegral_exp_mul_sin_centeredNegativeMode L n a hden]
  have hp : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← pow_add]
    norm_num [pow_succ]
  rw [show (-1 : ℝ) ^ n * Real.sqrt (2 / (L : ℝ)) *
      ((-1 : ℝ) ^ n * ccmCenteredModeFrequency L n *
        (Real.exp (a * (L : ℝ) / 2) - Real.exp (-(a * (L : ℝ) / 2))) /
          (a ^ 2 + ccmCenteredModeFrequency L n ^ 2)) =
      ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
        (Real.sqrt (2 / (L : ℝ)) * ccmCenteredModeFrequency L n *
          (Real.exp (a * (L : ℝ) / 2) - Real.exp (-(a * (L : ℝ) / 2))) /
            (a ^ 2 + ccmCenteredModeFrequency L n ^ 2)) by ring, hp, one_mul]

/-! ## Exact `w02` blocks and the published factor-two defect -/

/-- Common positive exponential factor in the paper's `w02` formulas. -/
def ccmW02ApertureFactor (L : CCMPositiveAperture) : ℝ :=
  Real.exp (-(L : ℝ) / 2) * (Real.exp ((L : ℝ) / 2) - 1) ^ 2

theorem sq_exp_quarter_sub_eq_ccmW02ApertureFactor (L : CCMPositiveAperture) :
    (Real.exp ((L : ℝ) / 4) - Real.exp (-(L : ℝ) / 4)) ^ 2 =
      ccmW02ApertureFactor L := by
  have hmul : Real.exp (-(L : ℝ) / 4) * Real.exp ((L : ℝ) / 2) =
      Real.exp ((L : ℝ) / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsq : Real.exp (-(L : ℝ) / 4) ^ 2 =
      Real.exp (-(L : ℝ) / 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [ccmW02ApertureFactor]
  calc
    (Real.exp ((L : ℝ) / 4) - Real.exp (-(L : ℝ) / 4)) ^ 2 =
        (Real.exp (-(L : ℝ) / 4) *
          (Real.exp ((L : ℝ) / 2) - 1)) ^ 2 := by
            rw [mul_sub, hmul, mul_one]
    _ = Real.exp (-(L : ℝ) / 4) ^ 2 *
        (Real.exp ((L : ℝ) / 2) - 1) ^ 2 := by ring
    _ = _ := by rw [hsq]

/-- Denominator used by the published real Fourier blocks. -/
def ccmW02ModeDenominator (L : CCMPositiveAperture) (n : ℕ) : ℝ :=
  (L : ℝ) ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2

private theorem ccmW02ModeDenominator_pos
    (L : CCMPositiveAperture) (n : ℕ) :
    0 < ccmW02ModeDenominator L n := by
  rw [ccmW02ModeDenominator]
  have hLsq : 0 < (L : ℝ) ^ 2 := sq_pos_of_pos L.property
  nlinarith [sq_nonneg (4 * Real.pi * (n : ℝ))]

private theorem half_sq_add_ccmCenteredModeFrequency_sq_ne
    (L : CCMPositiveAperture) (n : ℕ) :
    (1 / 2 : ℝ) ^ 2 + ccmCenteredModeFrequency L n ^ 2 ≠ 0 := by
  positivity

private theorem neg_half_sq_add_ccmCenteredModeFrequency_sq_ne
    (L : CCMPositiveAperture) (n : ℕ) :
    (-(1 / 2 : ℝ)) ^ 2 + ccmCenteredModeFrequency L n ^ 2 ≠ 0 := by
  positivity

private theorem ccmRealExponentialMoment_centeredCosineMode_half
    (L : CCMPositiveAperture) (n : ℕ) :
    ccmRealExponentialMoment (1 / 2) (ccmCenteredCosineMode L n) =
      2 * Real.sqrt (2 / (L : ℝ)) * (L : ℝ) ^ 2 *
        (Real.exp ((L : ℝ) / 4) - Real.exp (-(L : ℝ) / 4)) /
          ccmW02ModeDenominator L n := by
  rw [ccmRealExponentialMoment_centeredCosineMode L n (1 / 2)
    (half_sq_add_ccmCenteredModeFrequency_sq_ne L n),
    ccmCenteredModeFrequency, ccmW02ModeDenominator]
  ring_nf
  field_simp [ne_of_gt L.property, (ccmW02ModeDenominator_pos L n).ne']
  ring

private theorem ccmRealExponentialMoment_centeredCosineMode_neg_half
    (L : CCMPositiveAperture) (n : ℕ) :
    ccmRealExponentialMoment (-(1 / 2)) (ccmCenteredCosineMode L n) =
      2 * Real.sqrt (2 / (L : ℝ)) * (L : ℝ) ^ 2 *
        (Real.exp ((L : ℝ) / 4) - Real.exp (-(L : ℝ) / 4)) /
          ccmW02ModeDenominator L n := by
  rw [ccmRealExponentialMoment_centeredCosineMode L n (-(1 / 2))
    (neg_half_sq_add_ccmCenteredModeFrequency_sq_ne L n),
    ccmCenteredModeFrequency, ccmW02ModeDenominator]
  ring_nf
  field_simp [ne_of_gt L.property, (ccmW02ModeDenominator_pos L n).ne']
  ring

private theorem ccmRealExponentialMoment_centeredNegativeSineMode_half
    (L : CCMPositiveAperture) (n : ℕ) :
    ccmRealExponentialMoment (1 / 2) (ccmCenteredNegativeSineMode L n) =
      8 * Real.sqrt (2 / (L : ℝ)) * Real.pi * (n : ℝ) * (L : ℝ) *
        (Real.exp ((L : ℝ) / 4) - Real.exp (-(L : ℝ) / 4)) /
          ccmW02ModeDenominator L n := by
  rw [ccmRealExponentialMoment_centeredNegativeSineMode L n (1 / 2)
    (half_sq_add_ccmCenteredModeFrequency_sq_ne L n),
    ccmCenteredModeFrequency, ccmW02ModeDenominator]
  ring_nf
  field_simp [ne_of_gt L.property, (ccmW02ModeDenominator_pos L n).ne']
  ring

private theorem ccmRealExponentialMoment_centeredNegativeSineMode_neg_half
    (L : CCMPositiveAperture) (n : ℕ) :
    ccmRealExponentialMoment (-(1 / 2)) (ccmCenteredNegativeSineMode L n) =
      -(8 * Real.sqrt (2 / (L : ℝ)) * Real.pi * (n : ℝ) * (L : ℝ) *
        (Real.exp ((L : ℝ) / 4) - Real.exp (-(L : ℝ) / 4)) /
          ccmW02ModeDenominator L n) := by
  rw [ccmRealExponentialMoment_centeredNegativeSineMode L n (-(1 / 2))
    (neg_half_sq_add_ccmCenteredModeFrequency_sq_ne L n),
    ccmCenteredModeFrequency, ccmW02ModeDenominator]
  ring_nf
  field_simp [ne_of_gt L.property, (ccmW02ModeDenominator_pos L n).ne']
  ring

/-- The paper's displayed even right-hand side, with coefficient `8`. -/
def ccmW02PublishedEvenValue
    (L : CCMPositiveAperture) (m n : ℕ) : ℝ :=
  8 * ccmW02ApertureFactor L * (L : ℝ) ^ 3 /
    (ccmW02ModeDenominator L m * ccmW02ModeDenominator L n)

/-- The exact literal even source value; it has coefficient `16`. -/
def ccmW02CorrectedEvenValue
    (L : CCMPositiveAperture) (m n : ℕ) : ℝ :=
  16 * ccmW02ApertureFactor L * (L : ℝ) ^ 3 /
    (ccmW02ModeDenominator L m * ccmW02ModeDenominator L n)

/-- The odd formula printed in Lemma `w02`, indexed here by the positive magnitudes `m,n` of
the paper's negative indices `-m,-n`. -/
def ccmW02PublishedOddValue
    (L : CCMPositiveAperture) (m n : ℕ) : ℝ :=
  -(256 * Real.pi ^ 2 * (L : ℝ) * ccmW02ApertureFactor L * (m : ℝ) * (n : ℝ)) /
    (ccmW02ModeDenominator L m * ccmW02ModeDenominator L n)

/-- **Corrected even half of CCM Lemma `w02`.**  This starts from the literal normalized
zero-extended cosine modes and the literal bilateral polar pairing. -/
theorem ccmW02CorrelationPairing_centeredCosineMode
    (L : CCMPositiveAperture) (m n : ℕ) :
    ccmW02CorrelationPairing (ccmCenteredCosineMode L m)
        (ccmCenteredCosineMode L n) =
      ccmW02CorrectedEvenValue L m n := by
  rw [ccmW02CorrelationPairing_eq_moments
    (ccmCenteredCosineMode L m) (ccmCenteredCosineMode L n)
    (integrable_ccmCenteredCosineMode_tilt L m (1 / 2))
    (integrable_ccmCenteredCosineMode_tilt L m (-(1 / 2)))
    (integrable_ccmCenteredCosineMode_tilt L n (1 / 2))
    (integrable_ccmCenteredCosineMode_tilt L n (-(1 / 2)))]
  rw [ccmRealExponentialMoment_centeredCosineMode_half L m,
    ccmRealExponentialMoment_centeredCosineMode_neg_half L n,
    ccmRealExponentialMoment_centeredCosineMode_neg_half L m,
    ccmRealExponentialMoment_centeredCosineMode_half L n,
    ccmW02CorrectedEvenValue]
  have hsqrt : Real.sqrt (2 / (L : ℝ)) * Real.sqrt (2 / (L : ℝ)) =
      2 / (L : ℝ) := by
    have harg : 0 ≤ 2 / (L : ℝ) := div_nonneg (by norm_num) L.property.le
    simpa only [pow_two] using Real.sq_sqrt harg
  have hfac := sq_exp_quarter_sub_eq_ccmW02ApertureFactor L
  field_simp [(ccmW02ModeDenominator_pos L m).ne',
    (ccmW02ModeDenominator_pos L n).ne']
  rw [← hfac]
  ring_nf at hsqrt ⊢
  rw [hsqrt]
  field_simp [ne_of_gt L.property]
  ring

/-- **Exact odd half of CCM Lemma `w02`.** -/
theorem ccmW02CorrelationPairing_centeredNegativeSineMode
    (L : CCMPositiveAperture) (m n : ℕ) :
    ccmW02CorrelationPairing (ccmCenteredNegativeSineMode L m)
        (ccmCenteredNegativeSineMode L n) =
      ccmW02PublishedOddValue L m n := by
  rw [ccmW02CorrelationPairing_eq_moments
    (ccmCenteredNegativeSineMode L m) (ccmCenteredNegativeSineMode L n)
    (integrable_ccmCenteredNegativeSineMode_tilt L m (1 / 2))
    (integrable_ccmCenteredNegativeSineMode_tilt L m (-(1 / 2)))
    (integrable_ccmCenteredNegativeSineMode_tilt L n (1 / 2))
    (integrable_ccmCenteredNegativeSineMode_tilt L n (-(1 / 2)))]
  rw [ccmRealExponentialMoment_centeredNegativeSineMode_half L m,
    ccmRealExponentialMoment_centeredNegativeSineMode_neg_half L n,
    ccmRealExponentialMoment_centeredNegativeSineMode_neg_half L m,
    ccmRealExponentialMoment_centeredNegativeSineMode_half L n,
    ccmW02PublishedOddValue]
  have hsqrt : Real.sqrt (2 / (L : ℝ)) * Real.sqrt (2 / (L : ℝ)) =
      2 / (L : ℝ) := by
    have harg : 0 ≤ 2 / (L : ℝ) := div_nonneg (by norm_num) L.property.le
    simpa only [pow_two] using Real.sq_sqrt harg
  have hfac := sq_exp_quarter_sub_eq_ccmW02ApertureFactor L
  field_simp [(ccmW02ModeDenominator_pos L m).ne',
    (ccmW02ModeDenominator_pos L n).ne']
  rw [← hfac]
  ring_nf at hsqrt ⊢
  rw [hsqrt]
  field_simp [ne_of_gt L.property]
  ring

/-- The corrected even coefficient is exactly twice the paper's displayed coefficient. -/
theorem ccmW02CorrectedEvenValue_eq_two_mul_published
    (L : CCMPositiveAperture) (m n : ℕ) :
    ccmW02CorrectedEvenValue L m n =
      2 * ccmW02PublishedEvenValue L m n := by
  rw [ccmW02CorrectedEvenValue, ccmW02PublishedEvenValue]
  field_simp [(ccmW02ModeDenominator_pos L m).ne',
    (ccmW02ModeDenominator_pos L n).ne']
  ring

theorem ccmW02ApertureFactor_pos (L : CCMPositiveAperture) :
    0 < ccmW02ApertureFactor L := by
  rw [ccmW02ApertureFactor]
  have hexp : 1 < Real.exp ((L : ℝ) / 2) := by
    simpa using Real.exp_lt_exp.mpr (by linarith [L.property] : 0 < (L : ℝ) / 2)
  positivity

theorem ccmW02PublishedEvenValue_pos
    (L : CCMPositiveAperture) (m n : ℕ) :
    0 < ccmW02PublishedEvenValue L m n := by
  rw [ccmW02PublishedEvenValue]
  apply div_pos
  · exact mul_pos (mul_pos (by norm_num) (ccmW02ApertureFactor_pos L))
      (pow_pos L.property 3)
  · exact mul_pos (ccmW02ModeDenominator_pos L m)
      (ccmW02ModeDenominator_pos L n)

/-- **The even equality printed in CCM Lemma `w02` is false.**  For every positive aperture
and every pair of normalized cosine modes, the literal source pairing differs from the paper's
displayed coefficient-`8` value.  The corrected coefficient is `16`. -/
theorem ccmW02CorrelationPairing_centeredCosineMode_ne_published
    (L : CCMPositiveAperture) (m n : ℕ) :
    ccmW02CorrelationPairing (ccmCenteredCosineMode L m)
        (ccmCenteredCosineMode L n) ≠
      ccmW02PublishedEvenValue L m n := by
  rw [ccmW02CorrelationPairing_centeredCosineMode,
    ccmW02CorrectedEvenValue_eq_two_mul_published]
  have hpos := ccmW02PublishedEvenValue_pos L m n
  intro h
  nlinarith

/-! ## The exact even/odd block separation -/

theorem ccmCenteredCosineMode_neg
    (L : CCMPositiveAperture) (n : ℕ) (x : ℝ) :
    ccmCenteredCosineMode L n (-x) = ccmCenteredCosineMode L n x := by
  have hmem : -x ∈ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2) ↔
      x ∈ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2) := by
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  by_cases hx : x ∈ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2)
  · rw [ccmCenteredCosineMode, ccmCenteredCosineMode,
      Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx)]
    rw [show ccmCenteredModeFrequency L n * -x =
      -(ccmCenteredModeFrequency L n * x) by ring, Real.cos_neg]
  · rw [ccmCenteredCosineMode, ccmCenteredCosineMode,
      Set.indicator_of_notMem hx, Set.indicator_of_notMem (by simpa [hmem] using hx)]

theorem ccmCenteredNegativeSineMode_neg
    (L : CCMPositiveAperture) (n : ℕ) (x : ℝ) :
    ccmCenteredNegativeSineMode L n (-x) =
      -ccmCenteredNegativeSineMode L n x := by
  have hmem : -x ∈ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2) ↔
      x ∈ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2) := by
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  by_cases hx : x ∈ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2)
  · rw [ccmCenteredNegativeSineMode, ccmCenteredNegativeSineMode,
      Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx)]
    rw [show -(ccmCenteredModeFrequency L n) * -x =
      -(-(ccmCenteredModeFrequency L n) * x) by ring, Real.sin_neg]
    ring
  · rw [ccmCenteredNegativeSineMode, ccmCenteredNegativeSineMode,
      Set.indicator_of_notMem hx, Set.indicator_of_notMem (by simpa [hmem] using hx), neg_zero]

/-- Real correlation reflection, Lemma `polarize(ii)`. -/
theorem ccmRealCorrelation_neg (f g : ℝ → ℝ) (t : ℝ) :
    ccmRealCorrelation f g (-t) = ccmRealCorrelation g f t := by
  rw [ccmRealCorrelation, ccmRealCorrelation]
  have hshift := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun x : ℝ => f x * g (x + t)) (-t)
  rw [show (fun x : ℝ => f x * g (x - -t)) =
      fun x : ℝ => f x * g (x + t) by funext x; ring_nf]
  rw [← hshift]
  apply integral_congr_ae
  filter_upwards [] with x
  ring_nf

/-- Real functions supported in the centered CCM aperture.  No regularity is imposed because
Lemma `polarize(i)` needs only the support statement; this strengthens its `L²` formulation. -/
structure CCMCenteredWindowFunction (L : CCMPositiveAperture) where
  toFun : ℝ → ℝ
  zero_outside : ∀ x : ℝ,
    x ∉ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2) → toFun x = 0

instance (L : CCMPositiveAperture) : CoeFun (CCMCenteredWindowFunction L) (fun _ => ℝ → ℝ) :=
  ⟨CCMCenteredWindowFunction.toFun⟩

/-- A lag strictly outside the correlation aperture `[-L,L]`. -/
abbrev CCMExteriorLag (L : CCMPositiveAperture) :=
  {t : ℝ // (L : ℝ) < |t|}

/-- A literal zero-extended representative of an element of
`L²([-L/2,L/2], ℂ)`.  Bundling square-integrability and support makes the source
quantifiers intrinsic data rather than theorem hypotheses. -/
structure CCMCenteredComplexL2Function (L : CCMPositiveAperture) where
  toFun : ℝ → ℂ
  memLp : MemLp toFun 2 (volume : Measure ℝ)
  zero_outside : ∀ x : ℝ,
    x ∉ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2) → toFun x = 0

instance (L : CCMPositiveAperture) :
    CoeFun (CCMCenteredComplexL2Function L) (fun _ => ℝ → ℂ) :=
  ⟨CCMCenteredComplexL2Function.toFun⟩

/-- Lemma `polarize(i)`, literal complex support assertion: the correlation of two
zero-extended `L²([-L/2,L/2])` functions vanishes outside `[-L,L]`. -/
theorem ccmComplexCorrelation_centeredL2_eq_zero
    (L : CCMPositiveAperture)
    (f g : CCMCenteredComplexL2Function L) (t : CCMExteriorLag L) :
    ccmComplexCorrelation f g (t : ℝ) = 0 := by
  rw [ccmComplexCorrelation]
  have hfun :
      (fun x : ℝ => f x * (starRingEnd ℂ) (g (x - (t : ℝ)))) = fun _ => 0 := by
    funext x
    by_cases hx : x ∈ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2)
    · have hgt : x - (t : ℝ) ∉ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2) := by
        intro hxt
        rcases lt_abs.mp t.property with ht | ht
        · linarith [hx.1, hx.2, hxt.1, hxt.2]
        · linarith [hx.1, hx.2, hxt.1, hxt.2]
      rw [g.zero_outside _ hgt, map_zero, mul_zero]
    · rw [f.zero_outside _ hx, zero_mul]
  rw [hfun, integral_zero]

/-- Lemma `polarize(i)`, first displayed formula, with its literal complex conjugation
and exact positive-lag overlap interval. -/
theorem ccmComplexCorrelation_centeredL2_eq_integral
    (L : CCMPositiveAperture)
    (f g : CCMCenteredComplexL2Function L) (t : CCMApertureLag L) :
    ccmComplexCorrelation f g (t : ℝ) =
      ∫ x in Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2),
        f x * (starRingEnd ℂ) (g (x - (t : ℝ))) := by
  rw [ccmComplexCorrelation]
  have hfun :
      (fun x : ℝ => f x * (starRingEnd ℂ) (g (x - (t : ℝ)))) =
        (Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2)).indicator
          (fun x : ℝ => f x * (starRingEnd ℂ) (g (x - (t : ℝ)))) := by
    funext x
    by_cases hoverlap : x ∈ Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2)
    · rw [Set.indicator_of_mem hoverlap]
    · rw [Set.indicator_of_notMem hoverlap]
      by_cases hx : x ∈ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2)
      · have hgt : x - (t : ℝ) ∉ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2) := by
          intro hxt
          apply hoverlap
          constructor <;> linarith [hx.1, hx.2, hxt.1, hxt.2, t.property.1]
        rw [g.zero_outside _ hgt, map_zero, mul_zero]
      · rw [f.zero_outside _ hx, zero_mul]
  calc
    (∫ x : ℝ, f x * (starRingEnd ℂ) (g (x - (t : ℝ)))) =
        ∫ x : ℝ,
          (Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2)).indicator
            (fun y : ℝ => f y * (starRingEnd ℂ) (g (y - (t : ℝ)))) x :=
      congrArg (fun h : ℝ → ℂ => ∫ x : ℝ, h x) hfun
    _ = _ := MeasureTheory.integral_indicator (μ := volume)
      (f := fun x : ℝ => f x * (starRingEnd ℂ) (g (x - (t : ℝ)))) measurableSet_Icc

/-- Lemma `polarize(i)`, second displayed formula, after the literal translation of
the negative-lag correlation to the common positive-lag overlap interval. -/
theorem ccmComplexCorrelation_centeredL2_neg_eq_integral
    (L : CCMPositiveAperture)
    (f g : CCMCenteredComplexL2Function L) (t : CCMApertureLag L) :
    ccmComplexCorrelation f g (-(t : ℝ)) =
      ∫ x in Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2),
        f (x - (t : ℝ)) * (starRingEnd ℂ) (g x) := by
  rw [ccmComplexCorrelation]
  have hshift := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun x : ℝ => f (x - (t : ℝ)) * (starRingEnd ℂ) (g x)) (t : ℝ)
  rw [show (fun x : ℝ => f x * (starRingEnd ℂ) (g (x - -(t : ℝ)))) =
      fun x : ℝ =>
        (fun y : ℝ => f (y - (t : ℝ)) * (starRingEnd ℂ) (g y)) (x + (t : ℝ)) by
    funext x
    ring_nf]
  rw [hshift]
  have hfun :
      (fun x : ℝ => f (x - (t : ℝ)) * (starRingEnd ℂ) (g x)) =
        (Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2)).indicator
          (fun x : ℝ => f (x - (t : ℝ)) * (starRingEnd ℂ) (g x)) := by
    funext x
    by_cases hoverlap : x ∈ Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2)
    · rw [Set.indicator_of_mem hoverlap]
    · rw [Set.indicator_of_notMem hoverlap]
      by_cases hg : x ∈ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2)
      · have hf : x - (t : ℝ) ∉ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2) := by
          intro hxt
          apply hoverlap
          constructor <;> linarith [hg.1, hg.2, hxt.1, hxt.2, t.property.1]
        rw [f.zero_outside _ hf, zero_mul]
      · rw [g.zero_outside _ hg, map_zero, mul_zero]
  calc
    (∫ x : ℝ, f (x - (t : ℝ)) * (starRingEnd ℂ) (g x)) =
        ∫ x : ℝ,
          (Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2)).indicator
            (fun y : ℝ => f (y - (t : ℝ)) * (starRingEnd ℂ) (g y)) x :=
      congrArg (fun h : ℝ → ℂ => ∫ x : ℝ, h x) hfun
    _ = _ := MeasureTheory.integral_indicator (μ := volume)
      (f := fun x : ℝ => f (x - (t : ℝ)) * (starRingEnd ℂ) (g x)) measurableSet_Icc

/-- Lemma `polarize(i)`, support half: correlations of centered aperture functions vanish
outside `[-L,L]`. -/
theorem ccmRealCorrelation_centeredWindow_eq_zero
    (L : CCMPositiveAperture) (f g : CCMCenteredWindowFunction L)
    (t : CCMExteriorLag L) :
    ccmRealCorrelation f g (t : ℝ) = 0 := by
  rw [ccmRealCorrelation]
  have hfun : (fun x : ℝ => f x * g (x - (t : ℝ))) = fun _ => 0 := by
    funext x
    by_cases hx : x ∈ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2)
    · have hgt : x - (t : ℝ) ∉ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2) := by
        intro hxt
        rcases lt_abs.mp t.property with ht | ht
        · linarith [hx.1, hx.2, hxt.1, hxt.2]
        · linarith [hx.1, hx.2, hxt.1, hxt.2]
      rw [g.zero_outside _ hgt, mul_zero]
    · rw [f.zero_outside _ hx, zero_mul]
  rw [hfun, integral_zero]

/-- Lemma `polarize(i)`, positive-lag formula, on the exact overlap interval. -/
theorem ccmRealCorrelation_centeredWindow_eq_integral
    (L : CCMPositiveAperture) (f g : CCMCenteredWindowFunction L)
    (t : CCMApertureLag L) :
    ccmRealCorrelation f g (t : ℝ) =
      ∫ x in Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2),
        f x * g (x - (t : ℝ)) := by
  rw [ccmRealCorrelation]
  have hfun : (fun x : ℝ => f x * g (x - (t : ℝ))) =
      (Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2)).indicator
        (fun x : ℝ => f x * g (x - (t : ℝ))) := by
    funext x
    by_cases hoverlap : x ∈ Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2)
    · rw [Set.indicator_of_mem hoverlap]
    · rw [Set.indicator_of_notMem hoverlap]
      by_cases hx : x ∈ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2)
      · have hgt : x - (t : ℝ) ∉ Icc (-(L : ℝ) / 2) ((L : ℝ) / 2) := by
          intro hxt
          apply hoverlap
          constructor <;> linarith [hx.1, hx.2, hxt.1, hxt.2, t.property.1]
        rw [g.zero_outside _ hgt, mul_zero]
      · rw [f.zero_outside _ hx, zero_mul]
  calc
    (∫ x : ℝ, f x * g (x - (t : ℝ))) =
        ∫ x : ℝ,
          (Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2)).indicator
            (fun y : ℝ => f y * g (y - (t : ℝ))) x :=
      congrArg (fun h : ℝ → ℝ => ∫ x : ℝ, h x) hfun
    _ = _ := MeasureTheory.integral_indicator (μ := volume)
      (f := fun x : ℝ => f x * g (x - (t : ℝ))) measurableSet_Icc

/-- Lemma `polarize(i)`, negative-lag formula, on the same overlap interval. -/
theorem ccmRealCorrelation_centeredWindow_neg_eq_integral
    (L : CCMPositiveAperture) (f g : CCMCenteredWindowFunction L)
    (t : CCMApertureLag L) :
    ccmRealCorrelation f g (-(t : ℝ)) =
      ∫ x in Icc ((t : ℝ) - (L : ℝ) / 2) ((L : ℝ) / 2),
        f (x - (t : ℝ)) * g x := by
  rw [ccmRealCorrelation_neg, ccmRealCorrelation_centeredWindow_eq_integral L g f t]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

private theorem ccmRealCorrelation_neg_eq_neg_of_even_odd
    (f g : ℝ → ℝ) (hf : ∀ x, f (-x) = f x) (hg : ∀ x, g (-x) = -g x)
    (t : ℝ) :
    ccmRealCorrelation f g (-t) = -ccmRealCorrelation f g t := by
  rw [ccmRealCorrelation, ccmRealCorrelation]
  rw [show (fun x : ℝ => f x * g (x - -t)) =
      fun x : ℝ => f x * g (x + t) by funext x; ring_nf]
  calc
    (∫ x : ℝ, f x * g (x + t)) =
        ∫ x : ℝ, f (-x) * g (-x + t) := by
          symm
          exact integral_neg_eq_self (fun x : ℝ => f x * g (x + t)) volume
    _ = ∫ x : ℝ, -(f x * g (x - t)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hf, show -x + t = -(x - t) by ring, hg]
      ring
    _ = -(∫ x : ℝ, f x * g (x - t)) := by rw [integral_neg]

/-- Lemma `polarize(iii)`: the symmetrized correlation of a real even function with a real odd
function vanishes. -/
theorem ccmRealCorrelation_add_swap_eq_zero_of_even_odd
    (f g : ℝ → ℝ) (hf : ∀ x, f (-x) = f x) (hg : ∀ x, g (-x) = -g x)
    (t : ℝ) :
    ccmRealCorrelation f g t + ccmRealCorrelation g f t = 0 := by
  rw [← ccmRealCorrelation_neg f g t,
    ccmRealCorrelation_neg_eq_neg_of_even_odd f g hf hg t]
  ring

/-- Literal `polarize2(ii)`: every cosine/sine cross entry in the centered real Fourier basis
vanishes before applying the Weil functional. -/
theorem ccmCenteredCosineSineCorrelation_add_swap_eq_zero
    (L : CCMPositiveAperture) (m n : ℕ) (t : ℝ) :
    ccmRealCorrelation (ccmCenteredCosineMode L m)
        (ccmCenteredNegativeSineMode L n) t +
      ccmRealCorrelation (ccmCenteredNegativeSineMode L n)
        (ccmCenteredCosineMode L m) t = 0 :=
  ccmRealCorrelation_add_swap_eq_zero_of_even_odd _ _
    (ccmCenteredCosineMode_neg L m) (ccmCenteredNegativeSineMode_neg L n) t

end RHTower
