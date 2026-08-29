import GaloisForLFunctions.RHTower.ThetaTailFirstMomentDoubleLaplace
import GaloisForLFunctions.RHTower.ThetaTailSeparatedPacketPositivity
import GaloisForLFunctions.RHTower.HedenmalmThetaAllShiftedTails

/-!
# Separated real-packet positivity of the critical logarithmic-derivative kernel

On the real Euler ray the centered Xi function and its derivative are the bilateral Laplace
transform and first Laplace moment of the positive even theta-cusp source.  This module proves
explicit two-sided logarithmic bounds for the real-ray logarithmic derivative
`L(b) = ξ'/ξ(1/2 + b)` — namely `(log b)/8 ≤ L(b) ≤ log b + 1` beyond an explicit base — and
derives from them, by a scaled Gershgorin argument, unconditional positive semidefiniteness of
the critical logarithmic-derivative kernel `(L(x)+L(y))/(x+y)`, and hence of the theta tail
first-moment Bezoutian, on every finite real node packet with base at least `xiRayPacketBase`
and consecutive multiplicative ratio at least `xiRayPacketBase ^ 2`.  These are matrices of the
family whose positivity at all finite node systems of the cofinal Euler half-plane is
equivalent to the Riemann hypothesis.
-/

open Complex Real MeasureTheory Set
open scoped ComplexOrder

noncomputable section

namespace RHTower

open HedenmalmThetaSource

/-! ## The real-ray Laplace data of the theta-cusp source -/

/-- Real bilateral Laplace transform of the completed theta-cusp source. -/
def xiRayLaplace (b : ℝ) : ℝ := ∫ x : ℝ, thetaCuspFullSource x * Real.exp (b * x)

/-- First real bilateral Laplace moment of the completed theta-cusp source. -/
def xiRayLaplaceMoment (b : ℝ) : ℝ :=
  ∫ x : ℝ, x * thetaCuspFullSource x * Real.exp (b * x)

/-- The real-ray logarithmic derivative of the centered Xi function, as a Laplace quotient. -/
def xiRayLogDeriv (b : ℝ) : ℝ := xiRayLaplaceMoment b / xiRayLaplace b

theorem integrable_xiRayLaplace (b : ℝ) :
    Integrable (fun x : ℝ => thetaCuspFullSource x * Real.exp (b * x)) := by
  have h := HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource b
  apply h.congr
  filter_upwards with x
  exact mul_comm _ _

theorem integrable_xiRayLaplaceMoment (b : ℝ) :
    Integrable (fun x : ℝ => x * thetaCuspFullSource x * Real.exp (b * x)) := by
  have hmaj := integrable_abs_mul_exp_abs_mul_thetaCuspFullSource |b|
  apply Integrable.mono hmaj
  · exact ((continuous_id.mul contDiff_thetaCuspFullSource.continuous).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  · filter_upwards with x
    have hΦ : 0 ≤ thetaCuspFullSource x := (thetaCuspFullSource_pos x).le
    have habs : |x * thetaCuspFullSource x * Real.exp (b * x)| =
        |x| * thetaCuspFullSource x * Real.exp (b * x) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hΦ, abs_of_nonneg (Real.exp_pos _).le]
    have hmajnn : 0 ≤ |x| * Real.exp (|b| * |x|) * thetaCuspFullSource x :=
      mul_nonneg (mul_nonneg (abs_nonneg x) (Real.exp_pos _).le) hΦ
    rw [Real.norm_eq_abs, Real.norm_eq_abs, habs, abs_of_nonneg hmajnn]
    have he : Real.exp (b * x) ≤ Real.exp (|b| * |x|) := by
      apply Real.exp_le_exp.mpr
      calc b * x ≤ |b * x| := le_abs_self _
        _ = |b| * |x| := abs_mul b x
    calc |x| * thetaCuspFullSource x * Real.exp (b * x)
        = |x| * thetaCuspFullSource x * Real.exp (b * x) := rfl
      _ ≤ |x| * thetaCuspFullSource x * Real.exp (|b| * |x|) := by
          exact mul_le_mul_of_nonneg_left he (mul_nonneg (abs_nonneg x) hΦ)
      _ = |x| * Real.exp (|b| * |x|) * thetaCuspFullSource x := by ring

private theorem thetaEnvelope_pos' (x : ℝ) : 0 < thetaEnvelope x := by
  unfold HedenmalmThetaSource.thetaEnvelope
  exact mul_pos (Real.exp_pos _) (Real.exp_pos _)

private theorem laplace_integrand_nonneg (b x : ℝ) :
    0 ≤ thetaCuspFullSource x * Real.exp (b * x) :=
  mul_nonneg (thetaCuspFullSource_pos x).le (Real.exp_pos _).le

/-- Exponential floor for the real bilateral Laplace transform on the nonnegative ray. -/
theorem xiRayLaplace_ge {b : ℝ} (hb : 0 ≤ b) :
    thetaEnvelopeLower * thetaEnvelope 2 * Real.exp b ≤ xiRayLaplace b := by
  have hint := integrable_xiRayLaplace b
  have hpoint : ∀ x ∈ Ioc (1 : ℝ) 2,
      thetaEnvelopeLower * thetaEnvelope 2 * Real.exp b
        ≤ thetaCuspFullSource x * Real.exp (b * x) := by
    intro x hx
    have hx1 : 1 < x := hx.1
    have hx2 : x ≤ 2 := hx.2
    have hΦ : thetaEnvelopeLower * thetaEnvelope x ≤ thetaCuspFullSource x :=
      thetaCuspFullSource_ge_envelope (by linarith)
    have hE : thetaEnvelope 2 ≤ thetaEnvelope x := thetaEnvelope_le_of_le hx1.le hx2
    have he : Real.exp b ≤ Real.exp (b * x) := Real.exp_le_exp.mpr (by nlinarith)
    have h1 : thetaEnvelopeLower * thetaEnvelope 2 ≤ thetaEnvelopeLower * thetaEnvelope x :=
      mul_le_mul_of_nonneg_left hE thetaEnvelopeLower_pos.le
    have h0 : 0 ≤ thetaEnvelopeLower * thetaEnvelope 2 :=
      mul_nonneg thetaEnvelopeLower_pos.le (thetaEnvelope_pos' 2).le
    calc thetaEnvelopeLower * thetaEnvelope 2 * Real.exp b
        ≤ (thetaEnvelopeLower * thetaEnvelope x) * Real.exp (b * x) :=
          mul_le_mul h1 he (Real.exp_pos _).le (le_trans h0 h1)
      _ ≤ thetaCuspFullSource x * Real.exp (b * x) :=
          mul_le_mul_of_nonneg_right hΦ (Real.exp_pos _).le
  have hslab := MeasureTheory.setIntegral_ge_of_const_le measurableSet_Ioc
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) hpoint hint.integrableOn
  rw [MeasureTheory.measureReal_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2 - 1), smul_eq_mul] at hslab
  have hle := MeasureTheory.setIntegral_le_integral (s := Ioc (1 : ℝ) 2) hint
    (Filter.Eventually.of_forall fun x => laplace_integrand_nonneg b x)
  unfold xiRayLaplace
  nlinarith [hslab, hle]

theorem xiRayLaplace_pos {b : ℝ} (hb : 0 ≤ b) : 0 < xiRayLaplace b := by
  have h0 : 0 < thetaEnvelopeLower * thetaEnvelope 2 * Real.exp b :=
    mul_pos (mul_pos thetaEnvelopeLower_pos (thetaEnvelope_pos' 2)) (Real.exp_pos b)
  exact lt_of_lt_of_le h0 (xiRayLaplace_ge hb)

/-! ## Identification with the centered Xi function on the real ray -/

theorem xiCent_ofReal (b : ℝ) : xiCent (b : ℂ) = ((xiRayLaplace b : ℝ) : ℂ) := by
  rw [← thetaBilateralLaplace_eq_xiCent, thetaBilateralLaplace_eq_integral]
  have hfun : (fun x : ℝ => (thetaCuspFullSource x : ℂ) * Complex.exp ((b : ℂ) * (x : ℂ)))
      = fun x : ℝ => ((thetaCuspFullSource x * Real.exp (b * x) : ℝ) : ℂ) := by
    funext x
    rw [Complex.ofReal_mul, ← Complex.ofReal_mul b x, ← Complex.ofReal_exp]
  rw [hfun, integral_complex_ofReal]
  rfl

theorem deriv_xiCent_ofReal (b : ℝ) :
    deriv xiCent (b : ℂ) = ((xiRayLaplaceMoment b : ℝ) : ℂ) := by
  rw [← thetaBilateralLaplaceMoment_eq_deriv_xiCent]
  unfold thetaBilateralLaplaceMoment
  have hfun : (fun x : ℝ =>
      (x : ℂ) * (thetaCuspFullSource x : ℂ) * Complex.exp ((b : ℂ) * (x : ℂ)))
      = fun x : ℝ => ((x * thetaCuspFullSource x * Real.exp (b * x) : ℝ) : ℂ) := by
    funext x
    rw [Complex.ofReal_mul, Complex.ofReal_mul, ← Complex.ofReal_mul b x, ← Complex.ofReal_exp]
  rw [hfun, integral_complex_ofReal]
  rfl

/-- On the real ray the logarithmic derivative of the centered Xi function is the real
Laplace quotient of the theta-cusp source. -/
theorem logDeriv_xiCent_ofReal (b : ℝ) :
    logDeriv xiCent (b : ℂ) = ((xiRayLogDeriv b : ℝ) : ℂ) := by
  rw [logDeriv_apply, deriv_xiCent_ofReal, xiCent_ofReal]
  unfold xiRayLogDeriv
  rw [Complex.ofReal_div]

/-! ## The explicit constants -/

/-- Ratio of the two Hedenmalm envelope constants of the theta-cusp source. -/
def xiRayEnvelopeRatio : ℝ := thetaEnvelopeUpper / thetaEnvelopeLower

theorem one_le_xiRayEnvelopeRatio : 1 ≤ xiRayEnvelopeRatio := by
  have hE := thetaEnvelope_pos' 1
  have h1 := thetaCuspFullSource_ge_envelope (x := 1) one_pos
  have h2 := thetaCuspFullSource_le_envelope (x := 1) zero_le_one
  have hCl := thetaEnvelopeLower_pos
  unfold xiRayEnvelopeRatio
  rw [le_div_iff₀ hCl, one_mul]
  nlinarith

theorem xiRayEnvelopeRatio_pos : 0 < xiRayEnvelopeRatio :=
  lt_of_lt_of_le one_pos one_le_xiRayEnvelopeRatio

theorem thetaEnvelopeUpper_eq_ratio_mul :
    thetaEnvelopeUpper = xiRayEnvelopeRatio * thetaEnvelopeLower := by
  unfold xiRayEnvelopeRatio
  rw [div_mul_cancel₀ _ (ne_of_gt thetaEnvelopeLower_pos)]

/-- Base above which the upper logarithmic-derivative bound holds. -/
def xiRayUpperBase : ℝ := Real.pi * Real.exp 4 + Real.log xiRayEnvelopeRatio + 12

/-- Base above which the lower logarithmic-derivative bound holds. -/
def xiRayLowerBase : ℝ :=
  (2 * Real.pi) ^ 2 * Real.exp (2 * Real.exp 1 + 8)
    + 4 * Real.log (8 * xiRayEnvelopeRatio) + 16

/-- Packet base for the separated-packet positivity theorem. -/
def xiRayPacketBase : ℝ := xiRayUpperBase + xiRayLowerBase

private theorem two_le_exp_one' : (2 : ℝ) ≤ Real.exp 1 := by
  have := Real.exp_one_gt_d9
  linarith

private theorem log_nonneg_ratio8 : 0 ≤ Real.log (8 * xiRayEnvelopeRatio) :=
  Real.log_nonneg (by nlinarith [one_le_xiRayEnvelopeRatio])

private theorem xiRayUpperBase_ge : (12 : ℝ) ≤ xiRayUpperBase := by
  have h1 : 0 < Real.pi * Real.exp 4 := mul_pos Real.pi_pos (Real.exp_pos _)
  have h2 : 0 ≤ Real.log xiRayEnvelopeRatio := Real.log_nonneg one_le_xiRayEnvelopeRatio
  unfold xiRayUpperBase
  linarith

private theorem xiRayLowerBase_ge : (9216 : ℝ) ≤ xiRayLowerBase := by
  have h36 : (36 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  have h256 : (256 : ℝ) ≤ Real.exp (2 * Real.exp 1 + 8) := by
    have h8 : (8 : ℝ) ≤ 2 * Real.exp 1 + 8 := by nlinarith [Real.exp_pos 1]
    have hmono : Real.exp 8 ≤ Real.exp (2 * Real.exp 1 + 8) := Real.exp_le_exp.mpr h8
    have hpow : (2 : ℝ) ^ 8 ≤ (Real.exp 1) ^ 8 :=
      pow_le_pow_left₀ (by norm_num) two_le_exp_one' 8
    have hexp8 : (Real.exp 1) ^ 8 = Real.exp 8 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have : (256 : ℝ) = 2 ^ 8 := by norm_num
    linarith [hpow, hexp8 ▸ hpow]
  have hprod : (9216 : ℝ) ≤ (2 * Real.pi) ^ 2 * Real.exp (2 * Real.exp 1 + 8) := by
    have := mul_le_mul h36 h256 (by norm_num) (le_trans (by norm_num) h36)
    linarith
  have h2 := log_nonneg_ratio8
  unfold xiRayLowerBase
  linarith

theorem xiRayPacketBase_ge : (256 : ℝ) ≤ xiRayPacketBase := by
  have h1 := xiRayUpperBase_ge
  have h2 := xiRayLowerBase_ge
  unfold xiRayPacketBase
  linarith

private theorem xiRayUpperBase_le_packetBase : xiRayUpperBase ≤ xiRayPacketBase := by
  have := xiRayLowerBase_ge
  unfold xiRayPacketBase
  linarith

private theorem xiRayLowerBase_le_packetBase : xiRayLowerBase ≤ xiRayPacketBase := by
  have := xiRayUpperBase_ge
  unfold xiRayPacketBase
  linarith

/-! ## The upper logarithmic bound -/

/-- Beyond `xiRayUpperBase`, the real-ray logarithmic derivative of the centered Xi function
is at most `log b + 1`. -/
theorem xiRayLogDeriv_le {b : ℝ} (hb : xiRayUpperBase ≤ b) :
    xiRayLogDeriv b ≤ Real.log b + 1 := by
  have hγ1 := one_le_xiRayEnvelopeRatio
  have hlogγ : 0 ≤ Real.log xiRayEnvelopeRatio := Real.log_nonneg hγ1
  have hb12 : (12 : ℝ) ≤ b := le_trans xiRayUpperBase_ge hb
  have hb0 : (0 : ℝ) < b := by linarith
  set X := Real.log b with hXdef
  have hX1 : 1 ≤ X := by
    rw [hXdef, Real.le_log_iff_exp_le hb0]
    have := Real.exp_one_lt_d9
    linarith
  have hX0 : 0 < X := by linarith
  have hXb : X ≤ b - 1 := by
    rw [hXdef]
    exact Real.log_le_sub_one_of_pos hb0
  have hZpos : 0 < xiRayLaplace b := xiRayLaplace_pos hb0.le
  -- split the moment at X
  have hsplit : (∫ x in Iic X, x * thetaCuspFullSource x * Real.exp (b * x)) +
      (∫ x in Ioi X, x * thetaCuspFullSource x * Real.exp (b * x)) = xiRayLaplaceMoment b := by
    have h := MeasureTheory.integral_add_compl (measurableSet_Iic (a := X))
      (integrable_xiRayLaplaceMoment b)
    rwa [compl_Iic] at h
  -- left piece
  have hleft : (∫ x in Iic X, x * thetaCuspFullSource x * Real.exp (b * x))
      ≤ X * xiRayLaplace b := by
    have hmono : (∫ x in Iic X, x * thetaCuspFullSource x * Real.exp (b * x))
        ≤ ∫ x in Iic X, X * (thetaCuspFullSource x * Real.exp (b * x)) := by
      apply MeasureTheory.setIntegral_mono_on
        (integrable_xiRayLaplaceMoment b).integrableOn
        (((integrable_xiRayLaplace b).const_mul X).integrableOn)
        measurableSet_Iic
      intro x hx
      have hx' : x ≤ X := hx
      have h0 := laplace_integrand_nonneg b x
      calc x * thetaCuspFullSource x * Real.exp (b * x)
          = x * (thetaCuspFullSource x * Real.exp (b * x)) := by ring
        _ ≤ X * (thetaCuspFullSource x * Real.exp (b * x)) :=
            mul_le_mul_of_nonneg_right hx' h0
    have hXZ : (∫ x in Iic X, X * (thetaCuspFullSource x * Real.exp (b * x)))
        = X * ∫ x in Iic X, thetaCuspFullSource x * Real.exp (b * x) :=
      MeasureTheory.integral_const_mul _ _
    have hsub : (∫ x in Iic X, thetaCuspFullSource x * Real.exp (b * x)) ≤ xiRayLaplace b :=
      MeasureTheory.setIntegral_le_integral (integrable_xiRayLaplace b)
        (Filter.Eventually.of_forall fun x => laplace_integrand_nonneg b x)
    calc (∫ x in Iic X, x * thetaCuspFullSource x * Real.exp (b * x))
        ≤ X * ∫ x in Iic X, thetaCuspFullSource x * Real.exp (b * x) := by
          rw [← hXZ]; exact hmono
      _ ≤ X * xiRayLaplace b := mul_le_mul_of_nonneg_left hsub hX0.le
  -- tail piece
  have hb2 : Real.exp (2 * X) = b ^ 2 := by
    rw [hXdef, two_mul, Real.exp_add, Real.exp_log hb0]
    ring
  have hrate : b + 9 / 2 + 2 ≤ 2 * Real.pi * b ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have htailpoint : ∀ x ∈ Ioi X,
      x * thetaCuspFullSource x * Real.exp (b * x)
        ≤ (thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * (X + 1))
            * (Real.exp X * Real.exp (-x)) := by
    intro x hx
    have hxX : X < x := hx
    have hx0 : 0 < x := lt_trans hX0 hxX
    have hΦ := thetaCuspFullSource_le_envelope hx0.le
    -- exponent comparison
    have hexp2x : b ^ 2 * (1 + 2 * (x - X)) ≤ Real.exp (2 * x) := by
      have h1 : Real.exp (2 * x) = Real.exp (2 * X) * Real.exp (2 * (x - X)) := by
        rw [← Real.exp_add]; ring_nf
      have h2 : 1 + 2 * (x - X) ≤ Real.exp (2 * (x - X)) := by
        have := Real.add_one_le_exp (2 * (x - X))
        linarith
      rw [h1, hb2]
      exact mul_le_mul_of_nonneg_left h2 (sq_nonneg b)
    have hexponent : (b + 9 / 2) * x - Real.pi * Real.exp (2 * x)
        ≤ (b + 9 / 2) * X - Real.pi * b ^ 2 - (2 * Real.pi * b ^ 2 - (b + 9 / 2)) * (x - X) := by
      have hπ := Real.pi_pos
      nlinarith [hexp2x]
    -- collapse of the linear factor into a unit-rate exponential
    have hlin : x * Real.exp (-((2 * Real.pi * b ^ 2 - (b + 9 / 2)) * (x - X)))
        ≤ (X + 1) * Real.exp (-(x - X)) := by
      set u := x - X with hu
      have hu0 : 0 < u := by rw [hu]; linarith
      set r := 2 * Real.pi * b ^ 2 - (b + 9 / 2) with hr
      have hr2 : 2 ≤ r := by rw [hr]; linarith [hrate]
      have hx' : x = X + u := by rw [hu]; ring
      have h1 : X + u ≤ (X + 1) * (1 + u) := by nlinarith
      have h2 : (1 : ℝ) + u ≤ Real.exp u := by
        have := Real.add_one_le_exp u
        linarith
      have h3 : Real.exp u ≤ Real.exp ((r - 1) * u) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have h4 : X + u ≤ (X + 1) * Real.exp ((r - 1) * u) := by
        calc X + u ≤ (X + 1) * (1 + u) := h1
          _ ≤ (X + 1) * Real.exp u := mul_le_mul_of_nonneg_left h2 (by linarith)
          _ ≤ (X + 1) * Real.exp ((r - 1) * u) := mul_le_mul_of_nonneg_left h3 (by linarith)
      have h5 : (X + 1) * Real.exp ((r - 1) * u) * Real.exp (-(r * u))
          = (X + 1) * Real.exp (-u) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
      calc x * Real.exp (-(r * u))
          = (X + u) * Real.exp (-(r * u)) := by rw [hx']
        _ ≤ (X + 1) * Real.exp ((r - 1) * u) * Real.exp (-(r * u)) :=
            mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
        _ = (X + 1) * Real.exp (-u) := h5
    -- assemble
    have hΦe : x * thetaCuspFullSource x * Real.exp (b * x)
        ≤ thetaEnvelopeUpper * (x * Real.exp ((b + 9 / 2) * x - Real.pi * Real.exp (2 * x))) := by
      have hpack : thetaEnvelope x * Real.exp (b * x)
          = Real.exp ((b + 9 / 2) * x - Real.pi * Real.exp (2 * x)) := by
        unfold HedenmalmThetaSource.thetaEnvelope
        rw [← Real.exp_add, ← Real.exp_add]
        ring_nf
      have h1 : thetaCuspFullSource x * Real.exp (b * x)
          ≤ thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * x - Real.pi * Real.exp (2 * x)) := by
        rw [← hpack, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hΦ (Real.exp_pos _).le
      calc x * thetaCuspFullSource x * Real.exp (b * x)
          = x * (thetaCuspFullSource x * Real.exp (b * x)) := by ring
        _ ≤ x * (thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * x - Real.pi * Real.exp (2 * x))) :=
            mul_le_mul_of_nonneg_left h1 hx0.le
        _ = thetaEnvelopeUpper *
              (x * Real.exp ((b + 9 / 2) * x - Real.pi * Real.exp (2 * x))) := by ring
    have hCu : 0 ≤ thetaEnvelopeUpper := thetaEnvelopeUpper_pos.le
    have hmid : x * Real.exp ((b + 9 / 2) * x - Real.pi * Real.exp (2 * x))
        ≤ Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * ((X + 1) * Real.exp (-(x - X))) := by
      have h1 : Real.exp ((b + 9 / 2) * x - Real.pi * Real.exp (2 * x))
          ≤ Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2)
              * Real.exp (-((2 * Real.pi * b ^ 2 - (b + 9 / 2)) * (x - X))) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith [hexponent]
      calc x * Real.exp ((b + 9 / 2) * x - Real.pi * Real.exp (2 * x))
          ≤ x * (Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2)
              * Real.exp (-((2 * Real.pi * b ^ 2 - (b + 9 / 2)) * (x - X)))) :=
            mul_le_mul_of_nonneg_left h1 hx0.le
        _ = Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2)
              * (x * Real.exp (-((2 * Real.pi * b ^ 2 - (b + 9 / 2)) * (x - X)))) := by ring
        _ ≤ Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2)
              * ((X + 1) * Real.exp (-(x - X))) :=
            mul_le_mul_of_nonneg_left hlin (Real.exp_pos _).le
    have hExX : Real.exp (-(x - X)) = Real.exp X * Real.exp (-x) := by
      rw [← Real.exp_add]
      ring_nf
    calc x * thetaCuspFullSource x * Real.exp (b * x)
        ≤ thetaEnvelopeUpper *
            (x * Real.exp ((b + 9 / 2) * x - Real.pi * Real.exp (2 * x))) := hΦe
      _ ≤ thetaEnvelopeUpper * (Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2)
            * ((X + 1) * Real.exp (-(x - X)))) :=
          mul_le_mul_of_nonneg_left hmid hCu
      _ = (thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * (X + 1))
            * (Real.exp X * Real.exp (-x)) := by rw [hExX]; ring
  have hmajint : IntegrableOn
      (fun x : ℝ => (thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * (X + 1))
        * (Real.exp X * Real.exp (-x))) (Ioi X) := by
    have h1 : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi X) := by
      have h0 := integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) X
      exact MeasureTheory.IntegrableOn.congr_fun h0
        (fun x _ => by simp only [neg_one_mul]) measurableSet_Ioi
    exact ((h1.const_mul _).const_mul _)
  have htail : (∫ x in Ioi X, x * thetaCuspFullSource x * Real.exp (b * x))
      ≤ thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * (X + 1) := by
    have hTle := MeasureTheory.setIntegral_mono_on
      (integrable_xiRayLaplaceMoment b).integrableOn hmajint measurableSet_Ioi htailpoint
    have hval : (∫ x in Ioi X,
        (thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * (X + 1))
          * (Real.exp X * Real.exp (-x)))
        = thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * (X + 1) := by
      rw [MeasureTheory.integral_const_mul]
      have h2 : (∫ x in Ioi X, Real.exp X * Real.exp (-x))
          = Real.exp X * ∫ x in Ioi X, Real.exp (-x) :=
        MeasureTheory.integral_const_mul _ _
      rw [h2, integral_exp_neg_Ioi, ← Real.exp_add]
      simp
    rw [hval] at hTle
    exact hTle
  -- tail is below the Laplace floor
  have hTZ : thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * (X + 1)
      ≤ xiRayLaplace b := by
    have hfloor := xiRayLaplace_ge hb0.le
    have hE2 : thetaEnvelope 2 = Real.exp (9 - Real.pi * Real.exp 4) := by
      unfold HedenmalmThetaSource.thetaEnvelope
      rw [← Real.exp_add]
      norm_num
      ring_nf
    have hXe : X + 1 ≤ Real.exp X := by
      have := Real.add_one_le_exp X
      linarith
    have hCuγ : thetaEnvelopeUpper = xiRayEnvelopeRatio * thetaEnvelopeLower :=
      thetaEnvelopeUpper_eq_ratio_mul
    have hexpineq : Real.log xiRayEnvelopeRatio + ((b + 9 / 2) * X - Real.pi * b ^ 2 + X)
        ≤ 9 - Real.pi * Real.exp 4 + b := by
      have h1 : (b + 9 / 2 + 1) * X ≤ 2 * b * (b - 1) := by nlinarith
      have h2 : 3 * b ^ 2 ≤ Real.pi * b ^ 2 := by nlinarith [Real.pi_gt_three, sq_nonneg b]
      have h3 : Real.pi * Real.exp 4 + Real.log xiRayEnvelopeRatio ≤ b - 12 := by
        have : xiRayUpperBase = Real.pi * Real.exp 4 + Real.log xiRayEnvelopeRatio + 12 := rfl
        linarith [hb]
      nlinarith [sq_nonneg b]
    have hchain : thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * (X + 1)
        ≤ thetaEnvelopeLower * thetaEnvelope 2 * Real.exp b := by
      have hLHS : thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * (X + 1)
          ≤ thetaEnvelopeLower *
              (Real.exp (Real.log xiRayEnvelopeRatio)
                * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * Real.exp X) := by
        rw [hCuγ, Real.exp_log xiRayEnvelopeRatio_pos]
        have h0 : 0 ≤ xiRayEnvelopeRatio * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) :=
          mul_nonneg (xiRayEnvelopeRatio_pos).le (Real.exp_pos _).le
        calc xiRayEnvelopeRatio * thetaEnvelopeLower
              * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * (X + 1)
            ≤ xiRayEnvelopeRatio * thetaEnvelopeLower
              * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * Real.exp X := by
              apply mul_le_mul_of_nonneg_left hXe
              have := thetaEnvelopeLower_pos
              nlinarith [xiRayEnvelopeRatio_pos, Real.exp_pos ((b + 9 / 2) * X - Real.pi * b ^ 2)]
          _ = thetaEnvelopeLower * (xiRayEnvelopeRatio
              * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * Real.exp X) := by ring
      have hpack : Real.exp (Real.log xiRayEnvelopeRatio)
          * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * Real.exp X
          = Real.exp (Real.log xiRayEnvelopeRatio
              + ((b + 9 / 2) * X - Real.pi * b ^ 2 + X)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        ring_nf
      have hRHS : Real.exp (Real.log xiRayEnvelopeRatio
          + ((b + 9 / 2) * X - Real.pi * b ^ 2 + X)) ≤ Real.exp (9 - Real.pi * Real.exp 4 + b) :=
        Real.exp_le_exp.mpr hexpineq
      have hfin : thetaEnvelopeLower * thetaEnvelope 2 * Real.exp b
          = thetaEnvelopeLower * Real.exp (9 - Real.pi * Real.exp 4 + b) := by
        rw [hE2, mul_assoc]
        simp only [← Real.exp_add]
      calc thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * (X + 1)
          ≤ thetaEnvelopeLower *
              (Real.exp (Real.log xiRayEnvelopeRatio)
                * Real.exp ((b + 9 / 2) * X - Real.pi * b ^ 2) * Real.exp X) := hLHS
        _ = thetaEnvelopeLower * Real.exp (Real.log xiRayEnvelopeRatio
              + ((b + 9 / 2) * X - Real.pi * b ^ 2 + X)) := by rw [hpack]
        _ ≤ thetaEnvelopeLower * Real.exp (9 - Real.pi * Real.exp 4 + b) :=
            mul_le_mul_of_nonneg_left hRHS thetaEnvelopeLower_pos.le
        _ = thetaEnvelopeLower * thetaEnvelope 2 * Real.exp b := hfin.symm
    linarith
  -- conclude
  unfold xiRayLogDeriv
  rw [div_le_iff₀ hZpos]
  have hN : xiRayLaplaceMoment b ≤ X * xiRayLaplace b + xiRayLaplace b := by
    linarith [hsplit, hleft, htail, hTZ]
  linarith [hN]

/-! ## The lower logarithmic bound -/

private theorem log_le_div_exp {b : ℝ} (hb : 0 < b) : Real.log b ≤ b / Real.exp 1 := by
  have hpos : 0 < b / Real.exp 1 := div_pos hb (Real.exp_pos 1)
  have h := Real.log_le_sub_one_of_pos hpos
  rw [Real.log_div (ne_of_gt hb) (Real.exp_ne_zero 1), Real.log_exp] at h
  linarith

private theorem moment_reflected_le {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi (0 : ℝ), x * thetaCuspFullSource x * Real.exp (-(b * x))
      ≤ thetaEnvelopeUpper := by
  have hrate : (0 : ℝ) < 2 * Real.pi - 11 / 2 := by nlinarith [Real.pi_gt_three]
  have hpoint : ∀ x ∈ Ioi (0 : ℝ), x * thetaCuspFullSource x * Real.exp (-(b * x))
      ≤ (thetaEnvelopeUpper * Real.exp (-Real.pi))
          * Real.exp (-((2 * Real.pi - 11 / 2) * x)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hΦ := thetaCuspFullSource_le_envelope hx0.le
    have hone : Real.exp (-(b * x)) ≤ 1 := by
      have h := Real.exp_le_exp.mpr (show -(b * x) ≤ 0 by nlinarith)
      rwa [Real.exp_zero] at h
    have hxe : x ≤ Real.exp x := by
      have := Real.add_one_le_exp x
      linarith
    have h2x : 1 + 2 * x ≤ Real.exp (2 * x) := by
      have := Real.add_one_le_exp (2 * x)
      linarith
    have hxE : x * thetaEnvelope x
        ≤ Real.exp (-Real.pi) * Real.exp (-((2 * Real.pi - 11 / 2) * x)) := by
      unfold HedenmalmThetaSource.thetaEnvelope
      have hEbound : Real.exp (-Real.pi * Real.exp (2 * x))
          ≤ Real.exp (-Real.pi * (1 + 2 * x)) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      calc x * (Real.exp (9 * x / 2) * Real.exp (-Real.pi * Real.exp (2 * x)))
          ≤ Real.exp x * (Real.exp (9 * x / 2) * Real.exp (-Real.pi * (1 + 2 * x))) := by
            apply mul_le_mul hxe
            · exact mul_le_mul_of_nonneg_left hEbound (Real.exp_pos _).le
            · exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
            · exact (Real.exp_pos _).le
        _ = Real.exp (-Real.pi) * Real.exp (-((2 * Real.pi - 11 / 2) * x)) := by
            simp only [← Real.exp_add]
            ring_nf
    calc x * thetaCuspFullSource x * Real.exp (-(b * x))
        ≤ x * thetaCuspFullSource x * 1 := by
          apply mul_le_mul_of_nonneg_left hone
          exact mul_nonneg hx0.le (thetaCuspFullSource_pos x).le
      _ = x * thetaCuspFullSource x := by ring
      _ ≤ x * (thetaEnvelopeUpper * thetaEnvelope x) :=
          mul_le_mul_of_nonneg_left hΦ hx0.le
      _ = thetaEnvelopeUpper * (x * thetaEnvelope x) := by ring
      _ ≤ thetaEnvelopeUpper * (Real.exp (-Real.pi)
            * Real.exp (-((2 * Real.pi - 11 / 2) * x))) :=
          mul_le_mul_of_nonneg_left hxE thetaEnvelopeUpper_pos.le
      _ = (thetaEnvelopeUpper * Real.exp (-Real.pi))
            * Real.exp (-((2 * Real.pi - 11 / 2) * x)) := by ring
  have hmajint : IntegrableOn
      (fun x : ℝ => (thetaEnvelopeUpper * Real.exp (-Real.pi))
        * Real.exp (-((2 * Real.pi - 11 / 2) * x))) (Ioi (0 : ℝ)) := by
    have h1 : IntegrableOn (fun x : ℝ => Real.exp (-(2 * Real.pi - 11 / 2) * x))
        (Ioi (0 : ℝ)) :=
      integrableOn_exp_mul_Ioi (by linarith) 0
    exact MeasureTheory.IntegrableOn.congr_fun
      (h1.const_mul (thetaEnvelopeUpper * Real.exp (-Real.pi)))
      (fun x _ => by simp only [neg_mul]) measurableSet_Ioi
  have hint := MeasureTheory.setIntegral_mono_on
    ((integrable_xiRayLaplaceMoment (-b)).congr (by
      filter_upwards with x
      rw [neg_mul])).integrableOn
    hmajint measurableSet_Ioi hpoint
  have hval : (∫ x in Ioi (0 : ℝ), (thetaEnvelopeUpper * Real.exp (-Real.pi))
      * Real.exp (-((2 * Real.pi - 11 / 2) * x)))
      = (thetaEnvelopeUpper * Real.exp (-Real.pi)) * (1 / (2 * Real.pi - 11 / 2)) := by
    rw [MeasureTheory.integral_const_mul]
    have h2 : (∫ x in Ioi (0 : ℝ), Real.exp (-((2 * Real.pi - 11 / 2) * x)))
        = 1 / (2 * Real.pi - 11 / 2) := by
      have h3 := integral_exp_mul_Ioi (a := -(2 * Real.pi - 11 / 2)) (by linarith) 0
      have h4 : (∫ x in Ioi (0 : ℝ), Real.exp (-((2 * Real.pi - 11 / 2) * x)))
          = ∫ x in Ioi (0 : ℝ), Real.exp (-(2 * Real.pi - 11 / 2) * x) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro x _
        simp only [neg_mul]
      rw [h4, h3]
      rw [mul_zero, Real.exp_zero]
      field_simp
    rw [h2]
  have hsmall : (thetaEnvelopeUpper * Real.exp (-Real.pi)) * (1 / (2 * Real.pi - 11 / 2))
      ≤ thetaEnvelopeUpper := by
    have he3 : Real.exp (-Real.pi) ≤ 1 / 8 := by
      have h1 : Real.exp (-Real.pi) ≤ Real.exp (-3) :=
        Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three])
      have h2 : Real.exp (-3) = 1 / Real.exp 3 := by
        rw [Real.exp_neg]
        ring
      have h3 : (8 : ℝ) ≤ Real.exp 3 := by
        have hpow : (2 : ℝ) ^ 3 ≤ (Real.exp 1) ^ 3 :=
          pow_le_pow_left₀ (by norm_num) two_le_exp_one' 3
        have hexp3 : (Real.exp 1) ^ 3 = Real.exp 3 := by
          rw [← Real.exp_nat_mul]
          norm_num
        have : (8 : ℝ) = 2 ^ 3 := by norm_num
        linarith [hexp3 ▸ hpow]
      have h4 : 1 / Real.exp 3 ≤ 1 / 8 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) h3
      linarith [h1, h2 ▸ h1]
    have hrate8 : 1 / (2 * Real.pi - 11 / 2) ≤ 8 := by
      rw [div_le_iff₀ hrate]
      nlinarith [Real.pi_gt_three]
    have hCu := thetaEnvelopeUpper_pos
    calc (thetaEnvelopeUpper * Real.exp (-Real.pi)) * (1 / (2 * Real.pi - 11 / 2))
        ≤ (thetaEnvelopeUpper * (1 / 8)) * 8 := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left he3 hCu.le
          · exact hrate8
          · positivity
          · nlinarith [he3, Real.exp_pos (-Real.pi)]
      _ = thetaEnvelopeUpper := by ring
  have hcongr : (∫ x in Ioi (0 : ℝ), x * thetaCuspFullSource x * Real.exp (-(b * x)))
      = ∫ x in Ioi (0 : ℝ), x * thetaCuspFullSource x * Real.exp (-b * x) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _
    simp only [neg_mul]
  rw [hcongr]
  calc (∫ x in Ioi (0 : ℝ), x * thetaCuspFullSource x * Real.exp (-b * x))
      ≤ ∫ x in Ioi (0 : ℝ), (thetaEnvelopeUpper * Real.exp (-Real.pi))
          * Real.exp (-((2 * Real.pi - 11 / 2) * x)) := by
        have hcongr2 : (∫ x in Ioi (0 : ℝ), x * thetaCuspFullSource x * Real.exp (-b * x))
            = ∫ x in Ioi (0 : ℝ), x * thetaCuspFullSource x * Real.exp (-(b * x)) := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          intro x _
          simp only [neg_mul]
        rw [hcongr2]
        exact hint
    _ = (thetaEnvelopeUpper * Real.exp (-Real.pi)) * (1 / (2 * Real.pi - 11 / 2)) := hval
    _ ≤ thetaEnvelopeUpper := hsmall

private theorem mass_reflected_le {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi (0 : ℝ), thetaCuspFullSource x * Real.exp (-(b * x)) ≤ thetaEnvelopeUpper := by
  have hrate : (0 : ℝ) < 2 * Real.pi - 11 / 2 := by nlinarith [Real.pi_gt_three]
  have hpoint : ∀ x ∈ Ioi (0 : ℝ), thetaCuspFullSource x * Real.exp (-(b * x))
      ≤ x * thetaCuspFullSource x * Real.exp (-(b * x)) + thetaCuspFullSource x
          * Real.exp (-(b * x)) := by
    intro x hx
    have h := mul_nonneg (mul_nonneg (le_of_lt hx) (thetaCuspFullSource_pos x).le)
      (Real.exp_pos (-(b * x))).le
    linarith
  -- direct pointwise route instead: Φ e^{-bx} ≤ C_u e^{-π} e^{-(2π-9/2)x}, integrate
  have hrate9 : (0 : ℝ) < 2 * Real.pi - 9 / 2 := by nlinarith [Real.pi_gt_three]
  have hpoint2 : ∀ x ∈ Ioi (0 : ℝ), thetaCuspFullSource x * Real.exp (-(b * x))
      ≤ (thetaEnvelopeUpper * Real.exp (-Real.pi))
          * Real.exp (-((2 * Real.pi - 9 / 2) * x)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hΦ := thetaCuspFullSource_le_envelope hx0.le
    have hone : Real.exp (-(b * x)) ≤ 1 := by
      have h := Real.exp_le_exp.mpr (show -(b * x) ≤ 0 by nlinarith)
      rwa [Real.exp_zero] at h
    have h2x : 1 + 2 * x ≤ Real.exp (2 * x) := by
      have := Real.add_one_le_exp (2 * x)
      linarith
    have hE : thetaEnvelope x
        ≤ Real.exp (-Real.pi) * Real.exp (-((2 * Real.pi - 9 / 2) * x)) := by
      unfold HedenmalmThetaSource.thetaEnvelope
      have hEbound : Real.exp (-Real.pi * Real.exp (2 * x))
          ≤ Real.exp (-Real.pi * (1 + 2 * x)) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      calc Real.exp (9 * x / 2) * Real.exp (-Real.pi * Real.exp (2 * x))
          ≤ Real.exp (9 * x / 2) * Real.exp (-Real.pi * (1 + 2 * x)) :=
            mul_le_mul_of_nonneg_left hEbound (Real.exp_pos _).le
        _ = Real.exp (-Real.pi) * Real.exp (-((2 * Real.pi - 9 / 2) * x)) := by
            simp only [← Real.exp_add]
            ring_nf
    calc thetaCuspFullSource x * Real.exp (-(b * x))
        ≤ thetaCuspFullSource x * 1 :=
          mul_le_mul_of_nonneg_left hone (thetaCuspFullSource_pos x).le
      _ = thetaCuspFullSource x := by ring
      _ ≤ thetaEnvelopeUpper * thetaEnvelope x := hΦ
      _ ≤ thetaEnvelopeUpper * (Real.exp (-Real.pi)
            * Real.exp (-((2 * Real.pi - 9 / 2) * x))) :=
          mul_le_mul_of_nonneg_left hE thetaEnvelopeUpper_pos.le
      _ = (thetaEnvelopeUpper * Real.exp (-Real.pi))
            * Real.exp (-((2 * Real.pi - 9 / 2) * x)) := by ring
  have hmajint : IntegrableOn
      (fun x : ℝ => (thetaEnvelopeUpper * Real.exp (-Real.pi))
        * Real.exp (-((2 * Real.pi - 9 / 2) * x))) (Ioi (0 : ℝ)) := by
    have h1 : IntegrableOn (fun x : ℝ => Real.exp (-(2 * Real.pi - 9 / 2) * x))
        (Ioi (0 : ℝ)) :=
      integrableOn_exp_mul_Ioi (by linarith) 0
    exact MeasureTheory.IntegrableOn.congr_fun
      (h1.const_mul (thetaEnvelopeUpper * Real.exp (-Real.pi)))
      (fun x _ => by simp only [neg_mul]) measurableSet_Ioi
  have hint := MeasureTheory.setIntegral_mono_on
    ((integrable_xiRayLaplace (-b)).congr (by
      filter_upwards with x
      rw [neg_mul])).integrableOn
    hmajint measurableSet_Ioi hpoint2
  have hval : (∫ x in Ioi (0 : ℝ), (thetaEnvelopeUpper * Real.exp (-Real.pi))
      * Real.exp (-((2 * Real.pi - 9 / 2) * x)))
      = (thetaEnvelopeUpper * Real.exp (-Real.pi)) * (1 / (2 * Real.pi - 9 / 2)) := by
    rw [MeasureTheory.integral_const_mul]
    have h2 : (∫ x in Ioi (0 : ℝ), Real.exp (-((2 * Real.pi - 9 / 2) * x)))
        = 1 / (2 * Real.pi - 9 / 2) := by
      have h3 := integral_exp_mul_Ioi (a := -(2 * Real.pi - 9 / 2)) (by linarith) 0
      have h4 : (∫ x in Ioi (0 : ℝ), Real.exp (-((2 * Real.pi - 9 / 2) * x)))
          = ∫ x in Ioi (0 : ℝ), Real.exp (-(2 * Real.pi - 9 / 2) * x) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro x _
        simp only [neg_mul]
      rw [h4, h3, mul_zero, Real.exp_zero]
      field_simp
    rw [h2]
  have hsmall : (thetaEnvelopeUpper * Real.exp (-Real.pi)) * (1 / (2 * Real.pi - 9 / 2))
      ≤ thetaEnvelopeUpper := by
    have he3 : Real.exp (-Real.pi) ≤ 1 / 8 := by
      have h1 : Real.exp (-Real.pi) ≤ Real.exp (-3) :=
        Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three])
      have h2 : Real.exp (-3) = 1 / Real.exp 3 := by
        rw [Real.exp_neg]
        ring
      have h3 : (8 : ℝ) ≤ Real.exp 3 := by
        have hpow : (2 : ℝ) ^ 3 ≤ (Real.exp 1) ^ 3 :=
          pow_le_pow_left₀ (by norm_num) two_le_exp_one' 3
        have hexp3 : (Real.exp 1) ^ 3 = Real.exp 3 := by
          rw [← Real.exp_nat_mul]
          norm_num
        have : (8 : ℝ) = 2 ^ 3 := by norm_num
        linarith [hexp3 ▸ hpow]
      have h4 : 1 / Real.exp 3 ≤ 1 / 8 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) h3
      linarith [h1, h2 ▸ h1]
    have hrate8 : 1 / (2 * Real.pi - 9 / 2) ≤ 8 := by
      rw [div_le_iff₀ hrate9]
      nlinarith [Real.pi_gt_three]
    have hCu := thetaEnvelopeUpper_pos
    calc (thetaEnvelopeUpper * Real.exp (-Real.pi)) * (1 / (2 * Real.pi - 9 / 2))
        ≤ (thetaEnvelopeUpper * (1 / 8)) * 8 := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left he3 hCu.le
          · exact hrate8
          · positivity
          · nlinarith [he3, Real.exp_pos (-Real.pi)]
      _ = thetaEnvelopeUpper := by ring
  calc (∫ x in Ioi (0 : ℝ), thetaCuspFullSource x * Real.exp (-(b * x)))
      ≤ ∫ x in Ioi (0 : ℝ), (thetaEnvelopeUpper * Real.exp (-Real.pi))
          * Real.exp (-((2 * Real.pi - 9 / 2) * x)) := hint
    _ = (thetaEnvelopeUpper * Real.exp (-Real.pi)) * (1 / (2 * Real.pi - 9 / 2)) := hval
    _ ≤ thetaEnvelopeUpper := hsmall

private theorem moment_even_split (b : ℝ) :
    xiRayLaplaceMoment b
      = (∫ x in Ioi (0 : ℝ), x * thetaCuspFullSource x * Real.exp (b * x))
        - ∫ x in Ioi (0 : ℝ), x * thetaCuspFullSource x * Real.exp (-(b * x)) := by
  have hsplit := MeasureTheory.integral_add_compl (measurableSet_Ioi (a := (0 : ℝ)))
    (integrable_xiRayLaplaceMoment b)
  rw [compl_Ioi] at hsplit
  have hreflect : (∫ x in Iic (0 : ℝ), x * thetaCuspFullSource x * Real.exp (b * x))
      = - ∫ x in Ioi (0 : ℝ), x * thetaCuspFullSource x * Real.exp (-(b * x)) := by
    have h := integral_comp_neg_Iic (0 : ℝ)
      (fun u => -(u * thetaCuspFullSource u * Real.exp (-(b * u))))
    have hL : (fun x : ℝ => -((-x) * thetaCuspFullSource (-x) * Real.exp (-(b * -x))))
        = fun x : ℝ => x * thetaCuspFullSource x * Real.exp (b * x) := by
      funext x
      rw [thetaCuspFullSource_neg]
      ring_nf
    rw [neg_zero] at h
    calc (∫ x in Iic (0 : ℝ), x * thetaCuspFullSource x * Real.exp (b * x))
        = ∫ x in Iic (0 : ℝ),
            -((-x) * thetaCuspFullSource (-x) * Real.exp (-(b * -x))) := by
          rw [hL]
      _ = ∫ u in Ioi (0 : ℝ), -(u * thetaCuspFullSource u * Real.exp (-(b * u))) := h
      _ = - ∫ u in Ioi (0 : ℝ), u * thetaCuspFullSource u * Real.exp (-(b * u)) :=
          MeasureTheory.integral_neg _
  unfold xiRayLaplaceMoment
  linarith [hsplit, hreflect]

private theorem laplace_even_split (b : ℝ) :
    xiRayLaplace b
      = (∫ x in Ioi (0 : ℝ), thetaCuspFullSource x * Real.exp (b * x))
        + ∫ x in Ioi (0 : ℝ), thetaCuspFullSource x * Real.exp (-(b * x)) := by
  have hsplit := MeasureTheory.integral_add_compl (measurableSet_Ioi (a := (0 : ℝ)))
    (integrable_xiRayLaplace b)
  rw [compl_Ioi] at hsplit
  have hreflect : (∫ x in Iic (0 : ℝ), thetaCuspFullSource x * Real.exp (b * x))
      = ∫ x in Ioi (0 : ℝ), thetaCuspFullSource x * Real.exp (-(b * x)) := by
    have h := integral_comp_neg_Iic (0 : ℝ)
      (fun u => thetaCuspFullSource u * Real.exp (-(b * u)))
    have hL : (fun x : ℝ => thetaCuspFullSource (-x) * Real.exp (-(b * -x)))
        = fun x : ℝ => thetaCuspFullSource x * Real.exp (b * x) := by
      funext x
      rw [thetaCuspFullSource_neg]
      ring_nf
    rw [neg_zero] at h
    calc (∫ x in Iic (0 : ℝ), thetaCuspFullSource x * Real.exp (b * x))
        = ∫ x in Iic (0 : ℝ), thetaCuspFullSource (-x) * Real.exp (-(b * -x)) := by
          rw [hL]
      _ = ∫ u in Ioi (0 : ℝ), thetaCuspFullSource u * Real.exp (-(b * u)) := h
  unfold xiRayLaplace
  linarith [hsplit, hreflect]

set_option maxHeartbeats 1600000 in
/-- Beyond `xiRayLowerBase`, the real-ray logarithmic derivative of the centered Xi function
is at least `(log b)/8`. -/
theorem xiRayLogDeriv_ge {b : ℝ} (hb : xiRayLowerBase ≤ b) :
    Real.log b / 8 ≤ xiRayLogDeriv b := by
  have hγ1 := one_le_xiRayEnvelopeRatio
  have hγ0 := xiRayEnvelopeRatio_pos
  have hCl := thetaEnvelopeLower_pos
  have hCu := thetaEnvelopeUpper_pos
  have hexp1 : (2 : ℝ) ≤ Real.exp 1 := two_le_exp_one'
  have h2π0 : (0 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hBpos : (0 : ℝ) < (2 * Real.pi) ^ 2 * Real.exp (2 * Real.exp 1 + 8) :=
    mul_pos (by positivity) (Real.exp_pos _)
  have hB : (2 * Real.pi) ^ 2 * Real.exp (2 * Real.exp 1 + 8) ≤ b := by
    have h1 := log_nonneg_ratio8
    unfold xiRayLowerBase at hb
    linarith
  have hb9216 : (9216 : ℝ) ≤ b := le_trans xiRayLowerBase_ge hb
  have hb0 : (0 : ℝ) < b := by linarith
  set L := Real.log b with hLdef
  clear_value L
  have hlog2π0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hL8 : 2 * Real.log (2 * Real.pi) + 2 * Real.exp 1 + 8 ≤ L := by
    have h1 : Real.log ((2 * Real.pi) ^ 2 * Real.exp (2 * Real.exp 1 + 8)) ≤ L := by
      rw [hLdef]
      exact Real.log_le_log hBpos hB
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp] at h1
    push_cast at h1
    linarith
  have hL12 : (12 : ℝ) ≤ L := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  set Y := L / 4 with hYdef
  clear_value Y
  have hY2 : (2 : ℝ) ≤ Y := by rw [hYdef]; linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hLb : L ≤ b / 2 := by
    have h1 := log_le_div_exp hb0
    have h2 : b / Real.exp 1 ≤ b / 2 :=
      div_le_div_of_nonneg_left hb0.le (by norm_num) hexp1
    rw [hLdef]
    linarith
  have hlog8γb : Real.log (8 * xiRayEnvelopeRatio) ≤ b / 4 := by
    have h1 := log_nonneg_ratio8
    unfold xiRayLowerBase at hb
    linarith
  set c := b + 9 / 2 with hcdef
  clear_value c
  set x₂ := Real.log (b / (2 * Real.pi)) / 2 with hx₂def
  clear_value x₂
  have hb2π : (0 : ℝ) < b / (2 * Real.pi) := div_pos hb0 h2π0
  have hlogb2π : Real.log (b / (2 * Real.pi)) = L - Real.log (2 * Real.pi) := by
    rw [hLdef, Real.log_div (ne_of_gt hb0) (ne_of_gt h2π0)]
  have he2x₂ : Real.exp (2 * x₂) = b / (2 * Real.pi) := by
    rw [hx₂def, show 2 * (Real.log (b / (2 * Real.pi)) / 2)
      = Real.log (b / (2 * Real.pi)) by ring]
    exact Real.exp_log hb2π
  have hx₂1 : 1 ≤ x₂ := by
    rw [hx₂def, hlogb2π]
    linarith
  have hx₂e : Real.exp 1 / 2 + 1 ≤ x₂ := by
    rw [hx₂def, hlogb2π]
    linarith
  set A : ℝ := ∫ x in Ioi (0 : ℝ), x * thetaCuspFullSource x * Real.exp (b * x) with hAdef
  set A' : ℝ := ∫ x in Ioi (0 : ℝ), x * thetaCuspFullSource x * Real.exp (-(b * x)) with hA'def
  set Zp : ℝ := ∫ x in Ioi (0 : ℝ), thetaCuspFullSource x * Real.exp (b * x) with hZpdef
  set Z' : ℝ := ∫ x in Ioi (0 : ℝ), thetaCuspFullSource x * Real.exp (-(b * x)) with hZ'def
  clear_value A A' Zp Z'
  have hA'le : A' ≤ thetaEnvelopeUpper := by
    rw [hA'def]; exact moment_reflected_le hb0
  have hZ'le : Z' ≤ thetaEnvelopeUpper := by
    rw [hZ'def]; exact mass_reflected_le hb0
  have hNsplit : xiRayLaplaceMoment b = A - A' := by
    rw [hAdef, hA'def]; exact moment_even_split b
  have hZsplit : xiRayLaplace b = Zp + Z' := by
    rw [hZpdef, hZ'def]; exact laplace_even_split b
  have hintZp : IntegrableOn (fun x : ℝ => thetaCuspFullSource x * Real.exp (b * x))
      (Ioi (0 : ℝ)) := (integrable_xiRayLaplace b).integrableOn
  have hintA : IntegrableOn (fun x : ℝ => x * thetaCuspFullSource x * Real.exp (b * x))
      (Ioi (0 : ℝ)) := (integrable_xiRayLaplaceMoment b).integrableOn
  have hIoiu : Ioc (0 : ℝ) Y ∪ Ioi Y = Ioi 0 := Ioc_union_Ioi_eq_Ioi hY0.le
  have hdisj : Disjoint (Ioc (0 : ℝ) Y) (Ioi Y) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    exact absurd ht.2 (not_le.mpr ht')
  set S : ℝ := ∫ x in Ioc (0 : ℝ) Y, thetaCuspFullSource x * Real.exp (b * x) with hSdef
  clear_value S
  have hS0 : 0 ≤ S := by
    rw [hSdef]
    exact setIntegral_nonneg measurableSet_Ioc fun x _ => laplace_integrand_nonneg b x
  have hZpsplit : S + (∫ x in Ioi Y, thetaCuspFullSource x * Real.exp (b * x)) = Zp := by
    rw [hSdef, hZpdef, ← hIoiu, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
      (hintZp.mono_set (by rw [← hIoiu]; exact subset_union_left))
      (hintZp.mono_set (by rw [← hIoiu]; exact subset_union_right))]
  have hA2 : Y * (Zp - S) ≤ A := by
    have hA1 : (∫ x in Ioi Y, Y * (thetaCuspFullSource x * Real.exp (b * x)))
        ≤ ∫ x in Ioi Y, x * thetaCuspFullSource x * Real.exp (b * x) := by
      apply MeasureTheory.setIntegral_mono_on
        ((hintZp.mono_set (Ioi_subset_Ioi hY0.le)).const_mul Y)
        (hintA.mono_set (Ioi_subset_Ioi hY0.le))
        measurableSet_Ioi
      intro x hx
      have hxY : Y < x := hx
      have h0 := laplace_integrand_nonneg b x
      calc Y * (thetaCuspFullSource x * Real.exp (b * x))
          ≤ x * (thetaCuspFullSource x * Real.exp (b * x)) :=
            mul_le_mul_of_nonneg_right hxY.le h0
        _ = x * thetaCuspFullSource x * Real.exp (b * x) := by ring
    have h1 : (∫ x in Ioi Y, Y * (thetaCuspFullSource x * Real.exp (b * x)))
        = Y * ∫ x in Ioi Y, thetaCuspFullSource x * Real.exp (b * x) :=
      MeasureTheory.integral_const_mul _ _
    have h2 : (∫ x in Ioc (0 : ℝ) Y, x * thetaCuspFullSource x * Real.exp (b * x)) +
        (∫ x in Ioi Y, x * thetaCuspFullSource x * Real.exp (b * x)) = A := by
      rw [hAdef, ← hIoiu, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
        (hintA.mono_set (by rw [← hIoiu]; exact subset_union_left))
        (hintA.mono_set (by rw [← hIoiu]; exact subset_union_right))]
    have h3 : 0 ≤ ∫ x in Ioc (0 : ℝ) Y, x * thetaCuspFullSource x * Real.exp (b * x) :=
      setIntegral_nonneg measurableSet_Ioc fun x hx =>
        mul_nonneg (mul_nonneg (le_of_lt hx.1) (thetaCuspFullSource_pos x).le)
          (Real.exp_pos _).le
    have h4 : (∫ x in Ioi Y, thetaCuspFullSource x * Real.exp (b * x)) = Zp - S := by
      linarith [hZpsplit]
    calc Y * (Zp - S)
        = Y * ∫ x in Ioi Y, thetaCuspFullSource x * Real.exp (b * x) := by rw [h4]
      _ = ∫ x in Ioi Y, Y * (thetaCuspFullSource x * Real.exp (b * x)) := h1.symm
      _ ≤ ∫ x in Ioi Y, x * thetaCuspFullSource x * Real.exp (b * x) := hA1
      _ ≤ A := by linarith [h2, h3]
  have hSle : S ≤ thetaEnvelopeUpper * Y * Real.exp (c * Y) := by
    have hpoint : ∀ x ∈ Ioc (0 : ℝ) Y, thetaCuspFullSource x * Real.exp (b * x)
        ≤ thetaEnvelopeUpper * Real.exp (c * Y) := by
      intro x hx
      have hx0 : 0 < x := hx.1
      have hxY : x ≤ Y := hx.2
      have hΦ := thetaCuspFullSource_le_envelope hx0.le
      have hE : thetaEnvelope x ≤ Real.exp (9 * x / 2) := by
        unfold HedenmalmThetaSource.thetaEnvelope
        have h1 : Real.exp (-Real.pi * Real.exp (2 * x)) ≤ 1 := by
          have h := Real.exp_le_exp.mpr
            (show -Real.pi * Real.exp (2 * x) ≤ 0 by
              rw [neg_mul]
              exact neg_nonpos.mpr (mul_nonneg Real.pi_pos.le (Real.exp_pos _).le))
          rwa [Real.exp_zero] at h
        calc Real.exp (9 * x / 2) * Real.exp (-Real.pi * Real.exp (2 * x))
            ≤ Real.exp (9 * x / 2) * 1 :=
              mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
          _ = Real.exp (9 * x / 2) := mul_one _
      have hpack : Real.exp (9 * x / 2) * Real.exp (b * x) = Real.exp ((b + 9 / 2) * x) := by
        rw [← Real.exp_add]
        ring_nf
      have hcx : Real.exp ((b + 9 / 2) * x) ≤ Real.exp (c * Y) := by
        apply Real.exp_le_exp.mpr
        rw [hcdef]
        have h92 : (0 : ℝ) ≤ b + 9 / 2 := by linarith
        exact mul_le_mul_of_nonneg_left hxY h92
      calc thetaCuspFullSource x * Real.exp (b * x)
          ≤ (thetaEnvelopeUpper * thetaEnvelope x) * Real.exp (b * x) :=
            mul_le_mul_of_nonneg_right hΦ (Real.exp_pos _).le
        _ ≤ (thetaEnvelopeUpper * Real.exp (9 * x / 2)) * Real.exp (b * x) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hE hCu.le) (Real.exp_pos _).le
        _ = thetaEnvelopeUpper * (Real.exp (9 * x / 2) * Real.exp (b * x)) := by ring
        _ = thetaEnvelopeUpper * Real.exp ((b + 9 / 2) * x) := by rw [hpack]
        _ ≤ thetaEnvelopeUpper * Real.exp (c * Y) :=
            mul_le_mul_of_nonneg_left hcx hCu.le
    have hconstint : IntegrableOn (fun _ : ℝ => thetaEnvelopeUpper * Real.exp (c * Y))
        (Ioc (0 : ℝ) Y) := by
      apply integrableOn_const
      · rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top
      · exact enorm_ne_top
    have hSle' := MeasureTheory.setIntegral_mono_on
      (hintZp.mono_set Ioc_subset_Ioi_self) hconstint measurableSet_Ioc hpoint
    rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ Y - 0), sub_zero, smul_eq_mul] at hSle'
    calc S = ∫ x in Ioc (0 : ℝ) Y, thetaCuspFullSource x * Real.exp (b * x) := hSdef
      _ ≤ Y * (thetaEnvelopeUpper * Real.exp (c * Y)) := hSle'
      _ = thetaEnvelopeUpper * Y * Real.exp (c * Y) := by ring
  have hslab : thetaEnvelopeLower / 2 * Real.exp (b * x₂ - Real.exp 1 * b / 2) ≤ Zp := by
    have hpoint : ∀ x ∈ Ioc x₂ (x₂ + 1 / 2),
        thetaEnvelopeLower * Real.exp (b * x₂ - Real.exp 1 * b / 2)
          ≤ thetaCuspFullSource x * Real.exp (b * x) := by
      intro x hx
      have hx1 : x₂ < x := hx.1
      have hx2 : x ≤ x₂ + 1 / 2 := hx.2
      have hx0 : (0 : ℝ) < x := by linarith
      have hΦ := thetaCuspFullSource_ge_envelope hx0
      have hE : Real.exp (-(Real.exp 1 * b / 2)) ≤ thetaEnvelope x := by
        unfold HedenmalmThetaSource.thetaEnvelope
        have h1 : (1 : ℝ) ≤ Real.exp (9 * x / 2) := by
          rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
          exact Real.exp_le_exp.mpr (by nlinarith)
        have h3 : Real.exp (2 * x) ≤ Real.exp (2 * x₂ + 1) :=
          Real.exp_le_exp.mpr (by linarith)
        have h4 : Real.exp (2 * x₂ + 1) = Real.exp 1 * (b / (2 * Real.pi)) := by
          rw [Real.exp_add, he2x₂]
          ring
        have h5 : Real.pi * Real.exp (2 * x) ≤ Real.exp 1 * b / 2 := by
          have h6 : Real.pi * Real.exp (2 * x)
              ≤ Real.pi * (Real.exp 1 * (b / (2 * Real.pi))) := by
            apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
            rw [← h4]
            exact h3
          have h7 : Real.pi * (Real.exp 1 * (b / (2 * Real.pi))) = Real.exp 1 * b / 2 := by
            field_simp
          linarith
        have h2 : Real.exp (-(Real.exp 1 * b / 2)) ≤ Real.exp (-Real.pi * Real.exp (2 * x)) :=
          Real.exp_le_exp.mpr (by linarith [h5])
        calc Real.exp (-(Real.exp 1 * b / 2))
            ≤ Real.exp (-Real.pi * Real.exp (2 * x)) := h2
          _ = 1 * Real.exp (-Real.pi * Real.exp (2 * x)) := (one_mul _).symm
          _ ≤ Real.exp (9 * x / 2) * Real.exp (-Real.pi * Real.exp (2 * x)) :=
              mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      have hexpb : Real.exp (b * x₂) ≤ Real.exp (b * x) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hsplit2 : Real.exp (b * x₂ - Real.exp 1 * b / 2)
          = Real.exp (-(Real.exp 1 * b / 2)) * Real.exp (b * x₂) := by
        rw [← Real.exp_add]
        ring_nf
      calc thetaEnvelopeLower * Real.exp (b * x₂ - Real.exp 1 * b / 2)
          = thetaEnvelopeLower *
              (Real.exp (-(Real.exp 1 * b / 2)) * Real.exp (b * x₂)) := by rw [hsplit2]
        _ ≤ thetaEnvelopeLower * (thetaEnvelope x * Real.exp (b * x)) := by
            apply mul_le_mul_of_nonneg_left _ hCl.le
            exact mul_le_mul hE hexpb (Real.exp_pos _).le (thetaEnvelope_pos' x).le
        _ = (thetaEnvelopeLower * thetaEnvelope x) * Real.exp (b * x) := by ring
        _ ≤ thetaCuspFullSource x * Real.exp (b * x) :=
            mul_le_mul_of_nonneg_right hΦ (Real.exp_pos _).le
    have hsubset : Ioc x₂ (x₂ + 1 / 2) ⊆ Ioi (0 : ℝ) := by
      intro t ht
      have : x₂ < t := ht.1
      have : (0 : ℝ) < t := by linarith
      exact this
    have h := MeasureTheory.setIntegral_ge_of_const_le measurableSet_Ioc
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) hpoint
      (hintZp.mono_set hsubset)
    rw [MeasureTheory.measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ x₂ + 1 / 2 - x₂), smul_eq_mul] at h
    have hsub : (∫ x in Ioc x₂ (x₂ + 1 / 2), thetaCuspFullSource x * Real.exp (b * x)) ≤ Zp := by
      rw [hZpdef]
      apply MeasureTheory.setIntegral_mono_set hintZp
        (Filter.Eventually.of_forall fun x => laplace_integrand_nonneg b x)
        (LE.le.eventuallyLE hsubset)
    nlinarith [h, hsub]
  have hZpb : thetaEnvelopeLower / 2 * Real.exp b ≤ Zp := by
    have h1 : b ≤ b * x₂ - Real.exp 1 * b / 2 := by nlinarith [hx₂e]
    have h2 : Real.exp b ≤ Real.exp (b * x₂ - Real.exp 1 * b / 2) := Real.exp_le_exp.mpr h1
    have h3 : thetaEnvelopeLower / 2 * Real.exp b
        ≤ thetaEnvelopeLower / 2 * Real.exp (b * x₂ - Real.exp 1 * b / 2) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    linarith [hslab]
  have hZp0 : (0 : ℝ) ≤ Zp := by
    have h0 : (0 : ℝ) ≤ thetaEnvelopeLower / 2 * Real.exp b :=
      mul_nonneg (by linarith) (Real.exp_pos b).le
    linarith [hZpb]
  have h4S : 4 * S ≤ Zp := by
    have hYe : Y ≤ Real.exp Y := by
      have := Real.add_one_le_exp Y
      linarith
    have h8γ0 : (0 : ℝ) < 8 * xiRayEnvelopeRatio := by nlinarith
    have hγe : (8 : ℝ) * xiRayEnvelopeRatio
        = Real.exp (Real.log (8 * xiRayEnvelopeRatio)) := by
      rw [Real.exp_log h8γ0]
    have hexpineq : Real.log (8 * xiRayEnvelopeRatio) + Y + c * Y
        ≤ b * x₂ - Real.exp 1 * b / 2 := by
      have hx₂val : b * x₂ = b * L / 2 - b * Real.log (2 * Real.pi) / 2 := by
        rw [hx₂def, hlogb2π]
        ring
      have hcY : c * Y = b * L / 4 + 9 / 8 * L := by
        rw [hcdef, hYdef]
        ring
      have hmain : b * Real.log (2 * Real.pi) / 2 + Real.exp 1 * b / 2 + 2 * b
          ≤ b * L / 4 := by
        nlinarith [mul_nonneg
          (by linarith [hL8] :
            (0 : ℝ) ≤ L - 2 * Real.log (2 * Real.pi) - 2 * Real.exp 1 - 8) hb0.le]
      have hYL : Y = L / 4 := hYdef
      linarith [hlog8γb, hLb, hmain, hx₂val, hcY, hYL, hL0, hb0.le]
    have hkey : 4 * (thetaEnvelopeUpper * Y * Real.exp (c * Y))
        ≤ thetaEnvelopeLower / 2 * Real.exp (b * x₂ - Real.exp 1 * b / 2) := by
      have hstep1 : (8 * xiRayEnvelopeRatio) * Y * Real.exp (c * Y)
          ≤ (8 * xiRayEnvelopeRatio) * Real.exp Y * Real.exp (c * Y) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hYe h8γ0.le) (Real.exp_pos _).le
      have hpack : Real.exp (Real.log (8 * xiRayEnvelopeRatio)) * Real.exp Y
          * Real.exp (c * Y)
          = Real.exp (Real.log (8 * xiRayEnvelopeRatio) + Y + c * Y) := by
        rw [← Real.exp_add, ← Real.exp_add]
      have hstep2 : (8 * xiRayEnvelopeRatio) * Real.exp Y * Real.exp (c * Y)
          ≤ Real.exp (b * x₂ - Real.exp 1 * b / 2) := by
        rw [hγe, hpack]
        exact Real.exp_le_exp.mpr hexpineq
      have hCuform : thetaEnvelopeUpper = xiRayEnvelopeRatio * thetaEnvelopeLower :=
        thetaEnvelopeUpper_eq_ratio_mul
      have hfin : 4 * (thetaEnvelopeUpper * Y * Real.exp (c * Y))
          = thetaEnvelopeLower / 2 * ((8 * xiRayEnvelopeRatio) * Y * Real.exp (c * Y)) := by
        rw [hCuform]
        ring
      rw [hfin]
      apply mul_le_mul_of_nonneg_left _ (by linarith : (0 : ℝ) ≤ thetaEnvelopeLower / 2)
      exact le_trans hstep1 hstep2
    calc 4 * S ≤ 4 * (thetaEnvelopeUpper * Y * Real.exp (c * Y)) := by linarith [hSle]
      _ ≤ thetaEnvelopeLower / 2 * Real.exp (b * x₂ - Real.exp 1 * b / 2) := hkey
      _ ≤ Zp := hslab
  have hCuZ : thetaEnvelopeUpper * (1 + L / 8) ≤ L / 16 * Zp := by
    have h32γ : (32 : ℝ) * xiRayEnvelopeRatio ≤ Real.exp b := by
      have h32γ0 : (0 : ℝ) < 32 * xiRayEnvelopeRatio := by nlinarith
      have h2 : Real.log (32 * xiRayEnvelopeRatio)
          = Real.log 32 + Real.log xiRayEnvelopeRatio :=
        Real.log_mul (by norm_num) (ne_of_gt hγ0)
      have h3 : Real.log 32 ≤ Real.log 4096 :=
        Real.log_le_log (by norm_num) (by norm_num)
      have h4 : Real.log 4096 = 4 * Real.log 8 := by
        rw [show (4096 : ℝ) = 8 ^ 4 by norm_num, Real.log_pow]
        push_cast
        ring
      have h5 : Real.log (8 * xiRayEnvelopeRatio)
          = Real.log 8 + Real.log xiRayEnvelopeRatio :=
        Real.log_mul (by norm_num) (ne_of_gt hγ0)
      have h6 : 0 ≤ Real.log xiRayEnvelopeRatio := Real.log_nonneg hγ1
      have h7 : 4 * Real.log (8 * xiRayEnvelopeRatio) + 16 ≤ b := by
        unfold xiRayLowerBase at hb
        linarith
      have h1 : Real.log (32 * xiRayEnvelopeRatio) ≤ b := by linarith
      calc (32 : ℝ) * xiRayEnvelopeRatio
          = Real.exp (Real.log (32 * xiRayEnvelopeRatio)) := (Real.exp_log h32γ0).symm
        _ ≤ Real.exp b := Real.exp_le_exp.mpr h1
    have h1L : 1 + L / 8 ≤ L := by linarith
    have hCuL : thetaEnvelopeUpper * (1 + L / 8)
        ≤ xiRayEnvelopeRatio * thetaEnvelopeLower * L := by
      rw [← thetaEnvelopeUpper_eq_ratio_mul]
      exact mul_le_mul_of_nonneg_left h1L hCu.le
    have hmid : xiRayEnvelopeRatio * thetaEnvelopeLower * L
        = L / 16 * (thetaEnvelopeLower / 2 * (32 * xiRayEnvelopeRatio)) := by ring
    have hlast : L / 16 * (thetaEnvelopeLower / 2 * (32 * xiRayEnvelopeRatio))
        ≤ L / 16 * (thetaEnvelopeLower / 2 * Real.exp b) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith : (0 : ℝ) ≤ L / 16)
      exact mul_le_mul_of_nonneg_left h32γ (by linarith)
    have hfin2 : L / 16 * (thetaEnvelopeLower / 2 * Real.exp b) ≤ L / 16 * Zp :=
      mul_le_mul_of_nonneg_left hZpb (by linarith)
    calc thetaEnvelopeUpper * (1 + L / 8)
        ≤ xiRayEnvelopeRatio * thetaEnvelopeLower * L := hCuL
      _ = L / 16 * (thetaEnvelopeLower / 2 * (32 * xiRayEnvelopeRatio)) := hmid
      _ ≤ L / 16 * (thetaEnvelopeLower / 2 * Real.exp b) := hlast
      _ ≤ L / 16 * Zp := hfin2
  have hZpos : 0 < xiRayLaplace b := xiRayLaplace_pos hb0.le
  have hLS : L / 4 * S ≤ L / 16 * Zp := by
    have h := mul_le_mul_of_nonneg_left h4S (by linarith : (0 : ℝ) ≤ L / 16)
    nlinarith [hS0, hL0]
  have hNge : Y * (Zp - S) - thetaEnvelopeUpper ≤ xiRayLaplaceMoment b := by
    rw [hNsplit]
    linarith [hA2, hA'le]
  have hZle : xiRayLaplace b ≤ Zp + thetaEnvelopeUpper := by
    rw [hZsplit]
    linarith [hZ'le]
  have htarget : L / 8 * xiRayLaplace b ≤ xiRayLaplaceMoment b := by
    have h1 : L / 8 * xiRayLaplace b ≤ L / 8 * (Zp + thetaEnvelopeUpper) :=
      mul_le_mul_of_nonneg_left hZle (by linarith : (0 : ℝ) ≤ L / 8)
    have hYL : Y = L / 4 := hYdef
    nlinarith [hNge, hLS, hCuZ, hZp0, hS0, hL0]
  unfold xiRayLogDeriv
  rw [le_div_iff₀ hZpos]
  linarith [htarget]

end RHTower

namespace RHTower

/-! ## Correlation decay on multiplicatively separated nodes -/

private theorem log_div_self_antitone {a c : ℝ} (ha : Real.exp 1 ≤ a) (hac : a ≤ c) :
    Real.log c / c ≤ Real.log a / a := by
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 1) ha
  have hc0 : 0 < c := lt_of_lt_of_le ha0 hac
  have hla : 1 ≤ Real.log a := (Real.le_log_iff_exp_le ha0).mpr ha
  have hkey : a * Real.log c ≤ c * Real.log a := by
    have h1 : Real.log c - Real.log a ≤ c / a - 1 := by
      have h := Real.log_le_sub_one_of_pos (show 0 < c / a from div_pos hc0 ha0)
      rwa [Real.log_div (ne_of_gt hc0) (ne_of_gt ha0)] at h
    have h2 : a * (Real.log c - Real.log a) ≤ c - a := by
      have h3 := mul_le_mul_of_nonneg_left h1 ha0.le
      have h4 : a * (c / a - 1) = c - a := by
        field_simp
      linarith [h4 ▸ h3]
    have h5 : c - a ≤ (c - a) * Real.log a := by
      nlinarith [hla, hac]
    nlinarith [h2, h5]
  rw [div_le_div_iff₀ hc0 ha0]
  linarith [hkey]

private theorem one_add_two_le_four_pow (d : ℕ) : (1 : ℝ) + 2 * d ≤ 4 ^ d := by
  induction d with
  | zero => norm_num
  | succ m ih =>
    have h4 : (1 : ℝ) ≤ 4 ^ m := one_le_pow₀ (by norm_num)
    have hstep : (4 : ℝ) ^ (m + 1) = 4 * 4 ^ m := by ring
    push_cast
    nlinarith [ih]

private theorem exp_one_le_packetBase : Real.exp 1 ≤ xiRayPacketBase := by
  have h1 := Real.exp_one_lt_d9
  have h2 := xiRayPacketBase_ge
  linarith

private theorem xiRayLogDeriv_pos_of_packetBase {u : ℝ} (hu : xiRayPacketBase ≤ u) :
    0 < xiRayLogDeriv u := by
  have hu0 : 0 < u := lt_of_lt_of_le (by linarith [xiRayPacketBase_ge]) hu
  have hlow := xiRayLogDeriv_ge (le_trans xiRayLowerBase_le_packetBase hu)
  have hlog : 1 ≤ Real.log u := by
    rw [Real.le_log_iff_exp_le hu0]
    linarith [exp_one_le_packetBase]
  linarith

private theorem packet_corr {u v : ℝ} (hu : xiRayPacketBase ≤ u) (hv : xiRayPacketBase ≤ v)
    {d : ℕ} (hgap : xiRayPacketBase ^ (2 * d) * u ≤ v) :
    (xiRayLogDeriv u + xiRayLogDeriv v) / (u + v)
      ≤ 32 * (2 / xiRayPacketBase) ^ d *
        (Real.sqrt (xiRayLogDeriv u / u) * Real.sqrt (xiRayLogDeriv v / v)) := by
  have hR256 := xiRayPacketBase_ge
  have hR0 : (0 : ℝ) < xiRayPacketBase := by linarith
  have hR1 : (1 : ℝ) ≤ xiRayPacketBase := by linarith
  have hu0 : (0 : ℝ) < u := by linarith
  have hv0 : (0 : ℝ) < v := by linarith
  have huv : u ≤ v := by
    have hpow : (1 : ℝ) ≤ xiRayPacketBase ^ (2 * d) := one_le_pow₀ hR1
    nlinarith
  have hueexp : Real.exp 1 ≤ u := le_trans exp_one_le_packetBase hu
  have hru_le := xiRayLogDeriv_le (le_trans xiRayUpperBase_le_packetBase hu)
  have hru_ge := xiRayLogDeriv_ge (le_trans xiRayLowerBase_le_packetBase hu)
  have hrv_le := xiRayLogDeriv_le (le_trans xiRayUpperBase_le_packetBase hv)
  have hrv_ge := xiRayLogDeriv_ge (le_trans xiRayLowerBase_le_packetBase hv)
  have hlogu1 : 1 ≤ Real.log u := (Real.le_log_iff_exp_le hu0).mpr hueexp
  have hlogv1 : 1 ≤ Real.log v :=
    (Real.le_log_iff_exp_le hv0).mpr (le_trans hueexp huv)
  have hloguv : Real.log u ≤ Real.log v := Real.log_le_log hu0 huv
  set q : ℝ := 2 / xiRayPacketBase with hqdef
  have hq0 : 0 < q := div_pos (by norm_num) hR0
  -- the log-ratio contraction
  have hkey : Real.log v / v ≤ q ^ (2 * d) * (Real.log u / u) := by
    have hRu0 : (0 : ℝ) < xiRayPacketBase ^ (2 * d) * u :=
      mul_pos (pow_pos hR0 _) hu0
    have hRue : Real.exp 1 ≤ xiRayPacketBase ^ (2 * d) * u := by
      have hpow : (1 : ℝ) ≤ xiRayPacketBase ^ (2 * d) := one_le_pow₀ hR1
      nlinarith
    have step1 : Real.log v / v
        ≤ Real.log (xiRayPacketBase ^ (2 * d) * u) / (xiRayPacketBase ^ (2 * d) * u) :=
      log_div_self_antitone hRue hgap
    have step2 : Real.log (xiRayPacketBase ^ (2 * d) * u)
        = 2 * d * Real.log xiRayPacketBase + Real.log u := by
      rw [Real.log_mul (ne_of_gt (pow_pos hR0 _)) (ne_of_gt hu0), Real.log_pow]
      push_cast
      ring
    have hlogR : Real.log xiRayPacketBase ≤ Real.log u := Real.log_le_log hR0 hu
    have hlogR0 : 0 ≤ Real.log xiRayPacketBase := Real.log_nonneg hR1
    have step3 : 2 * d * Real.log xiRayPacketBase + Real.log u
        ≤ 4 ^ d * Real.log u := by
      have h1 : 2 * (d : ℝ) * Real.log xiRayPacketBase ≤ 2 * d * Real.log u := by
        apply mul_le_mul_of_nonneg_left hlogR
        positivity
      have h2 : (1 + 2 * (d : ℝ)) * Real.log u ≤ 4 ^ d * Real.log u := by
        apply mul_le_mul_of_nonneg_right (one_add_two_le_four_pow d)
        linarith
      nlinarith
    have step4 : Real.log (xiRayPacketBase ^ (2 * d) * u) / (xiRayPacketBase ^ (2 * d) * u)
        ≤ (4 ^ d * Real.log u) / (xiRayPacketBase ^ (2 * d) * u) := by
      apply div_le_div_of_nonneg_right _ hRu0.le
      rw [step2]
      exact step3
    have step5 : (4 ^ d * Real.log u) / (xiRayPacketBase ^ (2 * d) * u)
        = q ^ (2 * d) * (Real.log u / u) := by
      rw [hqdef, div_pow, show ((2 : ℝ)) ^ (2 * d) = 4 ^ d by
        rw [pow_mul]
        norm_num]
      field_simp
    calc Real.log v / v
        ≤ Real.log (xiRayPacketBase ^ (2 * d) * u) / (xiRayPacketBase ^ (2 * d) * u) := step1
      _ ≤ (4 ^ d * Real.log u) / (xiRayPacketBase ^ (2 * d) * u) := step4
      _ = q ^ (2 * d) * (Real.log u / u) := step5
  set A : ℝ := Real.log v / v with hAdef
  set B : ℝ := Real.log u / u with hBdef
  have hA0 : 0 ≤ A := div_nonneg (by linarith) hv0.le
  have hB0 : 0 ≤ B := div_nonneg (by linarith) hu0.le
  -- the square-root form of the contraction
  have hsqrt : A ≤ q ^ d * Real.sqrt (B * A) := by
    have h1 : A * A ≤ (q ^ (2 * d) * B) * A := mul_le_mul_of_nonneg_right hkey hA0
    have h2 : Real.sqrt (A * A) ≤ Real.sqrt ((q ^ (2 * d) * B) * A) :=
      Real.sqrt_le_sqrt h1
    have h3 : Real.sqrt (A * A) = A := Real.sqrt_mul_self hA0
    have h4 : (q ^ (2 * d) * B) * A = (q ^ d) ^ 2 * (B * A) := by
      rw [show 2 * d = d * 2 from Nat.mul_comm 2 d, pow_mul]
      ring
    have h5 : Real.sqrt ((q ^ d) ^ 2 * (B * A))
        = q ^ d * Real.sqrt (B * A) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hq0.le _)]
    calc A = Real.sqrt (A * A) := h3.symm
      _ ≤ Real.sqrt ((q ^ (2 * d) * B) * A) := h2
      _ = Real.sqrt ((q ^ d) ^ 2 * (B * A)) := by rw [h4]
      _ = q ^ d * Real.sqrt (B * A) := h5
  -- kernel numerator and diagonal comparison
  have hKnum : (xiRayLogDeriv u + xiRayLogDeriv v) / (u + v) ≤ 4 * Real.log v / v := by
    have hnum : xiRayLogDeriv u + xiRayLogDeriv v ≤ 4 * Real.log v := by
      have h1 : xiRayLogDeriv u ≤ Real.log v + 1 := by linarith
      have h2 : xiRayLogDeriv v ≤ Real.log v + 1 := by linarith
      linarith
    have hnum0 : 0 ≤ xiRayLogDeriv u + xiRayLogDeriv v := by
      have := xiRayLogDeriv_pos_of_packetBase hu
      have := xiRayLogDeriv_pos_of_packetBase hv
      linarith
    calc (xiRayLogDeriv u + xiRayLogDeriv v) / (u + v)
        ≤ (xiRayLogDeriv u + xiRayLogDeriv v) / v := by
          apply div_le_div_of_nonneg_left hnum0 hv0
          linarith
      _ ≤ (4 * Real.log v) / v := div_le_div_of_nonneg_right hnum hv0.le
      _ = 4 * Real.log v / v := by ring
  -- diagonal square roots dominate the (1/8)-scaled log data
  have hDu : B / 8 ≤ xiRayLogDeriv u / u := by
    have h1 : Real.log u / 8 / u ≤ xiRayLogDeriv u / u :=
      div_le_div_of_nonneg_right hru_ge hu0.le
    have h2 : B / 8 = Real.log u / 8 / u := by
      rw [hBdef]
      ring
    rw [h2]
    exact h1
  have hDv : A / 8 ≤ xiRayLogDeriv v / v := by
    have h1 : Real.log v / 8 / v ≤ xiRayLogDeriv v / v :=
      div_le_div_of_nonneg_right hrv_ge hv0.le
    have h2 : A / 8 = Real.log v / 8 / v := by
      rw [hAdef]
      ring
    rw [h2]
    exact h1
  have hsq8 : Real.sqrt (B / 8) * Real.sqrt (A / 8) = Real.sqrt (B * A) / 8 := by
    rw [← Real.sqrt_mul (by linarith : (0 : ℝ) ≤ B / 8)]
    have h1 : B / 8 * (A / 8) = B * A * (1 / 64) := by ring
    rw [h1, Real.sqrt_mul (mul_nonneg hB0 hA0),
      show (1 : ℝ) / 64 = (1 / 8) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 8)]
    ring
  have h3 : Real.sqrt (B / 8) * Real.sqrt (A / 8)
      ≤ Real.sqrt (xiRayLogDeriv u / u) * Real.sqrt (xiRayLogDeriv v / v) :=
    mul_le_mul (Real.sqrt_le_sqrt hDu) (Real.sqrt_le_sqrt hDv)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc (xiRayLogDeriv u + xiRayLogDeriv v) / (u + v)
      ≤ 4 * Real.log v / v := hKnum
    _ = 4 * A := by rw [hAdef]; ring
    _ ≤ 4 * (q ^ d * Real.sqrt (B * A)) := by
        linarith [mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0 : ℝ) ≤ 4)]
    _ = 32 * q ^ d * (Real.sqrt (B * A) / 8) := by ring
    _ = 32 * q ^ d * (Real.sqrt (B / 8) * Real.sqrt (A / 8)) := by rw [hsq8]
    _ ≤ 32 * q ^ d *
          (Real.sqrt (xiRayLogDeriv u / u) * Real.sqrt (xiRayLogDeriv v / v)) := by
        exact mul_le_mul_of_nonneg_left h3
          (mul_nonneg (by norm_num) (pow_nonneg hq0.le d))

end RHTower
