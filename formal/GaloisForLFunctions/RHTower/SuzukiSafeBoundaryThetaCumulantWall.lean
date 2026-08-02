import GaloisForLFunctions.HTGeometry.MomentHankelStrict
import GaloisForLFunctions.HTGeometry.PositiveReweightingSupport
import GaloisForLFunctions.RHTower.PrimeArchThetaWardLaplaceHalfDensity
import GaloisForLFunctions.RHTower.SuzukiXiSecondDefectJet

/-!
# Suzuki's safe wall as a boundary-theta cumulant inequality

The interior Fourier--Laplace source law for `XiC` was previously restricted to
`|w.im| < 1`, while Suzuki's safe point is the excluded endpoint `w = i`.  The actual
theta-cusp source has much faster atomwise decay than the coarse global exponential estimate:
all polynomial moments remain integrable after the unit tilt.

This module uses that decay and dominated convergence to extend every Xi jet to `w = i`.
The first four endpoint jets identify the literal probability law proportional to

`exp(x) * thetaCuspFullSource(x) dx`

with the first three logarithmic Xi jets at `s = 3/2`.  If `mu`, `v`, and `kappa3` are its
mean, variance, and third cumulant, and

`A = Re M₀(1)`, `B = Re M₁(1)`, `C = Re M₂(1)`,

then the exact unconditional calibration is

`8 * (A*C - B^2) = mu*kappa3 + (mu-v)*(mu+2*v)`.

Thus Suzuki's first nonlinear admission gate is one explicit skewness budget for the literal
boundary theta law.  The equivalence is proved here; the sign of that budget is not assumed.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

theorem exp_mul_thetaCuspSourceTerm_one_eq_polynomialAtom
    (x : ℝ) :
    Real.exp x * thetaCuspSourceTerm x 1 =
      thetaCuspPolynomialAtom (X * thetaCuspSeedPolynomial) 1 x := by
  simp [thetaCuspSourceTerm, thetaCuspSeed, thetaCuspPolynomialAtom,
    thetaCuspSeedPolynomial]
  ring

theorem integrableOn_pow_mul_exp_mul_thetaCuspFullSource
    (k : ℕ) :
    IntegrableOn (fun x : ℝ =>
      x ^ k * Real.exp x * thetaCuspFullSource x) (Ioi 0) := by
  let W : ℝ := thetaCuspHigherAtomDominationWeight
  let first : ℝ → ℝ := fun x => thetaCuspSourceTerm x 1
  let major : ℝ → ℝ := fun x =>
    (1 + W) * (x ^ k * Real.exp x * first x)
  have hW : 0 ≤ W := by
    exact thetaCuspHigherAtomDominationWeight_nonneg
  have hfirst : IntegrableOn (fun x : ℝ =>
      x ^ k * Real.exp x * first x) (Ioi 0) := by
    have h :=
      integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
        k (X * thetaCuspSeedPolynomial) (n := 1) (by norm_num)
    apply h.congr
    filter_upwards [] with x
    dsimp only [first]
    rw [← exp_mul_thetaCuspSourceTerm_one_eq_polynomialAtom]
    ring
  have hmajor : IntegrableOn major (Ioi 0) := by
    exact hfirst.const_mul (1 + W)
  apply Integrable.mono hmajor
  · exact (((continuous_id.pow k).mul Real.continuous_exp).mul
      contDiff_thetaCuspFullSource.continuous).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := hx.le
    have hfirst0 : 0 ≤ first x := by
      exact thetaCuspSourceTerm_nonneg_of_pos hx 1
    have hsource0 : 0 ≤ thetaCuspFullSource x :=
      (thetaCuspFullSource_pos_of_pos hx).le
    have hsource :
        thetaCuspFullSource x ≤ (1 + W) * first x := by
      have htail := thetaCuspFullSource_sub_first_le hx0
      dsimp only [W, first] at htail ⊢
      linarith
    have hcoef : 0 ≤ 1 + W := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg
        (mul_nonneg (pow_nonneg hx0 k) (Real.exp_pos _).le) hsource0),
      abs_of_nonneg (mul_nonneg hcoef
        (mul_nonneg
          (mul_nonneg (pow_nonneg hx0 k) (Real.exp_pos _).le) hfirst0))]
    nlinarith [mul_nonneg (pow_nonneg hx0 k) (Real.exp_pos x).le]

theorem integrable_pow_mul_exp_mul_thetaCuspFullSource
    (k : ℕ) :
    Integrable (fun x : ℝ =>
      x ^ k * Real.exp x * thetaCuspFullSource x) := by
  have hpos := integrableOn_pow_mul_exp_mul_thetaCuspFullSource k
  have hraw :=
    thetaCuspSchwartzReal.integrable_pow_mul (volume : Measure ℝ) k
  have hneg : IntegrableOn (fun x : ℝ =>
      x ^ k * Real.exp x * thetaCuspFullSource x) (Iic 0) := by
    apply Integrable.mono hraw.integrableOn
    · exact (((continuous_id.pow k).mul Real.continuous_exp).mul
        contDiff_thetaCuspFullSource.continuous).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
      have hexp : Real.exp x ≤ 1 := by
        simpa using Real.exp_le_one_iff.mpr hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      have hsource : 0 ≤ |thetaCuspFullSource x| := abs_nonneg _
      calc
        |x ^ k| * Real.exp x * |thetaCuspFullSource x| ≤
            |x ^ k| * 1 * |thetaCuspFullSource x| := by gcongr
        _ = |x ^ k| * |thetaCuspFullSource x| := by ring
        _ = ‖x‖ ^ k * ‖thetaCuspSchwartzReal x‖ := by
          simp [thetaCuspSchwartzReal_apply, abs_pow]
        _ ≤ |‖x‖ ^ k * ‖thetaCuspSchwartzReal x‖| :=
          le_abs_self _
  simpa [Ioi_union_Iic] using hpos.union hneg

theorem integrable_pow_mul_exp_neg_mul_thetaCuspFullSource
    (k : ℕ) :
    Integrable (fun x : ℝ =>
      x ^ k * Real.exp (-x) * thetaCuspFullSource x) := by
  have hcomp :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable
      (integrable_pow_mul_exp_mul_thetaCuspFullSource k)
  have hscaled := hcomp.const_mul ((-1 : ℝ) ^ k)
  apply hscaled.congr
  filter_upwards with x
  simp only [Function.comp_apply, thetaCuspFullSource_neg]
  have hnegpow : (-x) ^ k = (-1 : ℝ) ^ k * x ^ k := by
    rw [neg_pow]
  have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← pow_add, ← two_mul]
    rw [pow_mul]
    norm_num
  rw [hnegpow]
  calc
    (-1 : ℝ) ^ k *
        (((-1 : ℝ) ^ k * x ^ k) * Real.exp (-x) *
          thetaCuspFullSource x) =
        (((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * x ^ k) *
          Real.exp (-x) * thetaCuspFullSource x := by ring
    _ = x ^ k * Real.exp (-x) * thetaCuspFullSource x := by
      rw [hsign, one_mul]

theorem integrable_thetaCuspFourierLaplaceJetIntegrand_I
    (k : ℕ) :
    Integrable (thetaCuspFourierLaplaceJetIntegrand k I) := by
  have hreal : Integrable (fun x : ℝ =>
      ((x ^ k * Real.exp x * thetaCuspFullSource x : ℝ) : ℂ)) :=
    (integrable_pow_mul_exp_mul_thetaCuspFullSource k).ofReal
  have hcomplex := hreal.const_mul ((-I) ^ k)
  apply hcomplex.congr
  filter_upwards with x
  simp [thetaCuspFourierLaplaceJetIntegrand,
    thetaCuspFourierLaplaceIntegrand]
  ring

theorem integrable_thetaCuspFourierLaplaceJetIntegrand_neg_I
    (k : ℕ) :
    Integrable (thetaCuspFourierLaplaceJetIntegrand k (-I)) := by
  have hreal : Integrable (fun x : ℝ =>
      ((x ^ k * Real.exp (-x) * thetaCuspFullSource x : ℝ) : ℂ)) :=
    (integrable_pow_mul_exp_neg_mul_thetaCuspFullSource k).ofReal
  have hcomplex := hreal.const_mul ((-I) ^ k)
  apply hcomplex.congr
  filter_upwards with x
  simp [thetaCuspFourierLaplaceJetIntegrand,
    thetaCuspFourierLaplaceIntegrand]
  ring

/-- Every centered Xi jet has its literal theta-source integral at the excluded upper boundary
`w = i`. -/
theorem iteratedDeriv_XiC_eq_integral_thetaCuspFourierLaplaceJet_I
    (k : ℕ) :
    iteratedDeriv k XiC I =
      ∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand k I x := by
  let a : ℕ → ℝ := fun n => (n : ℝ) / ((n : ℝ) + 1)
  let w : ℕ → ℂ := fun n => (a n : ℂ) * I
  let F : ℕ → ℝ → ℂ := fun n x =>
    thetaCuspFourierLaplaceJetIntegrand k (w n) x
  let bound : ℝ → ℝ := fun x =>
    ‖thetaCuspFourierLaplaceJetIntegrand k I x‖ +
      ‖thetaCuspFourierLaplaceJetIntegrand k (-I) x‖
  have ha_nonneg (n : ℕ) : 0 ≤ a n := by
    dsimp only [a]
    positivity
  have ha_lt_one (n : ℕ) : a n < 1 := by
    dsimp only [a]
    rw [div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    linarith
  have ha_tend : Tendsto a atTop (𝓝 1) := by
    simpa only [a] using
      (tendsto_natCast_div_add_atTop (1 : ℝ))
  have hw_tend : Tendsto w atTop (𝓝 I) := by
    have hcomplex :
        Tendsto (fun n : ℕ => (a n : ℂ)) atTop (𝓝 (1 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp ha_tend
    simpa only [w, one_mul] using hcomplex.mul_const I
  have hFmeas : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable (F n) := by
    filter_upwards with n
    have hsource : Continuous thetaCuspFullSource :=
      contDiff_thetaCuspFullSource.continuous
    exact ((by
      dsimp only [F, w]
      unfold thetaCuspFourierLaplaceJetIntegrand
        thetaCuspFourierLaplaceIntegrand
      fun_prop (disch := assumption) : Continuous (F n))).aestronglyMeasurable
  have hboundInt : Integrable bound := by
    exact (integrable_thetaCuspFourierLaplaceJetIntegrand_I k).norm.add
      (integrable_thetaCuspFourierLaplaceJetIntegrand_neg_I k).norm
  have hnorm (b x : ℝ) :
      ‖thetaCuspFourierLaplaceJetIntegrand k ((b : ℂ) * I) x‖ =
        |x| ^ k * Real.exp (b * x) * |thetaCuspFullSource x| := by
    simp [thetaCuspFourierLaplaceJetIntegrand,
      thetaCuspFourierLaplaceIntegrand, Complex.norm_exp, mul_re]
    ring
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ x : ℝ,
      ‖F n x‖ ≤ bound x := by
    filter_upwards with n
    filter_upwards with x
    have ha_le : a n ≤ 1 := (ha_lt_one n).le
    by_cases hx : 0 ≤ x
    · have hax : a n * x ≤ 1 * x :=
        mul_le_mul_of_nonneg_right ha_le hx
      have hexp : Real.exp (a n * x) ≤ Real.exp (1 * x) :=
        Real.exp_le_exp.mpr hax
      have hmain :
          ‖thetaCuspFourierLaplaceJetIntegrand k (w n) x‖ ≤
            ‖thetaCuspFourierLaplaceJetIntegrand k I x‖ := by
        have hnormI :
            ‖thetaCuspFourierLaplaceJetIntegrand k I x‖ =
              |x| ^ k * Real.exp x * |thetaCuspFullSource x| := by
          simpa using hnorm 1 x
        rw [show w n = (a n : ℂ) * I by rfl,
          hnorm (a n) x, hnormI]
        gcongr
        simpa using hax
      exact le_trans hmain (le_add_of_nonneg_right (norm_nonneg _))
    · have hxle : x ≤ 0 := le_of_not_ge hx
      have hminus : -1 ≤ a n := by linarith [ha_nonneg n]
      have hax : a n * x ≤ (-1) * x :=
        mul_le_mul_of_nonpos_right hminus hxle
      have hexp : Real.exp (a n * x) ≤ Real.exp ((-1) * x) :=
        Real.exp_le_exp.mpr hax
      have hmain :
          ‖thetaCuspFourierLaplaceJetIntegrand k (w n) x‖ ≤
            ‖thetaCuspFourierLaplaceJetIntegrand k (-I) x‖ := by
        have hnormNegI :
            ‖thetaCuspFourierLaplaceJetIntegrand k (-I) x‖ =
              |x| ^ k * Real.exp (-x) * |thetaCuspFullSource x| := by
          simpa using hnorm (-1) x
        rw [show w n = (a n : ℂ) * I by rfl,
          hnorm (a n) x, hnormNegI]
        gcongr
        simpa using hax
      exact le_trans hmain (le_add_of_nonneg_left (norm_nonneg _))
  have hlim : ∀ᵐ x : ℝ,
      Tendsto (fun n : ℕ => F n x) atTop
        (𝓝 (thetaCuspFourierLaplaceJetIntegrand k I x)) := by
    filter_upwards with x
    have hcont : Continuous
        (fun z : ℂ => thetaCuspFourierLaplaceJetIntegrand k z x) := by
      unfold thetaCuspFourierLaplaceJetIntegrand
        thetaCuspFourierLaplaceIntegrand
      fun_prop
    change Tendsto
      ((fun z : ℂ => thetaCuspFourierLaplaceJetIntegrand k z x) ∘ w)
      atTop (𝓝 (thetaCuspFourierLaplaceJetIntegrand k I x))
    exact hcont.continuousAt.tendsto.comp hw_tend
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    bound hFmeas hbound hboundInt hlim
  have hXiCont : Continuous (iteratedDeriv k XiC) :=
    (XiC_analytic.contDiff (n := (k : ℕ∞))).continuous_iteratedDeriv' k
  have hXiTend :
      Tendsto (fun n : ℕ => iteratedDeriv k XiC (w n))
        atTop (𝓝 (iteratedDeriv k XiC I)) :=
    hXiCont.continuousAt.tendsto.comp hw_tend
  have hInterior (n : ℕ) :
      iteratedDeriv k XiC (w n) = ∫ x : ℝ, F n x := by
    have hwstrip : w n ∈ thetaCuspFourierLaplaceStrip := by
      change -1 < (w n).im ∧ (w n).im < 1
      have him : (w n).im = a n := by simp [w]
      rw [him]
      exact ⟨by linarith [ha_nonneg n], ha_lt_one n⟩
    simpa only [F] using
      (iteratedDeriv_XiC_eq_integral_thetaCuspFourierLaplaceJet
        k hwstrip)
  have hDCT' :
      Tendsto (fun n : ℕ => iteratedDeriv k XiC (w n))
        atTop
        (𝓝 (∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand k I x)) :=
    hDCT.congr' (Filter.Eventually.of_forall fun n => (hInterior n).symm)
  exact tendsto_nhds_unique hXiTend hDCT'

/-- Raw moments of the literal theta source under Suzuki's unit exponential tilt. -/
def thetaCuspSafeTiltRawMoment (k : ℕ) : ℝ :=
  ∫ x : ℝ, x ^ k * Real.exp x * thetaCuspFullSource x

theorem integrable_thetaCuspSafeTiltRawMoment (k : ℕ) :
    Integrable (fun x : ℝ =>
      x ^ k * Real.exp x * thetaCuspFullSource x) :=
  integrable_pow_mul_exp_mul_thetaCuspFullSource k

/-- The endpoint Xi jets are exactly the raw moments of the unit-tilted theta source. -/
theorem iteratedDeriv_XiC_I_eq_thetaCuspSafeTiltRawMoment
    (k : ℕ) :
    iteratedDeriv k XiC I =
      (-I) ^ k * (thetaCuspSafeTiltRawMoment k : ℂ) := by
  rw [iteratedDeriv_XiC_eq_integral_thetaCuspFourierLaplaceJet_I]
  rw [thetaCuspSafeTiltRawMoment]
  calc
    (∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand k I x) =
        ∫ x : ℝ, (-I) ^ k *
          ((x ^ k * Real.exp x * thetaCuspFullSource x : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      simp [thetaCuspFourierLaplaceJetIntegrand,
        thetaCuspFourierLaplaceIntegrand]
      ring
    _ = (-I) ^ k *
        ∫ x : ℝ, ((x ^ k * Real.exp x *
          thetaCuspFullSource x : ℝ) : ℂ) := by
      rw [integral_const_mul]
    _ = (-I) ^ k *
        ((∫ x : ℝ, x ^ k * Real.exp x *
          thetaCuspFullSource x : ℝ) : ℂ) := by
      congr 1
      exact integral_ofReal

theorem thetaCuspSafeTiltRawMoment_zero_ne :
    thetaCuspSafeTiltRawMoment 0 ≠ 0 := by
  have hXi : XiC I ≠ 0 := by
    apply XiC_ne_zero_of_abs_re_le_nine_halves
    norm_num
  have hjet :=
    iteratedDeriv_XiC_I_eq_thetaCuspSafeTiltRawMoment 0
  simp only [iteratedDeriv_zero, pow_zero, one_mul] at hjet
  exact fun h => hXi (by rw [hjet, h]; simp)

/-- Mean of the normalized unit-tilted theta source. -/
def thetaCuspSafeTiltMean : ℝ :=
  thetaCuspSafeTiltRawMoment 1 / thetaCuspSafeTiltRawMoment 0

/-- Variance of the normalized unit-tilted theta source. -/
def thetaCuspSafeTiltVariance : ℝ :=
  thetaCuspSafeTiltRawMoment 2 / thetaCuspSafeTiltRawMoment 0 -
    thetaCuspSafeTiltMean ^ 2

/-- Third cumulant of the normalized unit-tilted theta source. -/
def thetaCuspSafeTiltThirdCumulant : ℝ :=
  thetaCuspSafeTiltRawMoment 3 / thetaCuspSafeTiltRawMoment 0 -
    3 * thetaCuspSafeTiltRawMoment 2 *
      thetaCuspSafeTiltRawMoment 1 /
        thetaCuspSafeTiltRawMoment 0 ^ 2 +
    2 * thetaCuspSafeTiltMean ^ 3

/-- Suzuki's normalization scale is the literal mean of the boundary-tilted theta source. -/
theorem thetaCuspSafeTiltMean_eq_xiRealLogDeriv_one :
    thetaCuspSafeTiltMean = xiRealLogDeriv 1 := by
  have h0 := iteratedDeriv_XiC_I_eq_thetaCuspSafeTiltRawMoment 0
  have h1 := iteratedDeriv_XiC_I_eq_thetaCuspSafeTiltRawMoment 1
  simp only [iteratedDeriv_zero, pow_zero, one_mul] at h0
  simp only [iteratedDeriv_one, pow_one] at h1
  rw [← xiHedenmalmDonoghueScale_eq_xiRealLogDeriv_one]
  rw [xiHedenmalmDonoghueScale, logDeriv_apply, h0, h1,
    thetaCuspSafeTiltMean]
  have hm0 := thetaCuspSafeTiltRawMoment_zero_ne
  simp [Complex.div_im]
  field_simp [hm0]

/-- The first logarithmic jet at the theta boundary is minus the literal tilted variance. -/
theorem deriv_logDeriv_XiC_I_eq_neg_thetaCuspSafeTiltVariance :
    deriv (logDeriv XiC) I =
      -(thetaCuspSafeTiltVariance : ℂ) := by
  have hXi : XiC I ≠ 0 := by
    apply XiC_ne_zero_of_abs_re_le_nine_halves
    norm_num
  have hXiAn : AnalyticAt ℂ XiC I :=
    XiC_analytic I (Set.mem_univ I)
  have hquot :=
    hXiAn.deriv.differentiableAt.hasDerivAt.div
      hXiAn.differentiableAt.hasDerivAt hXi
  have hformula :
      deriv (logDeriv XiC) I =
        (deriv (deriv XiC) I * XiC I -
            deriv XiC I * deriv XiC I) / XiC I ^ 2 := by
    change deriv (deriv XiC / XiC) I = _
    simpa only [pow_two] using hquot.deriv
  have h0 := iteratedDeriv_XiC_I_eq_thetaCuspSafeTiltRawMoment 0
  have h1 := iteratedDeriv_XiC_I_eq_thetaCuspSafeTiltRawMoment 1
  have h2 := iteratedDeriv_XiC_I_eq_thetaCuspSafeTiltRawMoment 2
  simp only [iteratedDeriv_zero, pow_zero, one_mul] at h0
  simp only [iteratedDeriv_one, pow_one] at h1
  have hderiv2 :
      deriv (deriv XiC) I = iteratedDeriv 2 XiC I := by
    rw [show iteratedDeriv 2 XiC I =
      deriv (iteratedDeriv 1 XiC) I by
        simpa using congrFun (iteratedDeriv_succ (n := 1) (f := XiC)) I,
      iteratedDeriv_one]
  rw [hformula, hderiv2, h0, h1, h2,
    thetaCuspSafeTiltVariance, thetaCuspSafeTiltMean]
  have hm0 := thetaCuspSafeTiltRawMoment_zero_ne
  push_cast
  field_simp [hm0]
  rw [Complex.I_sq]
  ring

/-- Literal boundary variance equals the second logarithmic Xi jet at `s = 3/2`. -/
theorem thetaCuspSafeTiltVariance_eq_deriv_xiRealLogDeriv_one :
    thetaCuspSafeTiltVariance = deriv xiRealLogDeriv 1 := by
  have hraw :=
    deriv_logDeriv_XiC_I_eq_neg_thetaCuspSafeTiltVariance
  have hxi := deriv_logDeriv_XiC_I_eq_neg
  have hneg :
      -(thetaCuspSafeTiltVariance : ℂ) =
        -deriv (logDeriv xi) (3 / 2 : ℂ) :=
    hraw.symm.trans hxi
  have hcomplex :
      (thetaCuspSafeTiltVariance : ℂ) =
        deriv (logDeriv xi) (3 / 2 : ℂ) :=
    neg_injective hneg
  have hreal := (hasDerivAt_xiRealLogDeriv (1 : ℝ)).deriv
  norm_num at hreal
  rw [← hcomplex] at hreal
  simpa using hreal.symm

/-- The second logarithmic jet at the theta boundary is `i` times the literal third cumulant. -/
theorem iteratedDeriv_two_logDeriv_XiC_I_eq_mul_I_thetaCuspSafeTiltThirdCumulant :
    iteratedDeriv 2 (logDeriv XiC) I =
      I * (thetaCuspSafeTiltThirdCumulant : ℂ) := by
  have hXi : XiC I ≠ 0 := by
    apply XiC_ne_zero_of_abs_re_le_nine_halves
    norm_num
  have hXiAn : AnalyticAt ℂ XiC I :=
    XiC_analytic I (Set.mem_univ I)
  let f₁ : ℂ → ℂ := deriv XiC
  let f₂ : ℂ → ℂ := deriv f₁
  have hf₀ : HasDerivAt XiC (f₁ I) I :=
    hXiAn.differentiableAt.hasDerivAt
  have hf₁ : HasDerivAt f₁ (f₂ I) I := by
    exact hXiAn.deriv.differentiableAt.hasDerivAt
  have hf₂ : HasDerivAt f₂ (deriv f₂ I) I := by
    exact hXiAn.deriv.deriv.differentiableAt.hasDerivAt
  let N : ℂ → ℂ := f₂ * XiC - f₁ * f₁
  let D : ℂ → ℂ := XiC ^ 2
  have hnum : HasDerivAt N
      (deriv f₂ I * XiC I + f₂ I * f₁ I -
        (f₂ I * f₁ I + f₁ I * f₂ I)) I := by
    dsimp only [N]
    exact (hf₂.mul hf₀).sub (hf₁.mul hf₁)
  have hden : HasDerivAt D
      ((2 : ℂ) * XiC I ^ (2 - 1) * f₁ I) I := by
    dsimp only [D]
    exact hf₀.pow 2
  have hDne : D I ≠ 0 := by
    dsimp only [D]
    exact pow_ne_zero 2 hXi
  have hquot := hnum.div hden hDne
  have hfirstEq :
      deriv (logDeriv XiC) =ᶠ[nhds I] N / D := by
    filter_upwards [hXiAn.continuousAt.eventually_ne hXi] with z hz
    have hzAn : AnalyticAt ℂ XiC z :=
      XiC_analytic z (Set.mem_univ z)
    have hzquot :=
      hzAn.deriv.differentiableAt.hasDerivAt.div
        hzAn.differentiableAt.hasDerivAt hz
    change deriv (deriv XiC / XiC) z = (N / D) z
    simpa only [N, D, f₁, f₂, Pi.div_apply, Pi.mul_apply,
      Pi.sub_apply, Pi.pow_apply, pow_two] using hzquot.deriv
  have hformula :
      iteratedDeriv 2 (logDeriv XiC) I =
        (deriv f₂ I * XiC I ^ 2 -
            3 * f₂ I * f₁ I * XiC I +
            2 * f₁ I ^ 3) / XiC I ^ 3 := by
    rw [show iteratedDeriv 2 (logDeriv XiC) I =
      deriv (deriv (logDeriv XiC)) I by
        rw [show iteratedDeriv 2 (logDeriv XiC) I =
          deriv (iteratedDeriv 1 (logDeriv XiC)) I by
            simpa using congrFun
              (iteratedDeriv_succ (n := 1) (f := logDeriv XiC)) I,
          iteratedDeriv_one],
      hfirstEq.deriv_eq, hquot.deriv]
    dsimp only [N, D] at *
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply] at *
    field_simp [hXi]
    ring
  have h0 := iteratedDeriv_XiC_I_eq_thetaCuspSafeTiltRawMoment 0
  have h1 := iteratedDeriv_XiC_I_eq_thetaCuspSafeTiltRawMoment 1
  have h2 := iteratedDeriv_XiC_I_eq_thetaCuspSafeTiltRawMoment 2
  have h3 := iteratedDeriv_XiC_I_eq_thetaCuspSafeTiltRawMoment 3
  simp only [iteratedDeriv_zero, pow_zero, one_mul] at h0
  simp only [iteratedDeriv_one, pow_one] at h1
  have hf₂_eq : f₂ I = iteratedDeriv 2 XiC I := by
    dsimp only [f₂, f₁]
    rw [show iteratedDeriv 2 XiC I =
      deriv (iteratedDeriv 1 XiC) I by
        simpa using congrFun (iteratedDeriv_succ (n := 1) (f := XiC)) I,
      iteratedDeriv_one]
  have hdf₂_eq : deriv f₂ I = iteratedDeriv 3 XiC I := by
    dsimp only [f₂, f₁]
    rw [show iteratedDeriv 3 XiC I =
      deriv (iteratedDeriv 2 XiC) I by
        simpa using congrFun (iteratedDeriv_succ (n := 2) (f := XiC)) I]
    congr 1
    funext z
    rw [show iteratedDeriv 2 XiC z =
      deriv (iteratedDeriv 1 XiC) z by
        simpa using congrFun (iteratedDeriv_succ (n := 1) (f := XiC)) z,
      iteratedDeriv_one]
  rw [hformula, h0, show f₁ I = deriv XiC I by rfl, h1,
    hf₂_eq, h2, hdf₂_eq, h3, thetaCuspSafeTiltThirdCumulant,
    thetaCuspSafeTiltMean]
  have hm0 := thetaCuspSafeTiltRawMoment_zero_ne
  push_cast
  field_simp [hm0]
  rw [Complex.I_sq]
  ring

/-- Literal boundary third cumulant equals the third logarithmic Xi jet at `s = 3/2`. -/
theorem thetaCuspSafeTiltThirdCumulant_eq_deriv2_xiRealLogDeriv_one :
    thetaCuspSafeTiltThirdCumulant =
      deriv (deriv xiRealLogDeriv) 1 := by
  have hraw :=
    iteratedDeriv_two_logDeriv_XiC_I_eq_mul_I_thetaCuspSafeTiltThirdCumulant
  have hxi := iteratedDeriv_two_logDeriv_XiC_I_eq
  rw [iteratedDeriv_two_logDeriv_xi_threeHalves_eq_ofReal] at hxi
  have hmul :
      I * (thetaCuspSafeTiltThirdCumulant : ℂ) =
        I * ((deriv (deriv xiRealLogDeriv) 1 : ℝ) : ℂ) :=
    hraw.symm.trans hxi
  have hcomplex :
      (thetaCuspSafeTiltThirdCumulant : ℂ) =
        ((deriv (deriv xiRealLogDeriv) 1 : ℝ) : ℂ) :=
    mul_left_cancel₀ I_ne_zero hmul
  exact_mod_cast hcomplex

/-- Suzuki's safe minor is exactly one skewness budget for the literal boundary theta law. -/
theorem eight_mul_suzukiSafeMinor_eq_thetaCuspSafeTiltSkewnessBudget :
    8 *
        ((xiShiftedReciprocalMoment 1 0).re *
            (xiShiftedReciprocalMoment 1 2).re -
          (xiShiftedReciprocalMoment 1 1).re ^ 2) =
      thetaCuspSafeTiltMean * thetaCuspSafeTiltThirdCumulant +
        (thetaCuspSafeTiltMean - thetaCuspSafeTiltVariance) *
          (thetaCuspSafeTiltMean + 2 * thetaCuspSafeTiltVariance) := by
  rw [thetaCuspSafeTiltMean_eq_xiRealLogDeriv_one,
    thetaCuspSafeTiltVariance_eq_deriv_xiRealLogDeriv_one,
    thetaCuspSafeTiltThirdCumulant_eq_deriv2_xiRealLogDeriv_one,
    xiRealLogDeriv_eq_mul_re_xiShiftedReciprocalMoment (by norm_num),
    deriv_xiRealLogDeriv_one_eq, deriv2_xiRealLogDeriv_one_eq]
  norm_num
  ring

/-- Exact source-side form of Suzuki's safe wall. -/
theorem suzukiSafeMinor_nonneg_iff_thetaCuspSafeTiltSkewnessBudget :
    0 ≤
        (xiShiftedReciprocalMoment 1 0).re *
            (xiShiftedReciprocalMoment 1 2).re -
          (xiShiftedReciprocalMoment 1 1).re ^ 2 ↔
      -thetaCuspSafeTiltMean * thetaCuspSafeTiltThirdCumulant ≤
        (thetaCuspSafeTiltMean - thetaCuspSafeTiltVariance) *
          (thetaCuspSafeTiltMean + 2 * thetaCuspSafeTiltVariance) := by
  have h :=
    eight_mul_suzukiSafeMinor_eq_thetaCuspSafeTiltSkewnessBudget
  constructor <;> intro hs
  · nlinarith
  · nlinarith

/-- The already-proved first Suzuki defect becomes a strict mean-minus-variance gap of the
literal boundary theta law. -/
theorem thetaCuspSafeTiltVariance_lt_mean :
    thetaCuspSafeTiltVariance < thetaCuspSafeTiltMean := by
  rw [thetaCuspSafeTiltMean_eq_xiRealLogDeriv_one,
    thetaCuspSafeTiltVariance_eq_deriv_xiRealLogDeriv_one,
    xiRealLogDeriv_eq_mul_re_xiShiftedReciprocalMoment (by norm_num),
    deriv_xiRealLogDeriv_one_eq]
  norm_num
  have hB := re_xiShiftedReciprocalMoment_pos
    (y := (1 : ℝ)) (by norm_num) (n := 1) (by norm_num)
  linarith

/-! ## Full-support endpoint moment geometry -/

/-- Positive measure represented by the theta source at Suzuki's unit exponential tilt. -/
def thetaCuspSafeTiltMeasure : Measure ℝ :=
  volume.withDensity fun x =>
    ENNReal.ofReal (Real.exp x * thetaCuspFullSource x)

private theorem measurable_thetaCuspSafeTiltDensity :
    Measurable (fun x : ℝ =>
      ENNReal.ofReal (Real.exp x * thetaCuspFullSource x)) := by
  exact ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.mul
      contDiff_thetaCuspFullSource.continuous).measurable

private theorem thetaCuspSafeTiltDensity_pos (x : ℝ) :
    0 < Real.exp x * thetaCuspFullSource x :=
  mul_pos (Real.exp_pos x) (thetaCuspFullSource_pos_all x)

/-- Every polynomial monomial is integrable in the endpoint tilted theta state. -/
theorem integrable_pow_thetaCuspSafeTiltMeasure (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) thetaCuspSafeTiltMeasure := by
  rw [thetaCuspSafeTiltMeasure,
    integrable_withDensity_iff_integrable_smul₀'
      measurable_thetaCuspSafeTiltDensity.aemeasurable
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (thetaCuspSafeTiltDensity_pos _).le,
    smul_eq_mul]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    integrable_thetaCuspSafeTiltRawMoment k

/-- The safe-tilt raw sequence is the moment sequence of its positive endpoint measure. -/
theorem thetaCuspSafeTiltRawMoment_eq_integral_measure (k : ℕ) :
    thetaCuspSafeTiltRawMoment k =
      ∫ x : ℝ, x ^ k ∂thetaCuspSafeTiltMeasure := by
  rw [thetaCuspSafeTiltMeasure,
    integral_withDensity_eq_integral_toReal_smul
      measurable_thetaCuspSafeTiltDensity
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (thetaCuspSafeTiltDensity_pos _).le,
    smul_eq_mul]
  rw [thetaCuspSafeTiltRawMoment]
  apply integral_congr_ae
  filter_upwards with x
  ring

private theorem thetaCuspSafeTiltMeasure_compl_finset_pos
    (F : Finset ℝ) :
    0 < thetaCuspSafeTiltMeasure {x : ℝ | x ∉ F} := by
  classical
  rw [pos_iff_ne_zero]
  intro hzero
  have hpos : ∀ᵐ x : ℝ ∂volume,
      ENNReal.ofReal (Real.exp x * thetaCuspFullSource x) ≠ 0 := by
    filter_upwards with x
    exact (ENNReal.ofReal_pos.mpr (thetaCuspSafeTiltDensity_pos x)).ne'
  have hvolcomp : volume {x : ℝ | x ∉ F} = 0 := by
    apply (GaloisForLFunctions.HTGeometry.measure_withDensity_eq_zero_iff
      volume measurable_thetaCuspSafeTiltDensity hpos _).mp
    exact hzero
  have hF : volume (↑F : Set ℝ) = 0 := F.measure_zero volume
  have huniv : (volume : Measure ℝ) Set.univ = 0 := by
    rw [show Set.univ = (↑F : Set ℝ) ∪ {x : ℝ | x ∉ F} by
      ext x
      constructor
      · intro _
        exact Classical.em (x ∈ F)
      · intro _
        exact Set.mem_univ x]
    exact measure_union_null hF hvolcomp
  simp at huniv

/-- Every finite Hankel block of Suzuki's endpoint tilted theta moments is positive definite. -/
theorem thetaCuspSafeTilt_momentHankelMatrix_posDef (n : ℕ) :
    (HTGeometry.momentHankelMatrix thetaCuspSafeTiltRawMoment n).PosDef :=
  HTGeometry.momentHankelMatrix_posDef_of_infiniteSupport
    thetaCuspSafeTiltRawMoment thetaCuspSafeTiltRawMoment_eq_integral_measure
      integrable_pow_thetaCuspSafeTiltMeasure
      thetaCuspSafeTiltMeasure_compl_finset_pos n

/-- Every finite Hankel determinant of the endpoint tilted theta moments is strictly positive. -/
theorem det_thetaCuspSafeTilt_momentHankelMatrix_pos (n : ℕ) :
    0 <
      (HTGeometry.momentHankelMatrix thetaCuspSafeTiltRawMoment n).det :=
  (thetaCuspSafeTilt_momentHankelMatrix_posDef n).det_pos

theorem thetaCuspSafeTiltRawMoment_zero_pos :
    0 < thetaCuspSafeTiltRawMoment 0 := by
  have hdet := det_thetaCuspSafeTilt_momentHankelMatrix_pos 1
  simpa [HTGeometry.momentHankelMatrix] using hdet

theorem thetaCuspSafeTiltMean_pos :
    0 < thetaCuspSafeTiltMean := by
  rw [thetaCuspSafeTiltMean_eq_xiRealLogDeriv_one,
    ← xiHedenmalmDonoghueScale_eq_xiRealLogDeriv_one]
  exact xiHedenmalmDonoghueScale_pos

/-- The full-support endpoint moment law discharges strict positivity of the safe-tilt variance. -/
theorem thetaCuspSafeTiltVariance_pos :
    0 < thetaCuspSafeTiltVariance := by
  have hdet := det_thetaCuspSafeTilt_momentHankelMatrix_pos 2
  have hraw :
      0 <
        thetaCuspSafeTiltRawMoment 0 *
            thetaCuspSafeTiltRawMoment 2 -
          thetaCuspSafeTiltRawMoment 1 ^ 2 := by
    simpa [HTGeometry.momentHankelMatrix, Matrix.det_fin_two, pow_two] using hdet
  have hzero := thetaCuspSafeTiltRawMoment_zero_pos
  rw [thetaCuspSafeTiltVariance, thetaCuspSafeTiltMean]
  have hid :
      thetaCuspSafeTiltRawMoment 2 / thetaCuspSafeTiltRawMoment 0 -
          (thetaCuspSafeTiltRawMoment 1 /
            thetaCuspSafeTiltRawMoment 0) ^ 2 =
        (thetaCuspSafeTiltRawMoment 0 *
              thetaCuspSafeTiltRawMoment 2 -
            thetaCuspSafeTiltRawMoment 1 ^ 2) /
          thetaCuspSafeTiltRawMoment 0 ^ 2 := by
    field_simp [hzero.ne']
  rw [hid]
  exact div_pos hraw (sq_pos_of_pos hzero)

/-- Suzuki's endpoint tilted theta law has strictly negative third cumulant. -/
theorem thetaCuspSafeTiltThirdCumulant_neg :
    thetaCuspSafeTiltThirdCumulant < 0 := by
  rw [thetaCuspSafeTiltThirdCumulant_eq_deriv2_xiRealLogDeriv_one,
    deriv2_xiRealLogDeriv_one_eq]
  have hM1 := re_xiShiftedReciprocalMoment_pos
    (y := (1 : ℝ)) (by norm_num) (n := 1) (by norm_num)
  have hratio :=
    eightyFive_mul_re_xiShiftedReciprocalMoment_two_lt_four_mul_one
  nlinarith

/-- Exact unconditional sign chamber of the first three endpoint theta cumulants. -/
theorem thetaCuspSafeTilt_cumulantSignChamber :
    0 < thetaCuspSafeTiltMean ∧
      0 < thetaCuspSafeTiltVariance ∧
        thetaCuspSafeTiltThirdCumulant < 0 ∧
          thetaCuspSafeTiltVariance < thetaCuspSafeTiltMean :=
  ⟨thetaCuspSafeTiltMean_pos, thetaCuspSafeTiltVariance_pos,
    thetaCuspSafeTiltThirdCumulant_neg, thetaCuspSafeTiltVariance_lt_mean⟩

end

end RHTower
