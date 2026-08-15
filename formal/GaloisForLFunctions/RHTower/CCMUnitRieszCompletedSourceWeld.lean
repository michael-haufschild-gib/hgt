import GaloisForLFunctions.RHTower.CCMUnitRieszMarkovTransform
import GaloisForLFunctions.RHTower.CCMInverseTiltedCriticalMellinFactorization
import GaloisForLFunctions.RHTower.AnalyticDividedDifference
import GaloisForLFunctions.RHTower.ChebyshevPsiLogSummatory
import GaloisForLFunctions.RHTower.CCMPolarPrimeStieltjesAutocorrelation

/-!
# Unit-Riesz completed-source weld

The unit-Riesz coefficient admits an exact pole-filled factorization through the completed
critical-Mellin defect.  The remaining source-free term is the Laplace product of a positive
two-exponential kernel and an explicit Stirling-floor correction.  This file proves the complex
factorization and the strict sign and two-sided exponential bounds for that correction.

These are unconditional identities and inequalities.  No zero-free conclusion or RH claim is
made here.
-/

open Complex Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Zero-free aperture multiplier relating the unit-Riesz coefficient to the completed source. -/
def unitRieszCompletedSourceMultiplier (z : ℂ) : ℂ :=
  3 / (2 * (z + 1) * (z + 3 / 2))

/-- Pole-filled zeta profile whose divided difference is the elementary unit-Riesz correction. -/
def unitRieszPoleFilledZetaProfile (z : ℂ) : ℂ :=
  RHTower.regularizedRiemannZeta (1 + z) / (1 + z) ^ 2

/-- Holomorphic source-free correction after the critical-Mellin defect is removed. -/
def unitRieszCompletedSourceCorrection (z : ℂ) : ℂ :=
  unitRieszCompletedSourceMultiplier z *
    (dslope unitRieszPoleFilledZetaProfile 0 z - 1 / (z + 1))

/-- Pole-filled continuation of the complete unit-Riesz coefficient transform. -/
def unitRieszPoleFilledCoefficient (z : ℂ) : ℂ :=
  unitRieszCompletedSourceMultiplier z *
    (logDeriv RHTower.regularizedRiemannZeta (1 + z) +
      dslope unitRieszPoleFilledZetaProfile 0 z)

/-- Exact completed-source factorization, valid globally as a value identity. -/
theorem unitRieszPoleFilledCoefficient_eq_completedSource (z : ℂ) :
    unitRieszPoleFilledCoefficient z =
      unitRieszCompletedSourceMultiplier z *
          RHTower.regularizedCriticalMellinDefect z +
        unitRieszCompletedSourceCorrection z := by
  rw [unitRieszPoleFilledCoefficient, unitRieszCompletedSourceCorrection,
    RHTower.regularizedCriticalMellinDefect]
  ring_nf

theorem analyticAt_unitRieszCompletedSourceMultiplier
    {z : ℂ} (hz : -1 / 2 < z.re) :
    AnalyticAt ℂ unitRieszCompletedSourceMultiplier z := by
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re] at hre
    linarith
  have hz3 : z + 3 / 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re] at hre
    linarith
  unfold unitRieszCompletedSourceMultiplier
  exact analyticAt_const.div (by fun_prop)
    (mul_ne_zero (mul_ne_zero two_ne_zero hz1) hz3)

theorem unitRieszCompletedSourceMultiplier_ne_zero
    {z : ℂ} (hz : -1 / 2 < z.re) :
    unitRieszCompletedSourceMultiplier z ≠ 0 := by
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re] at hre
    linarith
  have hz3 : z + 3 / 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re] at hre
    linarith
  unfold unitRieszCompletedSourceMultiplier
  exact div_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero two_ne_zero hz1) hz3)

theorem analyticAt_unitRieszPoleFilledZetaProfile
    {z : ℂ} (hz : z + 1 ≠ 0) :
    AnalyticAt ℂ unitRieszPoleFilledZetaProfile z := by
  have hreg : AnalyticAt ℂ RHTower.regularizedRiemannZeta (1 + z) :=
    RHTower.differentiable_regularizedRiemannZeta.analyticAt _
  have hshift : AnalyticAt ℂ (fun w : ℂ => 1 + w) z := by fun_prop
  have hnum : AnalyticAt ℂ
      (fun w : ℂ => RHTower.regularizedRiemannZeta (1 + w)) z :=
    hreg.comp_of_eq hshift rfl
  have hz' : 1 + z ≠ 0 := by simpa [add_comm] using hz
  unfold unitRieszPoleFilledZetaProfile
  exact hnum.div (hshift.pow 2) (pow_ne_zero 2 hz')

theorem analyticAt_unitRieszCompletedSourceCorrection
    {z : ℂ} (hz : -1 / 2 < z.re) :
    AnalyticAt ℂ unitRieszCompletedSourceCorrection z := by
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re] at hre
    linarith
  have hprofile0 : AnalyticAt ℂ unitRieszPoleFilledZetaProfile 0 :=
    analyticAt_unitRieszPoleFilledZetaProfile (by norm_num)
  have hprofilez : AnalyticAt ℂ unitRieszPoleFilledZetaProfile z :=
    analyticAt_unitRieszPoleFilledZetaProfile hz1
  have hds : AnalyticAt ℂ (dslope unitRieszPoleFilledZetaProfile 0) z :=
    RHTower.analyticAt_dslope_of_analyticAt hprofile0 hprofilez
  have hrat : AnalyticAt ℂ (fun w : ℂ => 1 / (w + 1)) z :=
    analyticAt_const.div (by fun_prop) hz1
  exact (analyticAt_unitRieszCompletedSourceMultiplier hz).mul (hds.sub hrat)

/-- On the convergent half-plane, the pole-filled coefficient is the original zeta/log-derivative
formula. -/
theorem unitRieszPoleFilledCoefficient_eq_original
    {z : ℂ} (hz : 0 < z.re) :
    unitRieszPoleFilledCoefficient z =
      unitRieszCompletedSourceMultiplier z *
        (riemannZeta (1 + z) / (1 + z) ^ 2 +
          deriv riemannZeta (1 + z) / riemannZeta (1 + z)) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    norm_num at hz
  have hz1 : 1 + z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re] at hre
    linarith
  have ht1 : 1 + z ≠ 1 := by
    intro h
    exact hz0 (by linear_combination h)
  have hzeta : riemannZeta (1 + z) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by
      rw [Complex.add_re]
      norm_num
      linarith)
  have hprofile0 : unitRieszPoleFilledZetaProfile 0 = 1 := by
    norm_num [unitRieszPoleFilledZetaProfile, RHTower.regularizedRiemannZeta_one]
  have hlog := RHTower.logDeriv_regularizedRiemannZeta_eq ht1 hzeta
  rw [unitRieszPoleFilledCoefficient, hlog, RHTower.zetaLogDeriv]
  rw [dslope_of_ne _ hz0, slope_def_field]
  rw [unitRieszPoleFilledZetaProfile, hprofile0,
    RHTower.regularizedRiemannZeta_of_ne_one ht1]
  field_simp
  ring

/-! ## Explicit inverse correction and its sign -/

def unitRieszStirlingLogHead (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, Real.log n

def unitRieszStirlingCorrection (t : ℝ) : ℝ :=
  Real.exp (-t) *
      ((⌊Real.exp t⌋₊ : ℝ) * t - unitRieszStirlingLogHead t) -
    1 - Real.exp (-t)

theorem unitRieszStirlingCorrection_eq_factored (t : ℝ) :
    unitRieszStirlingCorrection t =
      Real.exp (-t) *
        ((⌊Real.exp t⌋₊ : ℝ) * t - unitRieszStirlingLogHead t -
          Real.exp t - 1) := by
  have hexp : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]
    simp
  rw [unitRieszStirlingCorrection]
  nlinarith

theorem unitRieszStirlingCorrection_le
    {t : ℝ} (ht : 0 ≤ t) :
    unitRieszStirlingCorrection t ≤ -2 * Real.exp (-t) := by
  let N : ℕ := ⌊Real.exp t⌋₊
  let x : ℝ := Real.exp t
  have hx : 0 < x := Real.exp_pos t
  have hN1 : 1 ≤ N := by
    exact Nat.le_floor (by simpa [x] using Real.one_le_exp ht)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
  have hNx : (N : ℝ) ≤ x := by
    exact Nat.floor_le hx.le
  have hratio : 0 < x / (N : ℝ) := div_pos hx hNpos
  have hlog := Real.log_le_sub_one_of_pos hratio
  have hlog' : t - Real.log (N : ℝ) ≤ x / (N : ℝ) - 1 := by
    rw [Real.log_div hx.ne' hNpos.ne', show Real.log x = t by simp [x]] at hlog
    exact hlog
  have hmul := mul_le_mul_of_nonneg_left hlog' hNpos.le
  have htangent : (N : ℝ) * t - x ≤
      (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) := by
    have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
    field_simp [hNne] at hmul
    linarith
  have hsum : (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1 ≤
      unitRieszStirlingLogHead t := by
    simpa [unitRieszStirlingLogHead, N] using RHTower.stirling_le_sum_log N hN1
  have hbracket :
      (N : ℝ) * t - unitRieszStirlingLogHead t - x - 1 ≤ -2 := by
    linarith
  rw [unitRieszStirlingCorrection_eq_factored]
  change Real.exp (-t) *
      ((N : ℝ) * t - unitRieszStirlingLogHead t - x - 1) ≤
    -2 * Real.exp (-t)
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left hbracket (Real.exp_pos (-t)).le)

theorem unitRieszStirlingCorrection_neg
    {t : ℝ} (ht : 0 ≤ t) : unitRieszStirlingCorrection t < 0 := by
  have h := unitRieszStirlingCorrection_le ht
  have he : 0 < Real.exp (-t) := Real.exp_pos _
  linarith

theorem unitRieszStirlingCorrection_lower
    {t : ℝ} (ht : 0 ≤ t) :
    -(t + 4) * Real.exp (-t) ≤ unitRieszStirlingCorrection t := by
  let N : ℕ := ⌊Real.exp t⌋₊
  let x : ℝ := Real.exp t
  have hx : 0 < x := Real.exp_pos t
  have hN1 : 1 ≤ N := by
    exact Nat.le_floor (by simpa [x] using Real.one_le_exp ht)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx.le
  have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlogN : Real.log (N : ℝ) ≤ t := by
    have h := Real.log_le_log hNpos hNx
    simpa [x] using h
  have hNt : (N : ℝ) * Real.log (N : ℝ) ≤ (N : ℝ) * t :=
    mul_le_mul_of_nonneg_left hlogN hNpos.le
  have hbase :
      (N : ℝ) * Real.log (N : ℝ) - ((N : ℝ) + 1) ≤
        (N : ℝ) * t - x := by
    linarith
  have hsum : unitRieszStirlingLogHead t ≤
      ((N : ℝ) + 1) * Real.log ((N : ℝ) + 1) - ((N : ℝ) + 1) + 1 := by
    simpa [unitRieszStirlingLogHead, N] using RHTower.sum_log_le_stirling N hN1
  have hNp : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have htwoX : (N : ℝ) + 1 ≤ 2 * x := by
    have hxone : 1 ≤ x := by simpa [x] using Real.one_le_exp ht
    linarith
  have hlogNp : Real.log ((N : ℝ) + 1) ≤ t + 1 := by
    have hmono := Real.log_le_log hNp htwoX
    have hlogtwo : Real.log (2 : ℝ) ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      exact h
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx.ne',
      show Real.log x = t by simp [x]] at hmono
    linarith
  have hratio : 0 < ((N : ℝ) + 1) / (N : ℝ) := div_pos hNp hNpos
  have hlogratio := Real.log_le_sub_one_of_pos hratio
  have hloggap :
      (N : ℝ) * (Real.log ((N : ℝ) + 1) - Real.log (N : ℝ)) ≤ 1 := by
    rw [← Real.log_div hNp.ne' hNpos.ne']
    have hmul := mul_le_mul_of_nonneg_left hlogratio hNpos.le
    have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
    field_simp [hNne] at hmul
    linarith
  have hD :
      ((N : ℝ) + 1) * Real.log ((N : ℝ) + 1) -
          (N : ℝ) * Real.log (N : ℝ) ≤ t + 2 := by
    calc
      ((N : ℝ) + 1) * Real.log ((N : ℝ) + 1) -
          (N : ℝ) * Real.log (N : ℝ) =
        Real.log ((N : ℝ) + 1) +
          (N : ℝ) * (Real.log ((N : ℝ) + 1) - Real.log (N : ℝ)) := by ring
      _ ≤ (t + 1) + 1 := add_le_add hlogNp hloggap
      _ = t + 2 := by ring
  have hbracket :
      -(t + 4) ≤
        (N : ℝ) * t - unitRieszStirlingLogHead t - x - 1 := by
    linarith
  rw [unitRieszStirlingCorrection_eq_factored]
  change -(t + 4) * Real.exp (-t) ≤
    Real.exp (-t) *
      ((N : ℝ) * t - unitRieszStirlingLogHead t - x - 1)
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left hbracket (Real.exp_pos (-t)).le)

/-- Positive two-exponential aperture kernel with Laplace multiplier
`3 / (2(z+1)(z+3/2))`. -/
def unitRieszCompletedSourceKernel (t : ℝ) : ℝ :=
  3 * (Real.exp (-t) - Real.exp (-3 * t / 2))

theorem unitRieszCompletedSourceKernel_nonneg
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ unitRieszCompletedSourceKernel t := by
  have h := Real.exp_le_exp.mpr (show -3 * t / 2 ≤ -t by linarith)
  unfold unitRieszCompletedSourceKernel
  positivity

theorem unitRieszCompletedSourceKernel_le
    {t : ℝ} (_ht : 0 ≤ t) :
    unitRieszCompletedSourceKernel t ≤ 3 * Real.exp (-t) := by
  have hpos : 0 ≤ Real.exp (-3 * t / 2) := (Real.exp_pos _).le
  unfold unitRieszCompletedSourceKernel
  linarith

/-! ## Literal completed-source response -/

/-- Smooth finite-aperture test realizing the unit-Riesz completed-source response. -/
def unitRieszCompletedSourceTest (t h : ℝ) : ℂ :=
  Complex.ofReal
    (3 * (Real.exp (-t + h / 2) - Real.exp (-3 * t / 2 + h)))

/-- Derivative of the finite-aperture unit-Riesz source test. -/
def unitRieszCompletedSourceTestDeriv (t h : ℝ) : ℂ :=
  Complex.ofReal ((3 / 2 : ℝ) * Real.exp (-t + h / 2) -
    3 * Real.exp (-3 * t / 2 + h))

theorem hasDerivAt_unitRieszCompletedSourceTest (t h : ℝ) :
    HasDerivAt (unitRieszCompletedSourceTest t)
      (unitRieszCompletedSourceTestDeriv t h) h := by
  have h₁ : HasDerivAt (fun x : ℝ => Real.exp (-t + x / 2))
      ((1 / 2 : ℝ) * Real.exp (-t + h / 2)) h := by
    simpa only [Function.comp_def, id_eq, mul_comm] using
      (Real.hasDerivAt_exp (-t + h / 2)).comp h
        (((hasDerivAt_id h).div_const 2).const_add (-t))
  have h₂ : HasDerivAt (fun x : ℝ => Real.exp (-3 * t / 2 + x))
      (Real.exp (-3 * t / 2 + h)) h := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      (Real.hasDerivAt_exp (-3 * t / 2 + h)).comp h
        ((hasDerivAt_id h).const_add (-3 * t / 2))
  have hr := (h₁.sub h₂).const_mul 3
  have hc := hr.ofReal_comp
  convert hc using 1
  · funext y
    simp only [unitRieszCompletedSourceTest, Pi.sub_apply,
      Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
  · simp only [unitRieszCompletedSourceTestDeriv, Complex.ofReal_sub,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_div,
      Complex.ofReal_one]
    ring

theorem unitRieszCompletedSourceTest_eq_kernel (t h : ℝ) :
    unitRieszCompletedSourceTest t h =
      Complex.ofReal
        (Real.exp (-h / 2) * unitRieszCompletedSourceKernel (t - h)) := by
  change Complex.ofReal _ = Complex.ofReal _
  congr 1
  simp only [unitRieszCompletedSourceKernel]
  have he1 : Real.exp (-h / 2) * Real.exp (-(t - h)) =
      Real.exp (-t + h / 2) := by rw [← Real.exp_add]; congr 1; ring
  have he2 : Real.exp (-h / 2) * Real.exp (-3 * (t - h) / 2) =
      Real.exp (-3 * t / 2 + h) := by rw [← Real.exp_add]; congr 1; ring
  rw [← he1, ← he2]
  ring

/-- Literal completed Euler--Gamma Stieltjes response seen by the unit-Riesz aperture. -/
def unitRieszCompletedSourceResponse (t : ℝ) : ℂ :=
  RHTower.criticalMellinStieltjesPairing (t / 2)
    (unitRieszCompletedSourceTest t)

theorem unitRieszCompletedSourceTest_endpoint (t : ℝ) :
    unitRieszCompletedSourceTest t t = 0 := by
  rw [unitRieszCompletedSourceTest_eq_kernel]
  norm_num [unitRieszCompletedSourceKernel]

theorem unitRieszCompletedSourceResponse_eq_errorIntegral
    {t : ℝ} (ht : 0 ≤ t) :
    unitRieszCompletedSourceResponse t =
      -(∫ h in Set.Ioc (0 : ℝ) t,
        (RHTower.criticalMellinCompletedError h : ℂ) *
          unitRieszCompletedSourceTestDeriv t h) := by
  rw [unitRieszCompletedSourceResponse]
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) (2 * (t / 2)),
      HasDerivAt (unitRieszCompletedSourceTest t)
        (unitRieszCompletedSourceTestDeriv t x) x := by
    intro x _
    exact hasDerivAt_unitRieszCompletedSourceTest t x
  have hint : IntervalIntegrable (unitRieszCompletedSourceTestDeriv t) volume
      0 (2 * (t / 2)) := by
    have hc : Continuous (unitRieszCompletedSourceTestDeriv t) := by
      unfold unitRieszCompletedSourceTestDeriv
      fun_prop
    exact hc.intervalIntegrable 0 (2 * (t / 2))
  have hibp := RHTower.criticalMellinStieltjesPairing_integrationByParts
    (a := t / 2) (by linarith) hderiv hint
    (by rw [show 2 * (t / 2) = t by ring]; exact unitRieszCompletedSourceTest_endpoint t)
  simpa only [show 2 * (t / 2) = t by ring] using hibp

/-- The source response is exactly a difference of two exponentially weighted completed-error
moments; no Möbius coordinate remains. -/
theorem unitRieszCompletedSourceResponse_eq_twoMomentIntegral
    {t : ℝ} (ht : 0 ≤ t) :
    unitRieszCompletedSourceResponse t =
      ∫ h in Set.Ioc (0 : ℝ) t,
        (RHTower.criticalMellinCompletedError h : ℂ) *
          ((3 * Real.exp (-3 * t / 2 + h) -
            (3 / 2 : ℝ) * Real.exp (-t + h / 2) : ℝ) : ℂ) := by
  rw [unitRieszCompletedSourceResponse_eq_errorIntegral ht,
    ← MeasureTheory.integral_neg]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with h
  rw [unitRieszCompletedSourceTestDeriv]
  push_cast
  ring

end GaloisForLFunctions.RHTower

end
