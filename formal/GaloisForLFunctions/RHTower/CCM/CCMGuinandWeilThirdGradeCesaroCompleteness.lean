import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilThirdGradeAbelCompleteness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Third-grade Cesàro completeness

One further primitive strictly enlarges the CCM--FU completion class.  If the primitive of the
literal prime-minus-polar third-grade cumulative source has only linear growth, a second Abel
transform is analytic on `Re u > 0`.  Finite-interval absolute-continuity integration by parts and
an identity theorem recover the original third-grade Abel transform on `Re u > 1`.  Three complex
derivatives therefore expose the same critical Mellin defect, so the continuation argument reaches
`Re s > -1/2` and forces RH.

This criterion permits large oscillatory cumulative sources excluded by pointwise boundedness and
by every fixed subcubic pointwise envelope.  Contrapositively, failure of RH forces the Cesàro
primitive to beat every linear coefficient somewhere beyond every positive wall.
-/

open Complex Filter Function Set MeasureTheory Topology
open GaloisForLFunctions

namespace RHTower

noncomputable section

set_option maxHeartbeats 50000

def ccmCesaroPrimitive (q : ℝ → ℝ) (b H : ℝ) : ℝ :=
  ∫ h in b..H, q h

def ccmSecondAbelLaplaceTail (q : ℝ → ℝ) (b : ℝ) (u : ℂ) : ℂ :=
  ∫ H : ℝ in Set.Ioi b,
    Complex.exp (-u * (H : ℂ)) * (ccmCesaroPrimitive q b H : ℂ)

def ccmSecondAbelCumulativeSourceContinuation
    (q : ℝ → ℝ) (b : ℝ) (u : ℂ) : ℂ :=
  u ^ 2 * ccmSecondAbelLaplaceTail q b u

theorem intervalIntegrable_thirdGradeCumulative
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    IntervalIntegrable
      (ccmGuinandWeilThirdGradeCumulativeMeasurable b) volume b H := by
  let K : ℝ := (32 / b ^ 2) * Real.exp H +
      (64 / b ^ 3) * H * Real.exp (H / 2)
  have hH0 : 0 ≤ H := (hb.trans_le hbH).le
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => K) volume b H).mono_fun
  · exact (measurable_ccmGuinandWeilThirdGradeCumulativeMeasurable hb).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
    rw [uIoc_of_le hbH] at hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hK,
      ccmGuinandWeilThirdGradeCumulativeMeasurable_eq_primePolar hx.1.le,
      ccmGuinandWeilPrimePolarWeightedWindow_thirdGrade_eq_prime_sub_polar]
    have hp0 := ccmGuinandWeilPrimeThirdGradeRateWindow_nonneg
      (b := b) (H := x)
    have hr0 := ccmGuinandWeilPolarThirdGradeRateWindow_nonneg hb hx.1.le
    have hp := ccmGuinandWeilPrimeThirdGradeRateWindow_le hb x
    have hr := ccmGuinandWeilPolarThirdGradeRateWindow_le hb hx.1.le
    have hex : Real.exp x ≤ Real.exp H := Real.exp_le_exp.mpr hx.2
    have hxh : x * Real.exp (x / 2) ≤ H * Real.exp (H / 2) := by
      have hx0 : 0 ≤ x := (hb.trans hx.1).le
      calc
        x * Real.exp (x / 2) ≤ H * Real.exp (x / 2) :=
          mul_le_mul_of_nonneg_right hx.2 (Real.exp_nonneg _)
        _ ≤ H * Real.exp (H / 2) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr
              (div_le_div_of_nonneg_right hx.2 (by norm_num))) hH0
    calc
      |ccmGuinandWeilPrimeThirdGradeRateWindow b x -
          ccmGuinandWeilPolarThirdGradeRateWindow b x| ≤
          ccmGuinandWeilPrimeThirdGradeRateWindow b x +
            ccmGuinandWeilPolarThirdGradeRateWindow b x := by
        calc
          |_ - _| ≤ |ccmGuinandWeilPrimeThirdGradeRateWindow b x| +
              |ccmGuinandWeilPolarThirdGradeRateWindow b x| := abs_sub _ _
          _ = _ := by rw [abs_of_nonneg hp0, abs_of_nonneg hr0]
      _ ≤ (32 / b ^ 2) * Real.exp x +
          (64 / b ^ 3) * x * Real.exp (x / 2) := add_le_add hp hr
      _ ≤ K := by
        dsimp only [K]
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hex (by positivity)
        · simpa only [mul_assoc] using
            (mul_le_mul_of_nonneg_left hxh
              (show 0 ≤ 64 / b ^ 3 by positivity))

theorem intervalIntegrable_thirdGradeCumulative_all
    {b : ℝ} (hb : 0 < b) (a H : ℝ) :
    IntervalIntegrable
      (ccmGuinandWeilThirdGradeCumulativeMeasurable b) volume a H := by
  let K : ℝ := (32 / b ^ 2) * Real.exp (max a H)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hprime : IntervalIntegrable
      (ccmGuinandWeilPrimeThirdGradeRateWindow b) volume a H := by
    apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => K) volume a H).mono_fun
    · exact (measurable_ccmGuinandWeilPrimeThirdGradeRateWindow b).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
      have hxu : x ∈ Set.uIcc a H := uIoc_subset_uIcc hx
      have hxmax : x ≤ max a H := by
        simpa only [Set.uIcc, Set.mem_Icc] using hxu |>.2
      have hp0 := ccmGuinandWeilPrimeThirdGradeRateWindow_nonneg
        (b := b) (H := x)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp0, abs_of_nonneg hK]
      exact (ccmGuinandWeilPrimeThirdGradeRateWindow_le hb x).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hxmax) (by positivity))
  have hclamped := continuous_ccmGuinandWeilThirdGradePolarDensityClamped hb
  have hpolar : Continuous (fun H : ℝ =>
      ∫ h in b..H, ccmGuinandWeilThirdGradePolarDensityClamped b h) :=
    intervalIntegral.continuous_primitive
      (fun x y => hclamped.intervalIntegrable x y) b
  change IntervalIntegrable (fun H : ℝ =>
    ccmGuinandWeilPrimeThirdGradeRateWindow b H -
      ∫ h in b..H, ccmGuinandWeilThirdGradePolarDensityClamped b h) volume a H
  exact hprime.sub (hpolar.intervalIntegrable a H)

theorem continuous_ccmCesaroPrimitive_thirdGradeCumulative
    {b : ℝ} (hb : 0 < b) :
    Continuous (ccmCesaroPrimitive
      (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b) := by
  unfold ccmCesaroPrimitive
  exact intervalIntegral.continuous_primitive
    (intervalIntegrable_thirdGradeCumulative_all hb) b

theorem analyticOnNhd_ccmSecondAbelLaplaceTail_of_linear
    {Q : ℝ → ℝ} (hQ : Measurable Q)
    {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (hQC : ∀ H, b < H → |Q H| ≤ C * (H + 1)) :
    AnalyticOnNhd ℂ
      (fun u : ℂ => ∫ H : ℝ in Set.Ioi b,
        Complex.exp (-u * (H : ℂ)) * (Q H : ℂ))
      {u : ℂ | 0 < u.re} := by
  intro u₀ hu₀
  change 0 < u₀.re at hu₀
  let σ : ℝ := u₀.re / 2
  let M : ℝ := max 1 σ⁻¹
  let r : ℝ → ℝ := fun H => Real.exp (-σ * H) * Q H
  have hσ : 0 < σ := by dsimp only [σ]; linarith
  have hM : 0 ≤ M := by
    exact le_trans zero_le_one (le_max_left 1 σ⁻¹)
  have hrMeas : Measurable r := by
    dsimp only [r]
    have hlin : Measurable (fun H : ℝ => -σ * H) :=
      measurable_const.mul measurable_id
    exact (Real.measurable_exp.comp hlin).mul hQ
  have hrBound : ∀ H, b < H → |r H| ≤ C * M := by
    intro H hH
    have hH0 : 0 ≤ H := (hb.trans hH).le
    have hσH0 : 0 ≤ σ * H := mul_nonneg hσ.le hH0
    have hHM : H + 1 ≤ M * (σ * H + 1) := by
      calc
        H + 1 = σ⁻¹ * (σ * H) + 1 := by
          field_simp
        _ ≤ M * (σ * H) + M := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right (le_max_right 1 σ⁻¹) hσH0)
            (le_max_left 1 σ⁻¹)
        _ = M * (σ * H + 1) := by ring
    have hHExp : H + 1 ≤ M * Real.exp (σ * H) :=
      hHM.trans (mul_le_mul_of_nonneg_left
        (Real.add_one_le_exp (σ * H)) hM)
    calc
      |r H| = Real.exp (-σ * H) * |Q H| := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-σ * H) * (C * (H + 1)) := by
        exact mul_le_mul_of_nonneg_left (hQC H hH) (Real.exp_nonneg _)
      _ ≤ Real.exp (-σ * H) * (C * (M * Real.exp (σ * H))) := by
        gcongr
      _ = C * M := by
        rw [show Real.exp (-σ * H) * (C * (M * Real.exp (σ * H))) =
          C * M * (Real.exp (-σ * H) * Real.exp (σ * H)) by ring,
          ← Real.exp_add]
        simp
  have hrAn := analyticOnNhd_ccmAbelLaplaceTail_of_bounded
    hrMeas hb (mul_nonneg hC hM) hrBound
  have hshift : 0 < (u₀ - (σ : ℂ)).re := by
    dsimp only [σ]
    simp only [sub_re, ofReal_re]
    linarith
  have hcomp : AnalyticAt ℂ
      (fun u : ℂ => ccmAbelLaplaceTail r b (u - (σ : ℂ))) u₀ := by
    have hinner : AnalyticAt ℂ (fun u : ℂ => u - (σ : ℂ)) u₀ :=
      analyticAt_id.sub analyticAt_const
    have hraw := AnalyticAt.comp
      (x := u₀) (f := fun u : ℂ => u - (σ : ℂ))
      (g := ccmAbelLaplaceTail r b)
      (hrAn (u₀ - (σ : ℂ)) hshift) hinner
    simpa only [Function.comp_def] using hraw
  have heq : (fun u : ℂ => ∫ H : ℝ in Set.Ioi b,
      Complex.exp (-u * (H : ℂ)) * (Q H : ℂ)) =
      (fun u : ℂ => ccmAbelLaplaceTail r b (u - (σ : ℂ))) := by
    funext u
    rw [ccmAbelLaplaceTail]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro H hH
    dsimp only [r]
    rw [ofReal_mul, ofReal_exp]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [heq]
  exact hcomp

def CCMGuinandWeilThirdGradeCesaroLinearBound (b : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, b < H →
    |ccmCesaroPrimitive
      (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H| ≤ C * (H + 1)

theorem integrableOn_exp_mul_ccmCesaroPrimitive_of_linear
    {b C : ℝ} (hb : 0 < b)
    (hbound : ∀ H : ℝ, b < H →
      |ccmCesaroPrimitive
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H| ≤ C * (H + 1))
    {u : ℂ} (hu : 0 < u.re) :
    IntegrableOn
      (fun H : ℝ => Complex.exp (-u * (H : ℂ)) *
        (ccmCesaroPrimitive
          (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H : ℂ))
      (Set.Ioi b) := by
  have hpow (m : ℕ) : IntegrableOn
      (fun H : ℝ => H ^ m * Real.exp (-(u.re * H))) (Set.Ioi b) := by
    have hg := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (m : ℝ)) (b := u.re)
      (by have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m; linarith)
      (by norm_num) hu
    apply (hg.mono_set (Set.Ioi_subset_Ioi hb.le)).congr_fun
    · intro H hH
      change H ^ (m : ℝ) * Real.exp (-u.re * H ^ (1 : ℝ)) =
        H ^ m * Real.exp (-(u.re * H))
      rw [Real.rpow_natCast H m, Real.rpow_one]
      congr 1
      ring_nf
    · exact measurableSet_Ioi
  have h0 := hpow 0
  have h1 := hpow 1
  have hmajor : IntegrableOn
      (fun H : ℝ => C * (H + 1) * Real.exp (-(u.re * H)))
      (Set.Ioi b) := by
    have hadd : IntegrableOn
        (fun H : ℝ => (H ^ 1 + H ^ 0) * Real.exp (-(u.re * H)))
        (Set.Ioi b) := by
      apply (h1.add h0).congr_fun _ measurableSet_Ioi
      intro H hH
      simp only [Pi.add_apply, pow_one, pow_zero]
      ring
    change Integrable
      (fun H : ℝ => C * (H + 1) * Real.exp (-(u.re * H)))
      (volume.restrict (Set.Ioi b))
    apply (hadd.const_mul C).congr
    filter_upwards with H
    simp only [pow_one, pow_zero]
    ring
  apply hmajor.mono'
  · apply Measurable.aestronglyMeasurable
    exact (by fun_prop : Measurable (fun H : ℝ => Complex.exp (-u * (H : ℂ))))
      |>.mul (Complex.continuous_ofReal.measurable.comp
        (continuous_ccmCesaroPrimitive_thirdGradeCumulative hb).measurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with H hH
    rw [norm_mul, Complex.norm_exp, norm_real, Real.norm_eq_abs]
    have hre : (-u * (H : ℂ)).re = -u.re * H := by simp [mul_re]
    rw [hre]
    have hmul := mul_le_mul_of_nonneg_left (hbound H hH)
      (Real.exp_nonneg (-u.re * H))
    simpa only [neg_mul, mul_neg, mul_assoc, mul_comm, mul_left_comm] using hmul

theorem analyticOnNhd_ccmSecondAbelCumulativeSourceContinuation_of_linear
    {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (hbound : ∀ H : ℝ, b < H →
      |ccmCesaroPrimitive
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H| ≤ C * (H + 1)) :
    AnalyticOnNhd ℂ
      (ccmSecondAbelCumulativeSourceContinuation
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b)
      {u : ℂ | 0 < u.re} := by
  have htail := analyticOnNhd_ccmSecondAbelLaplaceTail_of_linear
    (continuous_ccmCesaroPrimitive_thirdGradeCumulative hb).measurable
    hb hC hbound
  intro u hu
  change AnalyticAt ℂ (fun z : ℂ => z ^ 2 *
    (∫ H : ℝ in Set.Ioi b, Complex.exp (-z * (H : ℂ)) *
      (ccmCesaroPrimitive
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H : ℂ))) u
  exact (analyticAt_id.pow 2).mul (htail u hu)

theorem integrableOn_exp_mul_thirdGradeCumulative
    {b : ℝ} (hb : 0 < b) {u : ℂ} (hu : 1 < u.re) :
    IntegrableOn
      (fun H : ℝ => Complex.exp (-u * (H : ℂ)) *
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b H : ℂ))
      (Set.Ioi b) := by
  have hprime := integrableOn_exp_mul_ccmGuinandWeilPrimeThirdGradeRateWindow hb hu
  have hpolar0 := integrableOn_ccmGuinandWeilPolarThirdGradeRateWindow_mul_exp
    hb (by linarith : 1 / 2 < u.re)
  have hpolar : IntegrableOn
      (fun H : ℝ => Complex.exp (-u * (H : ℂ)) *
        (ccmGuinandWeilPolarThirdGradeRateWindow b H : ℂ))
      (Set.Ioi b) :=
    hpolar0.congr_fun (fun H _ => by ring) measurableSet_Ioi
  apply (hprime.sub hpolar).congr_fun _ measurableSet_Ioi
  intro H hH
  change Complex.exp (-u * (H : ℂ)) *
      (ccmGuinandWeilPrimeThirdGradeRateWindow b H : ℂ) -
        Complex.exp (-u * (H : ℂ)) *
          (ccmGuinandWeilPolarThirdGradeRateWindow b H : ℂ) =
    Complex.exp (-u * (H : ℂ)) *
      (ccmGuinandWeilThirdGradeCumulativeMeasurable b H : ℂ)
  rw [ccmGuinandWeilThirdGradeCumulativeMeasurable_eq_primePolar hH.le,
    ccmGuinandWeilPrimePolarWeightedWindow_thirdGrade_eq_prime_sub_polar]
  push_cast
  ring

theorem intervalIntegral_exp_mul_thirdGradeCumulative_eq_boundary_add
    {b T r : ℝ} (hb : 0 < b) (hbT : b ≤ T) :
    (∫ H in b..T, Real.exp (-r * H) *
      ccmGuinandWeilThirdGradeCumulativeMeasurable b H) =
      Real.exp (-r * T) *
          ccmCesaroPrimitive
            (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b T +
        r * (∫ H in b..T, Real.exp (-r * H) *
          ccmCesaroPrimitive
            (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H) := by
  let q := ccmGuinandWeilThirdGradeCumulativeMeasurable b
  let Q := ccmCesaroPrimitive q b
  let E : ℝ → ℝ := fun H => Real.exp (-r * H)
  have hqInt : IntervalIntegrable q volume b T :=
    intervalIntegrable_thirdGradeCumulative hb hbT
  have hQac : AbsolutelyContinuousOnInterval Q b T := by
    exact hqInt.absolutelyContinuousOnInterval_intervalIntegral
      (show b ∈ Set.uIcc b T by simp [hbT])
  have hEcd : ContDiff ℝ 1 E := by
    dsimp only [E]
    fun_prop
  have hEac : AbsolutelyContinuousOnInterval E b T :=
    hEcd.contDiffOn.absolutelyContinuousOnInterval
  have hibp := hEac.integral_mul_deriv_eq_deriv_mul hQac
  have hleft : (∫ H in b..T, E H * deriv Q H) =
      ∫ H in b..T, E H * q H := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hqInt.ae_hasDerivAt_integral] with H hH hmem
    have hderiv : HasDerivAt Q (q H) H := by
      exact hH (uIoc_subset_uIcc hmem) b (by simp [hbT])
    rw [hderiv.deriv]
  have hright : (∫ H in b..T, deriv E H * Q H) =
      ∫ H in b..T, (-r * E H) * Q H := by
    apply intervalIntegral.integral_congr
    intro H hH
    have hderiv : HasDerivAt E (-r * E H) H := by
      simpa only [E, id_eq, mul_one, mul_comm] using
        ((hasDerivAt_id H).const_mul (-r)).exp
    change deriv E H * Q H = (-r * E H) * Q H
    rw [hderiv.deriv]
  have hQb : Q b = 0 := by simp [Q, ccmCesaroPrimitive]
  rw [hleft, hright, hQb, mul_zero, sub_zero] at hibp
  dsimp only [E, Q, q] at hibp ⊢
  have hnegInt :
      -(∫ H in b..T, (-r * Real.exp (-r * H)) *
        ccmCesaroPrimitive
          (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H) =
      ∫ H in b..T, r * (Real.exp (-r * H) *
        ccmCesaroPrimitive
          (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro H hH
    ring
  rw [hibp, sub_eq_add_neg, hnegInt, intervalIntegral.integral_const_mul]

theorem integrableOn_real_exp_mul_thirdGradeCumulative
    {b r : ℝ} (hb : 0 < b) (hr : 1 < r) :
    IntegrableOn
      (fun H : ℝ => Real.exp (-r * H) *
        ccmGuinandWeilThirdGradeCumulativeMeasurable b H)
      (Set.Ioi b) := by
  have hc := integrableOn_exp_mul_thirdGradeCumulative hb
    (u := (r : ℂ)) (by simpa using hr)
  have hc' : IntegrableOn
      (fun H : ℝ => ((Real.exp (-r * H) *
        ccmGuinandWeilThirdGradeCumulativeMeasurable b H : ℝ) : ℂ))
      (Set.Ioi b) := by
    apply hc.congr_fun _ measurableSet_Ioi
    intro H hH
    have hexp : Complex.exp (-(r : ℂ) * (H : ℂ)) =
        (Real.exp (-r * H) : ℂ) := by
      calc
        Complex.exp (-(r : ℂ) * (H : ℂ)) =
            Complex.exp ((-r * H : ℝ) : ℂ) := by
          congr 1
          push_cast
          ring
        _ = (Real.exp (-r * H) : ℂ) := (ofReal_exp _).symm
    change Complex.exp (-(r : ℂ) * (H : ℂ)) *
      (ccmGuinandWeilThirdGradeCumulativeMeasurable b H : ℂ) =
        ((Real.exp (-r * H) *
          ccmGuinandWeilThirdGradeCumulativeMeasurable b H : ℝ) : ℂ)
    rw [hexp, ofReal_mul]
  have hre := Integrable.re
    (f := fun H : ℝ => ((Real.exp (-r * H) *
      ccmGuinandWeilThirdGradeCumulativeMeasurable b H : ℝ) : ℂ)) hc'
  apply hre.congr
  filter_upwards with H
  exact Complex.ofReal_re _

theorem integrableOn_real_exp_mul_ccmCesaroPrimitive_of_linear
    {b C r : ℝ} (hb : 0 < b)
    (hbound : ∀ H : ℝ, b < H →
      |ccmCesaroPrimitive
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H| ≤ C * (H + 1))
    (hr : 0 < r) :
    IntegrableOn
      (fun H : ℝ => Real.exp (-r * H) *
        ccmCesaroPrimitive
          (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H)
      (Set.Ioi b) := by
  have hc := integrableOn_exp_mul_ccmCesaroPrimitive_of_linear hb hbound
    (u := (r : ℂ)) (by simpa using hr)
  have hc' : IntegrableOn
      (fun H : ℝ => ((Real.exp (-r * H) *
        ccmCesaroPrimitive
          (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H : ℝ) : ℂ))
      (Set.Ioi b) := by
    apply hc.congr_fun _ measurableSet_Ioi
    intro H hH
    have hexp : Complex.exp (-(r : ℂ) * (H : ℂ)) =
        (Real.exp (-r * H) : ℂ) := by
      calc
        Complex.exp (-(r : ℂ) * (H : ℂ)) =
            Complex.exp ((-r * H : ℝ) : ℂ) := by
          congr 1
          push_cast
          ring
        _ = (Real.exp (-r * H) : ℂ) := (ofReal_exp _).symm
    change Complex.exp (-(r : ℂ) * (H : ℂ)) *
      (ccmCesaroPrimitive
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H : ℂ) =
        ((Real.exp (-r * H) *
          ccmCesaroPrimitive
            (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H : ℝ) : ℂ)
    rw [hexp, ofReal_mul]
  have hre := Integrable.re
    (f := fun H : ℝ => ((Real.exp (-r * H) *
      ccmCesaroPrimitive
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H : ℝ) : ℂ)) hc'
  apply hre.congr
  filter_upwards with H
  exact Complex.ofReal_re _

theorem integral_Ioi_exp_mul_thirdGradeCumulative_eq_cesaro
    {b C r : ℝ} (hb : 0 < b)
    (hbound : ∀ H : ℝ, b < H →
      |ccmCesaroPrimitive
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H| ≤ C * (H + 1))
    (hr : 1 < r) :
    (∫ H : ℝ in Set.Ioi b, Real.exp (-r * H) *
      ccmGuinandWeilThirdGradeCumulativeMeasurable b H) =
      r * ∫ H : ℝ in Set.Ioi b, Real.exp (-r * H) *
        ccmCesaroPrimitive
          (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hqInt := integrableOn_real_exp_mul_thirdGradeCumulative hb hr
  have hQInt := integrableOn_real_exp_mul_ccmCesaroPrimitive_of_linear
    hb hbound hr0
  have hlin : Tendsto (fun T : ℝ => T * Real.exp (-r * T))
      atTop (nhds 0) := by
    simpa only [Real.rpow_one] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 r hr0
  have hexp : Tendsto (fun T : ℝ => Real.exp (-r * T))
      atTop (nhds 0) := by
    have harg : Tendsto (fun T : ℝ => -r * T) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hr0)
    exact Real.tendsto_exp_atBot.comp harg
  have hdecay : Tendsto
      (fun T : ℝ => (T + 1) * Real.exp (-r * T))
      atTop (nhds 0) := by
    have hsum := hlin.add hexp
    convert hsum using 1
    · funext T
      ring
    · simp
  have hboundary : Tendsto
      (fun T : ℝ => Real.exp (-r * T) *
        ccmCesaroPrimitive
          (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b T)
      atTop (nhds 0) := by
    have hpoint : ∀ᶠ T : ℝ in atTop,
        |Real.exp (-r * T) *
          ccmCesaroPrimitive
            (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b T| ≤
          C * ((T + 1) * Real.exp (-r * T)) := by
      filter_upwards [eventually_gt_atTop b] with T hT
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      have hmul := mul_le_mul_of_nonneg_left (hbound T hT)
        (Real.exp_nonneg (-r * T))
      calc
        Real.exp (-r * T) *
            |ccmCesaroPrimitive
              (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b T| ≤
            Real.exp (-r * T) * (C * (T + 1)) := hmul
        _ = C * ((T + 1) * Real.exp (-r * T)) := by ring
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hmajor : Tendsto
        (fun T : ℝ => C * ((T + 1) * Real.exp (-r * T)))
        atTop (nhds 0) := by
      simpa using hdecay.const_mul C
    simpa only [Real.norm_eq_abs] using
      squeeze_zero' (Eventually.of_forall fun T => abs_nonneg _)
        hpoint hmajor
  have hqLim := intervalIntegral_tendsto_integral_Ioi b hqInt tendsto_id
  have hQLim := intervalIntegral_tendsto_integral_Ioi b hQInt tendsto_id
  have hrightLim := hboundary.add (hQLim.const_mul r)
  have hrightLim' : Tendsto
      (fun T : ℝ => Real.exp (-r * T) *
          ccmCesaroPrimitive
            (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b T +
        r * (∫ H in b..T, Real.exp (-r * H) *
          ccmCesaroPrimitive
            (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H))
      atTop
      (nhds (r * ∫ H : ℝ in Set.Ioi b, Real.exp (-r * H) *
        ccmCesaroPrimitive
          (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H)) := by
    simpa only [id_eq, zero_add] using hrightLim
  have heq : ∀ᶠ T : ℝ in atTop,
      (∫ H in b..T, Real.exp (-r * H) *
        ccmGuinandWeilThirdGradeCumulativeMeasurable b H) =
        Real.exp (-r * T) *
            ccmCesaroPrimitive
              (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b T +
          r * (∫ H in b..T, Real.exp (-r * H) *
            ccmCesaroPrimitive
              (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H) := by
    filter_upwards [eventually_ge_atTop b] with T hT
    exact intervalIntegral_exp_mul_thirdGradeCumulative_eq_boundary_add hb hT
  exact tendsto_nhds_unique hqLim
    (hrightLim'.congr' (heq.mono fun _ h => h.symm))

theorem ccmSecondAbelCumulativeSourceContinuation_eq_first_on_real
    {b C r : ℝ} (hb : 0 < b)
    (hbound : ∀ H : ℝ, b < H →
      |ccmCesaroPrimitive
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H| ≤ C * (H + 1))
    (hr : 1 < r) :
    ccmSecondAbelCumulativeSourceContinuation
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b (r : ℂ) =
      ccmAbelCumulativeSourceContinuation
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b (r : ℂ) := by
  have hreal := integral_Ioi_exp_mul_thirdGradeCumulative_eq_cesaro
    hb hbound hr
  have hq :
      (∫ H : ℝ in Set.Ioi b, Complex.exp (-(r : ℂ) * (H : ℂ)) *
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b H : ℂ)) =
      ((∫ H : ℝ in Set.Ioi b, Real.exp (-r * H) *
        ccmGuinandWeilThirdGradeCumulativeMeasurable b H : ℝ) : ℂ) := by
    calc
      _ = ∫ H : ℝ in Set.Ioi b,
          ((Real.exp (-r * H) *
            ccmGuinandWeilThirdGradeCumulativeMeasurable b H : ℝ) : ℂ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro H hH
        have hexp : Complex.exp (-(r : ℂ) * (H : ℂ)) =
            (Real.exp (-r * H) : ℂ) := by
          calc
            Complex.exp (-(r : ℂ) * (H : ℂ)) =
                Complex.exp ((-r * H : ℝ) : ℂ) := by
              congr 1
              push_cast
              ring
            _ = (Real.exp (-r * H) : ℂ) := (ofReal_exp _).symm
        change Complex.exp (-(r : ℂ) * (H : ℂ)) *
          (ccmGuinandWeilThirdGradeCumulativeMeasurable b H : ℂ) =
            ((Real.exp (-r * H) *
              ccmGuinandWeilThirdGradeCumulativeMeasurable b H : ℝ) : ℂ)
        rw [hexp, ofReal_mul]
      _ = _ := integral_complex_ofReal
  have hQ :
      (∫ H : ℝ in Set.Ioi b, Complex.exp (-(r : ℂ) * (H : ℂ)) *
        (ccmCesaroPrimitive
          (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H : ℂ)) =
      ((∫ H : ℝ in Set.Ioi b, Real.exp (-r * H) *
        ccmCesaroPrimitive
          (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H : ℝ) : ℂ) := by
    calc
      _ = ∫ H : ℝ in Set.Ioi b,
          ((Real.exp (-r * H) *
            ccmCesaroPrimitive
              (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H : ℝ) : ℂ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro H hH
        have hexp : Complex.exp (-(r : ℂ) * (H : ℂ)) =
            (Real.exp (-r * H) : ℂ) := by
          calc
            Complex.exp (-(r : ℂ) * (H : ℂ)) =
                Complex.exp ((-r * H : ℝ) : ℂ) := by
              congr 1
              push_cast
              ring
            _ = (Real.exp (-r * H) : ℂ) := (ofReal_exp _).symm
        change Complex.exp (-(r : ℂ) * (H : ℂ)) *
          (ccmCesaroPrimitive
            (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H : ℂ) =
            ((Real.exp (-r * H) *
              ccmCesaroPrimitive
                (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H : ℝ) : ℂ)
        rw [hexp, ofReal_mul]
      _ = _ := integral_complex_ofReal
  rw [ccmSecondAbelCumulativeSourceContinuation,
    ccmSecondAbelLaplaceTail, ccmAbelCumulativeSourceContinuation,
    ccmAbelLaplaceTail, hq, hQ]
  rw [hreal]
  rw [ofReal_mul]
  ring

theorem analyticOnNhd_eqOn_re_gt_one_of_eq_ofReal
    {F G : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 1 < z.re})
    (hG : AnalyticOnNhd ℂ G {z : ℂ | 1 < z.re})
    (hreal : ∀ r : ℝ, 1 < r → F (r : ℂ) = G (r : ℂ)) :
    ∀ u : ℂ, 1 < u.re → F u = G u := by
  have htwo : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
  have htend : Tendsto (fun r : ℝ => (r : ℂ))
      (𝓝[>] (2 : ℝ)) (𝓝[≠] (2 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun r : ℝ => (r : ℂ))
          (𝓝 (2 : ℝ)) (𝓝 (2 : ℂ)) := by
        simpa using Complex.continuous_ofReal.tendsto (2 : ℝ)
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [mem_compl_iff, mem_singleton_iff]
      intro hcon
      have : r = 2 := by exact_mod_cast hcon
      exact absurd this (ne_of_gt hr)
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), F z = G z := by
    refine htend.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hreal r (lt_trans (by norm_num) hr)
  have heq := hF.eqOn_of_preconnected_of_frequently_eq hG
    (convex_halfSpace_re_gt 1).isPreconnected htwo hfreq
  intro u hu
  exact heq hu

theorem ccmSecondAbelCumulativeSourceContinuation_eq_atomic_sub_polar
    {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (hbound : ∀ H : ℝ, b < H →
      |ccmCesaroPrimitive
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H| ≤ C * (H + 1))
    {u : ℂ} (hu : 1 < u.re) :
    ccmSecondAbelCumulativeSourceContinuation
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b u =
      LSeries (ccmGuinandWeilThirdGradePrimeDirichletCoeff b) u -
        ccmGuinandWeilThirdGradePolarLaplaceMoment b 0 u := by
  let F := ccmSecondAbelCumulativeSourceContinuation
    (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b
  let G : ℂ → ℂ := fun z =>
    LSeries (ccmGuinandWeilThirdGradePrimeDirichletCoeff b) z -
      ccmGuinandWeilThirdGradePolarLaplaceMoment b 0 z
  have hF : AnalyticOnNhd ℂ F {z : ℂ | 1 < z.re} :=
    (analyticOnNhd_ccmSecondAbelCumulativeSourceContinuation_of_linear
      hb hC hbound).mono (by
        intro z hz
        change 1 < z.re at hz
        change 0 < z.re
        linarith)
  have hG : AnalyticOnNhd ℂ G {z : ℂ | 1 < z.re} := by
    intro z hz
    change 1 < z.re at hz
    have habs : LSeries.abscissaOfAbsConv
        (ccmGuinandWeilThirdGradePrimeDirichletCoeff b) < z.re :=
      (abscissaOfAbsConv_ccmGuinandWeilThirdGradePrimeDirichletCoeff_le_one hb).trans_lt
        (by exact_mod_cast hz)
    exact (LSeries_analyticOnNhd
      (ccmGuinandWeilThirdGradePrimeDirichletCoeff b) z habs).sub
        (analyticOnNhd_ccmGuinandWeilThirdGradePolarLaplaceMoment hb 0 z
          (by
            change (1 / 2 : ℝ) < z.re
            linarith))
  apply analyticOnNhd_eqOn_re_gt_one_of_eq_ofReal hF hG _ u hu
  intro r hr1
  dsimp only [F, G]
  rw [ccmSecondAbelCumulativeSourceContinuation_eq_first_on_real
    hb hbound hr1]
  rw [ccmAbelCumulativeSourceContinuation_eq_atomic_sub_polar
    (u := (r : ℂ)) hb (by simpa using hr1)]
  rw [ccmGuinandWeilThirdGradePolarLaplaceMoment]
  simp

theorem ccmSecondAbelCumulativeSourceContinuation_eq_first
    {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (hbound : ∀ H : ℝ, b < H →
      |ccmCesaroPrimitive
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H| ≤ C * (H + 1))
    {u : ℂ} (hu : 1 < u.re) :
    ccmSecondAbelCumulativeSourceContinuation
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b u =
      ccmAbelCumulativeSourceContinuation
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b u := by
  rw [ccmSecondAbelCumulativeSourceContinuation_eq_atomic_sub_polar
    hb hC hbound hu,
    ccmAbelCumulativeSourceContinuation_eq_atomic_sub_polar hb hu,
    ccmGuinandWeilThirdGradePolarLaplaceMoment]
  simp

theorem iteratedDeriv_three_ccmSecondAbelCumulativeSourceContinuation_eq_tailDefect
    {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (hbound : ∀ H : ℝ, b < H →
      |ccmCesaroPrimitive
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H| ≤ C * (H + 1))
    {u : ℂ} (hu : 1 < u.re) :
    iteratedDeriv 3
        (ccmSecondAbelCumulativeSourceContinuation
          (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b) u =
      32 * ccmGuinandWeilThirdGradeTailMellinDefect b u := by
  have hopen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have heq : ccmSecondAbelCumulativeSourceContinuation
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b =ᶠ[𝓝 u]
      ccmAbelCumulativeSourceContinuation
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b := by
    filter_upwards [hopen.mem_nhds hu] with z hz
    exact ccmSecondAbelCumulativeSourceContinuation_eq_first
      hb hC hbound hz
  rw [heq.iteratedDeriv_eq 3]
  exact iteratedDeriv_three_ccmAbelCumulativeSourceContinuation_eq_tailDefect hb hu

def ccmGuinandWeilThirdGradeCesaroCriticalMellinExtension
    (b : ℝ) (s : ℂ) : ℂ :=
  (1 / 32 : ℂ) * iteratedDeriv 3
      (ccmSecondAbelCumulativeSourceContinuation
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b) (s + 1 / 2) +
    ccmGuinandWeilThirdGradeWallHead b s

theorem analyticOnNhd_ccmGuinandWeilThirdGradeCesaroCriticalMellinExtension_of_linear
    {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (hbound : ∀ H : ℝ, b < H →
      |ccmCesaroPrimitive
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H| ≤ C * (H + 1)) :
    AnalyticOnNhd ℂ
      (ccmGuinandWeilThirdGradeCesaroCriticalMellinExtension b)
      ccmGuinandWeilCriticalMellinContinuationHalfPlane := by
  have hG := analyticOnNhd_ccmSecondAbelCumulativeSourceContinuation_of_linear
    hb hC hbound
  have hG3 : AnalyticOnNhd ℂ
      (iteratedDeriv 3
        (ccmSecondAbelCumulativeSourceContinuation
          (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b))
      {u : ℂ | 0 < u.re} := by
    simpa only [iteratedDeriv_eq_iterate] using hG.iterated_deriv 3
  intro s hs
  have hu : 0 < (s + 1 / 2).re := by
    change -1 / 2 < s.re at hs
    norm_num [div_re]
    linarith
  have hshift : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) s := by fun_prop
  have hGcomp := AnalyticAt.comp (f := fun z : ℂ => z + 1 / 2)
    (hG3 (s + 1 / 2) hu) hshift
  have hwall := analyticOnNhd_ccmGuinandWeilThirdGradeWallHead hb
    s (Set.mem_univ _)
  change AnalyticAt ℂ
    (fun z => (1 / 32 : ℂ) * iteratedDeriv 3
        (ccmSecondAbelCumulativeSourceContinuation
          (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b) (z + 1 / 2) +
      ccmGuinandWeilThirdGradeWallHead b z) s
  exact analyticAt_const.mul hGcomp |>.add hwall

theorem ccmGuinandWeilThirdGradeCesaroCriticalMellinExtension_eq_regularized_safe
    {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (hbound : ∀ H : ℝ, b < H →
      |ccmCesaroPrimitive
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H| ≤ C * (H + 1))
    {s : ℂ} (hs : 3 / 2 < s.re) :
    ccmGuinandWeilThirdGradeCesaroCriticalMellinExtension b s =
      regularizedCriticalMellinDefect s := by
  have hu : 1 < (s + 1 / 2).re := by
    norm_num [div_re]
    linarith
  rw [ccmGuinandWeilThirdGradeCesaroCriticalMellinExtension,
    iteratedDeriv_three_ccmSecondAbelCumulativeSourceContinuation_eq_tailDefect
      hb hC hbound hu]
  calc
    (1 / 32 : ℂ) *
          (32 * ccmGuinandWeilThirdGradeTailMellinDefect b (s + 1 / 2)) +
        ccmGuinandWeilThirdGradeWallHead b s =
        ccmGuinandWeilThirdGradeAbelCriticalMellinExtension b s := by
      rw [ccmGuinandWeilThirdGradeAbelCriticalMellinExtension,
        iteratedDeriv_three_ccmAbelCumulativeSourceContinuation_eq_tailDefect hb hu]
    _ = regularizedCriticalMellinDefect s :=
      ccmGuinandWeilThirdGradeAbelCriticalMellinExtension_eq_regularized_safe hb hs

theorem ccmGuinandWeilThirdGradeCesaroCriticalMellinExtension_eq_regularized_of_linear
    {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (hbound : ∀ H : ℝ, b < H →
      |ccmCesaroPrimitive
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H| ≤ C * (H + 1)) :
    ∀ s : ℂ, 0 < s.re →
      ccmGuinandWeilThirdGradeCesaroCriticalMellinExtension b s =
        regularizedCriticalMellinDefect s := by
  let U : Set ℂ := {s : ℂ | 0 < s.re}
  have hUpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hsubset : U ⊆ ccmGuinandWeilCriticalMellinContinuationHalfPlane := by
    intro s hs
    change -1 / 2 < s.re
    change 0 < s.re at hs
    linarith
  have hA : AnalyticOnNhd ℂ
      (ccmGuinandWeilThirdGradeCesaroCriticalMellinExtension b) U :=
    (analyticOnNhd_ccmGuinandWeilThirdGradeCesaroCriticalMellinExtension_of_linear
      hb hC hbound).mono hsubset
  have hR : AnalyticOnNhd ℂ regularizedCriticalMellinDefect U := by
    simpa only [U] using analyticOnNhd_regularizedCriticalMellinDefect_rightHalfPlane
  let z₀ : ℂ := 2
  have hz₀ : z₀ ∈ U := by change 0 < (2 : ℂ).re; norm_num
  have hsafeOpen : IsOpen {s : ℂ | 3 / 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hz₀safe : z₀ ∈ {s : ℂ | 3 / 2 < s.re} := by
    change 3 / 2 < (2 : ℂ).re
    norm_num
  have hevent :
      ccmGuinandWeilThirdGradeCesaroCriticalMellinExtension b =ᶠ[nhds z₀]
        regularizedCriticalMellinDefect := by
    filter_upwards [hsafeOpen.mem_nhds hz₀safe] with s hs
    exact ccmGuinandWeilThirdGradeCesaroCriticalMellinExtension_eq_regularized_safe
      hb hC hbound hs
  have heq := hA.eqOn_of_preconnected_of_eventuallyEq hR hUpre hz₀ hevent
  intro s hs
  exact heq (show s ∈ U from hs)

theorem riemannHypothesis_of_ccmGuinandWeilThirdGradeCesaroLinearBound
    {b : ℝ} (hb : 0 < b)
    (hlinear : CCMGuinandWeilThirdGradeCesaroLinearBound b) :
    RiemannHypothesis := by
  rcases hlinear with ⟨C, hC, hbound⟩
  exact riemannHypothesis_of_regularizedCriticalMellinDefect_extension
    (ccmGuinandWeilThirdGradeCesaroCriticalMellinExtension b)
    (analyticOnNhd_ccmGuinandWeilThirdGradeCesaroCriticalMellinExtension_of_linear
      hb hC hbound)
    (ccmGuinandWeilThirdGradeCesaroCriticalMellinExtension_eq_regularized_of_linear
      hb hC hbound)

theorem ccmGuinandWeilThirdGradeCesaroPrimitive_superlinear_of_not_riemannHypothesis
    (hRH : ¬RiemannHypothesis) {b : ℝ} (hb : 0 < b) :
    ∀ C : ℝ, 0 ≤ C → ∃ H : ℝ, b < H ∧
      C * (H + 1) <
        |ccmCesaroPrimitive
          (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H| := by
  intro C hC
  by_contra hnot
  have hbound : ∀ H : ℝ, b < H →
      |ccmCesaroPrimitive
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H| ≤ C * (H + 1) := by
    intro H hH
    exact le_of_not_gt fun hgt => hnot ⟨H, hH, hgt⟩
  exact hRH (riemannHypothesis_of_ccmGuinandWeilThirdGradeCesaroLinearBound
    hb ⟨C, hC, hbound⟩)

end

end RHTower
