import GaloisForLFunctions.RHTower.PrimeArchThetaFirstMoment
import GaloisForLFunctions.RHTower.SignedReflectionParity
import Mathlib.MeasureTheory.Function.L2Space

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped SchwartzMap

noncomputable section

namespace RHTower

def thetaCuspCosineDerivativeIntegrand (n : ℕ) (t x : ℝ) : ℝ :=
  2 * x ^ n * thetaCuspFullSource x *
    Real.cos (t * x + (n : ℝ) * Real.pi / 2)

def thetaCuspCosineDerivativeIntegral (n : ℕ) (t : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0, thetaCuspCosineDerivativeIntegrand n t x

theorem integrableOn_thetaCuspCosineDerivativeIntegrand (n : ℕ) (t : ℝ) :
    IntegrableOn (thetaCuspCosineDerivativeIntegrand n t) (Ioi 0) := by
  have hmajor : Integrable
      (fun x : ℝ => 2 * (‖x‖ ^ n * ‖thetaCuspSchwartzReal x‖))
      (volume.restrict (Ioi 0)) :=
    ((thetaCuspSchwartzReal.integrable_pow_mul
      (volume : Measure ℝ) n).const_mul 2).restrict
  apply hmajor.mono
  · exact ((((continuous_const.mul (continuous_id.pow n)).mul
      contDiff_thetaCuspFullSource.continuous).mul
        (Real.continuous_cos.comp
          ((continuous_const.mul continuous_id).add continuous_const)
        )).aestronglyMeasurable)
  · filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity :
        0 ≤ 2 * (‖x‖ ^ n * ‖thetaCuspSchwartzReal x‖))]
    rw [thetaCuspCosineDerivativeIntegrand]
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      2 * |x ^ n| * |thetaCuspFullSource x| *
          |Real.cos (t * x + (n : ℝ) * Real.pi / 2)| ≤
          2 * |x ^ n| * |thetaCuspFullSource x| := by
        exact mul_le_of_le_one_right (by positivity) (abs_cos_le_one _)
      _ = 2 * (‖x‖ ^ n * ‖thetaCuspSchwartzReal x‖) := by
        simp [Real.norm_eq_abs, abs_pow]
        ring

theorem hasDerivAt_thetaCuspCosineDerivativeIntegrand (n : ℕ) (t x : ℝ) :
    HasDerivAt (fun s => thetaCuspCosineDerivativeIntegrand n s x)
      (thetaCuspCosineDerivativeIntegrand (n + 1) t x) t := by
  change HasDerivAt
    (fun s => 2 * x ^ n * thetaCuspFullSource x *
      Real.cos (s * x + (n : ℝ) * Real.pi / 2))
    (2 * x ^ (n + 1) * thetaCuspFullSource x *
      Real.cos (t * x + ((n + 1 : ℕ) : ℝ) * Real.pi / 2)) t
  have hcos := (Real.hasDerivAt_cos
    (t * x + (n : ℝ) * Real.pi / 2)).comp t
      (((hasDerivAt_id t).mul_const x).add_const ((n : ℝ) * Real.pi / 2))
  have h := hcos.const_mul (2 * x ^ n * thetaCuspFullSource x)
  have hderiv :
      2 * x ^ (n + 1) * thetaCuspFullSource x *
          Real.cos (t * x + ((n + 1 : ℕ) : ℝ) * Real.pi / 2) =
        2 * x ^ n * thetaCuspFullSource x *
          (-Real.sin (t * x + (n : ℝ) * Real.pi / 2) * (1 * x)) := by
    rw [show t * x + ((n + 1 : ℕ) : ℝ) * Real.pi / 2 =
        (t * x + (n : ℝ) * Real.pi / 2) + Real.pi / 2 by
      push_cast
      ring,
      Real.cos_add_pi_div_two, pow_succ]
    ring
  simpa only [Function.comp_apply, id_eq] using! h.congr_deriv hderiv.symm

theorem hasDerivAt_thetaCuspCosineDerivativeIntegral (n : ℕ) (t : ℝ) :
    HasDerivAt (thetaCuspCosineDerivativeIntegral n)
      (thetaCuspCosineDerivativeIntegral (n + 1) t) t := by
  let F : ℝ → ℝ → ℝ := fun s x => thetaCuspCosineDerivativeIntegrand n s x
  let F' : ℝ → ℝ → ℝ := fun s x => thetaCuspCosineDerivativeIntegrand (n + 1) s x
  let bound : ℝ → ℝ := fun x =>
    2 * (‖x‖ ^ (n + 1) * ‖thetaCuspSchwartzReal x‖)
  have hFint : Integrable (F t) (volume.restrict (Ioi 0)) :=
    integrableOn_thetaCuspCosineDerivativeIntegrand n t
  have hbound : Integrable bound (volume.restrict (Ioi 0)) := by
    exact ((thetaCuspSchwartzReal.integrable_pow_mul
      (volume : Measure ℝ) (n + 1)).const_mul 2).restrict
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0))
    (F := F) (F' := F') (x₀ := t) (s := Set.univ) (bound := bound)
    univ_mem
    (Filter.Eventually.of_forall fun s =>
      (by
        dsimp [F, thetaCuspCosineDerivativeIntegrand]
        exact ((((continuous_const.mul (continuous_id.pow n)).mul
          contDiff_thetaCuspFullSource.continuous).mul
            (Real.continuous_cos.comp
              ((continuous_const.mul continuous_id).add continuous_const)
            )).aestronglyMeasurable)))
    hFint
    (by
      dsimp [F', thetaCuspCosineDerivativeIntegrand]
      exact ((((continuous_const.mul (continuous_id.pow (n + 1))).mul
        contDiff_thetaCuspFullSource.continuous).mul
          (Real.continuous_cos.comp
            ((continuous_const.mul continuous_id).add continuous_const)
          )).aestronglyMeasurable))
    (by
      filter_upwards with x
      intro s hs
      dsimp [F', bound, thetaCuspCosineDerivativeIntegrand]
      rw [abs_mul, abs_mul, abs_mul]
      norm_num
      calc
        2 * |x| ^ (n + 1) * |thetaCuspFullSource x| *
            |Real.cos (s * x + ((n : ℝ) + 1) * Real.pi / 2)| ≤
            2 * |x| ^ (n + 1) * |thetaCuspFullSource x| := by
          exact mul_le_of_le_one_right (by positivity) (abs_cos_le_one _)
        _ = 2 * (‖x‖ ^ (n + 1) * ‖thetaCuspSchwartzReal x‖) := by
          simp [Real.norm_eq_abs]
          ring)
    hbound
    (by
      filter_upwards with x
      intro s hs
      exact hasDerivAt_thetaCuspCosineDerivativeIntegrand n s x)
  simpa only [thetaCuspCosineDerivativeIntegral, F, F'] using! hresult.2

theorem thetaCuspCosineDerivativeIntegral_zero (t : ℝ) :
    thetaCuspCosineDerivativeIntegral 0 t = thetaCuspCosineRepresentation t := by
  rw [thetaCuspCosineDerivativeIntegral, thetaCuspCosineRepresentation,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp [thetaCuspCosineDerivativeIntegrand]
  ring

theorem iteratedDeriv_thetaCuspCosineRepresentation_eq_integral (n : ℕ) (t : ℝ) :
    iteratedDeriv n thetaCuspCosineRepresentation t =
      thetaCuspCosineDerivativeIntegral n t := by
  induction n generalizing t with
  | zero =>
      simpa [iteratedDeriv_zero] using
        (thetaCuspCosineDerivativeIntegral_zero t).symm
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv n thetaCuspCosineRepresentation =
          thetaCuspCosineDerivativeIntegral n := by
        funext s
        exact ih s
      rw [hfun]
      exact (hasDerivAt_thetaCuspCosineDerivativeIntegral n t).deriv

def thetaCuspRawEvenMoment (n : ℕ) : ℝ :=
  2 * ∫ x : ℝ in Ioi 0, x ^ (2 * n) * thetaCuspFullSource x

theorem iteratedDeriv_Xi_zero_eq_rawEvenMoment (n : ℕ) :
    iteratedDeriv (2 * n) Xi 0 = (-1 : ℝ) ^ n * thetaCuspRawEvenMoment n := by
  rw [show Xi = thetaCuspCosineRepresentation by
    funext t
    exact Xi_eq_thetaCuspCosineRepresentation t,
    iteratedDeriv_thetaCuspCosineRepresentation_eq_integral]
  rw [thetaCuspCosineDerivativeIntegral, thetaCuspRawEvenMoment]
  rw [← mul_assoc, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [thetaCuspCosineDerivativeIntegrand]
  simp only [zero_mul, zero_add]
  rw [show ((2 * n : ℕ) : ℝ) * Real.pi / 2 = (n : ℝ) * Real.pi by
    push_cast
    ring,
    Real.cos_nat_mul_pi]
  ring

theorem iteratedDeriv_XiC_ofReal (n : ℕ) (x : ℝ) :
    iteratedDeriv n XiC (x : ℂ) = ((iteratedDeriv n Xi x : ℝ) : ℂ) := by
  induction n generalizing x with
  | zero => simpa [iteratedDeriv_zero] using XiC_ofReal x
  | succ n ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      apply complex_deriv_eq_of_real_restriction
        (iteratedDeriv n XiC) (iteratedDeriv n Xi)
      · intro z
        simpa only [iteratedDeriv_eq_iterate] using
          (iteratedDeriv_analyticOnNhd_univ XiC_analytic n z
            (Set.mem_univ z)).differentiableAt
      · exact ih

theorem oddTracePreimage_normalizedTraceMomentGerm_eq
    (T : ℂ → ℂ) (hT0 : T 0 = 0) :
    oddTracePreimage (normalizedTraceMomentGerm T) = T := by
  funext z
  by_cases hz : z = 0
  · subst z
    simp [oddTracePreimage, hT0]
  · rw [oddTracePreimage, normalizedTraceMomentGerm, dslope_of_ne _ hz,
      slope_def_module, hT0]
    simp only [sub_zero, smul_eq_mul]
    field_simp [hz]

def normalizedPrimeArchMomentGerm : ℂ → ℂ :=
  normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace

theorem normalizedPrimeArch_differential_identity :
    (fun z : ℂ => deriv XiC z + z * normalizedPrimeArchMomentGerm z * XiC z) =ᶠ[𝓝 0]
      fun _ => 0 := by
  have hinv := congrFun
    (oddTracePreimage_normalizedTraceMomentGerm_eq
      continuedPrimeArchSourceRelativeTrace continuedPrimeArchSourceRelativeTrace_zero)
  have hsource := continuedPrimeArchSourceRelativeTrace_eventuallyEq_logDeriv_XiC
  have hXi : ∀ᶠ z in 𝓝 0, XiC z ≠ 0 :=
    (XiC_analytic 0 (Set.mem_univ 0)).continuousAt.eventually_ne XiC_zero_ne
  filter_upwards [hsource, hXi] with z hzsource hXiz
  rw [logDeriv_apply] at hzsource
  have hratio : -(z * normalizedPrimeArchMomentGerm z) = deriv XiC z / XiC z := by
    calc
      -(z * normalizedPrimeArchMomentGerm z) =
          oddTracePreimage (normalizedTraceMomentGerm
            continuedPrimeArchSourceRelativeTrace) z := by
            simp [normalizedPrimeArchMomentGerm, oddTracePreimage]
      _ = continuedPrimeArchSourceRelativeTrace z := hinv z
      _ = deriv XiC z / XiC z := hzsource
  have hratio' := hratio.symm
  rw [div_eq_iff hXiz] at hratio'
  rw [hratio']
  ring

theorem iteratedDeriv_normalizedPrimeArchMomentGerm_two_mul (n : ℕ) :
    iteratedDeriv (2 * n) normalizedPrimeArchMomentGerm 0 =
      (((2 * n).factorial : ℕ) : ℂ) *
        (analyticTraceMoments normalizedPrimeArchMomentGerm n : ℝ) := by
  have heq := normalizedTraceMomentGerm_continuedPrimeArchSource_eventuallyEq_momentGerm
  have hderEq : iteratedDeriv (2 * n) normalizedPrimeArchMomentGerm 0 =
      iteratedDeriv (2 * n) xiCentralMomentGerm 0 := by
    exact heq.iteratedDeriv_eq (2 * n)
  have hp := xiCentralMomentPowerSeries.hasFPowerSeriesOnBall
    xiCentralMomentPowerSeries_radius_pos
  have hfac := hp.factorial_smul (1 : ℂ) (2 * n)
  have hderiv : iteratedDeriv (2 * n) xiCentralMomentGerm 0 =
      (((2 * n).factorial : ℕ) : ℂ) * xiCentralReciprocalMoment n := by
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
      Finset.prod_const_one, one_smul] at hfac
    rw [xiCentralMomentPowerSeries, FormalMultilinearSeries.ofScalars_apply_eq,
      one_pow, smul_eq_mul, mul_one, xiCentralMomentCoefficient_two_mul] at hfac
    rw [xiCentralMomentGerm]
    simpa only [xiCentralMomentPowerSeries, nsmul_eq_mul] using hfac.symm
  rw [hderEq, hderiv, ← primeArchSourceMoment_eq_xiCentralReciprocalMoment]
  rfl

theorem iteratedDeriv_normalizedPrimeArchMomentGerm_odd_zero {n : ℕ} (hn : Odd n) :
    iteratedDeriv n normalizedPrimeArchMomentGerm 0 = 0 := by
  have hderEq := normalizedTraceMomentGerm_continuedPrimeArchSource_eventuallyEq_momentGerm
    |>.iteratedDeriv_eq n
  change iteratedDeriv n
    (normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace) 0 = 0
  rw [hderEq]
  have hp := xiCentralMomentPowerSeries.hasFPowerSeriesOnBall
    xiCentralMomentPowerSeries_radius_pos
  have hfac := hp.factorial_smul (1 : ℂ) n
  have hnmod : n % 2 ≠ 0 := by
    rw [Nat.odd_iff] at hn
    omega
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const_one, one_smul] at hfac
  rw [xiCentralMomentPowerSeries, FormalMultilinearSeries.ofScalars_apply_eq,
    one_pow, smul_eq_mul, mul_one, xiCentralMomentCoefficient, if_neg hnmod] at hfac
  rw [xiCentralMomentGerm]
  simpa only [xiCentralMomentPowerSeries, nsmul_eq_mul, mul_zero] using hfac.symm

def thetaCuspNormalizedEvenMoment (n : ℕ) : ℝ :=
  thetaCuspRawEvenMoment n / thetaCuspRawEvenMoment 0

def normalizedPrimeArchMoment (n : ℕ) : ℝ :=
  analyticTraceMoments normalizedPrimeArchMomentGerm n

theorem thetaCuspRawEvenMoment_zero_pos : 0 < thetaCuspRawEvenMoment 0 := by
  rw [thetaCuspRawEvenMoment]
  simpa using (mul_pos (by norm_num : (0 : ℝ) < 2)
    integral_Ioi_thetaCuspFullSource_pos)

theorem normalizedPrimeArchMomentGerm_zero :
    normalizedPrimeArchMomentGerm 0 = (normalizedPrimeArchMoment 0 : ℝ) := by
  have h := iteratedDeriv_normalizedPrimeArchMomentGerm_two_mul 0
  simpa [iteratedDeriv_zero, normalizedPrimeArchMoment] using h

theorem normalizedPrimeArchMomentGerm_second :
    iteratedDeriv 2 normalizedPrimeArchMomentGerm 0 =
      2 * (normalizedPrimeArchMoment 1 : ℝ) := by
  have h := iteratedDeriv_normalizedPrimeArchMomentGerm_two_mul 1
  norm_num [normalizedPrimeArchMoment] at h ⊢
  exact h

theorem normalizedPrimeArchMomentGerm_fourth :
    iteratedDeriv 4 normalizedPrimeArchMomentGerm 0 =
      24 * (normalizedPrimeArchMoment 2 : ℝ) := by
  have h := iteratedDeriv_normalizedPrimeArchMomentGerm_two_mul 2
  norm_num [normalizedPrimeArchMoment] at h ⊢
  exact h

theorem iteratedDeriv_XiC_odd_zero {n : ℕ} (hn : Odd n) :
    iteratedDeriv n XiC 0 = 0 := by
  simpa only [iteratedDeriv_eq_iterate] using
    (iteratedDeriv_odd_eq_zero_of_symmetric
      (f := XiC) (c := 0) XiC_analytic
      (by
        intro z
        rw [show 2 * (0 : ℂ) - z = -z by ring]
        exact XiC_even z)
      hn)

theorem iteratedDeriv_id_mul_zero_succ
    (f : ℂ → ℂ) (n : ℕ) (hf : ContDiffAt ℂ (n + 1 : ℕ∞) f 0) :
    iteratedDeriv (n + 1) (fun z => z * f z) 0 =
      (n + 1 : ℕ) * iteratedDeriv n f 0 := by
  have hid : ContDiffAt ℂ (n + 1 : ℕ∞) (fun z : ℂ => z) 0 := by fun_prop
  rw [show (fun z : ℂ => z * f z) = (fun z => z) * f by rfl,
    iteratedDeriv_mul hid hf]
  rw [Finset.sum_eq_single 1]
  · simp [iteratedDeriv_fun_id_zero]
  · intro b hb hb1
    simp [iteratedDeriv_fun_id_zero, hb1]
  · simp

theorem normalizedPrimeArch_recurrence_one :
    iteratedDeriv 2 XiC 0 +
      normalizedPrimeArchMomentGerm 0 * XiC 0 = 0 := by
  have h := normalizedPrimeArch_differential_identity.iteratedDeriv_eq 1
  have hXi : AnalyticAt ℂ XiC 0 := XiC_analytic 0 (Set.mem_univ 0)
  have hG : AnalyticAt ℂ normalizedPrimeArchMomentGerm 0 :=
    analyticAt_normalizedTraceMomentGerm_continuedPrimeArchSource
  have hZG : AnalyticAt ℂ (fun z : ℂ => z * normalizedPrimeArchMomentGerm z) 0 :=
    analyticAt_id.mul hG
  change iteratedDeriv 1
    (deriv XiC + (fun z : ℂ => z * normalizedPrimeArchMomentGerm z) * XiC) 0 =
      iteratedDeriv 1 (fun _ : ℂ => 0) 0 at h
  rw [iteratedDeriv_add hXi.deriv.contDiffAt (hZG.mul hXi).contDiffAt,
    iteratedDeriv_mul hZG.contDiffAt hXi.contDiffAt] at h
  have hshift : iteratedDeriv 1 (deriv XiC) 0 = iteratedDeriv 2 XiC 0 := by
    exact (congrFun (iteratedDeriv_succ' (f := XiC) (n := 1)) 0).symm
  rw [hshift] at h
  have hZG0 : iteratedDeriv 0 (fun z : ℂ => z * normalizedPrimeArchMomentGerm z) 0 = 0 := by
    simp [iteratedDeriv_zero]
  have hZG1 : iteratedDeriv 1 (fun z : ℂ => z * normalizedPrimeArchMomentGerm z) 0 =
      normalizedPrimeArchMomentGerm 0 := by
    simpa using iteratedDeriv_id_mul_zero_succ normalizedPrimeArchMomentGerm 0
      hG.contDiffAt
  norm_num [Finset.sum_range_succ, hZG0, hZG1] at h
  exact h

theorem normalizedPrimeArch_recurrence_one_moment :
    iteratedDeriv 2 XiC 0 +
      (normalizedPrimeArchMoment 0 : ℝ) * XiC 0 = 0 := by
  simpa [normalizedPrimeArchMomentGerm_zero] using normalizedPrimeArch_recurrence_one

theorem normalizedPrimeArch_recurrence_three :
    iteratedDeriv 4 XiC 0 +
      3 * (normalizedPrimeArchMoment 0 : ℝ) * iteratedDeriv 2 XiC 0 +
      6 * (normalizedPrimeArchMoment 1 : ℝ) * XiC 0 = 0 := by
  have h := normalizedPrimeArch_differential_identity.iteratedDeriv_eq 3
  have hXi : AnalyticAt ℂ XiC 0 := XiC_analytic 0 (Set.mem_univ 0)
  have hG : AnalyticAt ℂ normalizedPrimeArchMomentGerm 0 :=
    analyticAt_normalizedTraceMomentGerm_continuedPrimeArchSource
  have hZG : AnalyticAt ℂ (fun z : ℂ => z * normalizedPrimeArchMomentGerm z) 0 :=
    analyticAt_id.mul hG
  change iteratedDeriv 3
    (deriv XiC + (fun z : ℂ => z * normalizedPrimeArchMomentGerm z) * XiC) 0 =
      iteratedDeriv 3 (fun _ : ℂ => 0) 0 at h
  rw [iteratedDeriv_add hXi.deriv.contDiffAt (hZG.mul hXi).contDiffAt,
    iteratedDeriv_mul hZG.contDiffAt hXi.contDiffAt] at h
  have hshift : iteratedDeriv 3 (deriv XiC) 0 = iteratedDeriv 4 XiC 0 :=
    (congrFun (iteratedDeriv_succ' (f := XiC) (n := 3)) 0).symm
  rw [hshift] at h
  have hZG0 : iteratedDeriv 0 (fun z : ℂ => z * normalizedPrimeArchMomentGerm z) 0 = 0 := by
    simp [iteratedDeriv_zero]
  have hZG1 : iteratedDeriv 1 (fun z : ℂ => z * normalizedPrimeArchMomentGerm z) 0 =
      (normalizedPrimeArchMoment 0 : ℝ) := by
    simpa [normalizedPrimeArchMomentGerm_zero] using
      iteratedDeriv_id_mul_zero_succ normalizedPrimeArchMomentGerm 0 hG.contDiffAt
  have hZG2 : iteratedDeriv 2 (fun z : ℂ => z * normalizedPrimeArchMomentGerm z) 0 = 0 := by
    rw [iteratedDeriv_id_mul_zero_succ normalizedPrimeArchMomentGerm 1 hG.contDiffAt,
      iteratedDeriv_normalizedPrimeArchMomentGerm_odd_zero (n := 1) (by decide)]
    norm_num
  have hZG3 : iteratedDeriv 3 (fun z : ℂ => z * normalizedPrimeArchMomentGerm z) 0 =
      6 * (normalizedPrimeArchMoment 1 : ℝ) := by
    rw [iteratedDeriv_id_mul_zero_succ normalizedPrimeArchMomentGerm 2 hG.contDiffAt,
      normalizedPrimeArchMomentGerm_second]
    ring
  have hXi1 : iteratedDeriv 1 XiC 0 = 0 :=
    iteratedDeriv_XiC_odd_zero (by decide)
  have hXi3 : iteratedDeriv 3 XiC 0 = 0 :=
    iteratedDeriv_XiC_odd_zero (by decide)
  norm_num [Finset.sum_range_succ, hZG0, hZG1, hZG2, hZG3, hXi1, hXi3] at h
  simpa [add_assoc] using h

theorem normalizedPrimeArch_recurrence_five :
    iteratedDeriv 6 XiC 0 +
      5 * (normalizedPrimeArchMoment 0 : ℝ) * iteratedDeriv 4 XiC 0 +
      60 * (normalizedPrimeArchMoment 1 : ℝ) * iteratedDeriv 2 XiC 0 +
      120 * (normalizedPrimeArchMoment 2 : ℝ) * XiC 0 = 0 := by
  have h := normalizedPrimeArch_differential_identity.iteratedDeriv_eq 5
  have hXi : AnalyticAt ℂ XiC 0 := XiC_analytic 0 (Set.mem_univ 0)
  have hG : AnalyticAt ℂ normalizedPrimeArchMomentGerm 0 :=
    analyticAt_normalizedTraceMomentGerm_continuedPrimeArchSource
  have hZG : AnalyticAt ℂ (fun z : ℂ => z * normalizedPrimeArchMomentGerm z) 0 :=
    analyticAt_id.mul hG
  change iteratedDeriv 5
    (deriv XiC + (fun z : ℂ => z * normalizedPrimeArchMomentGerm z) * XiC) 0 =
      iteratedDeriv 5 (fun _ : ℂ => 0) 0 at h
  rw [iteratedDeriv_add hXi.deriv.contDiffAt (hZG.mul hXi).contDiffAt,
    iteratedDeriv_mul hZG.contDiffAt hXi.contDiffAt] at h
  have hshift : iteratedDeriv 5 (deriv XiC) 0 = iteratedDeriv 6 XiC 0 :=
    (congrFun (iteratedDeriv_succ' (f := XiC) (n := 5)) 0).symm
  rw [hshift] at h
  have hZG0 : iteratedDeriv 0 (fun z : ℂ => z * normalizedPrimeArchMomentGerm z) 0 = 0 := by
    simp [iteratedDeriv_zero]
  have hZG1 : iteratedDeriv 1 (fun z : ℂ => z * normalizedPrimeArchMomentGerm z) 0 =
      (normalizedPrimeArchMoment 0 : ℝ) := by
    simpa [normalizedPrimeArchMomentGerm_zero] using
      iteratedDeriv_id_mul_zero_succ normalizedPrimeArchMomentGerm 0 hG.contDiffAt
  have hZG2 : iteratedDeriv 2 (fun z : ℂ => z * normalizedPrimeArchMomentGerm z) 0 = 0 := by
    rw [iteratedDeriv_id_mul_zero_succ normalizedPrimeArchMomentGerm 1 hG.contDiffAt,
      iteratedDeriv_normalizedPrimeArchMomentGerm_odd_zero (n := 1) (by decide)]
    norm_num
  have hZG3 : iteratedDeriv 3 (fun z : ℂ => z * normalizedPrimeArchMomentGerm z) 0 =
      6 * (normalizedPrimeArchMoment 1 : ℝ) := by
    rw [iteratedDeriv_id_mul_zero_succ normalizedPrimeArchMomentGerm 2 hG.contDiffAt,
      normalizedPrimeArchMomentGerm_second]
    ring
  have hZG4 : iteratedDeriv 4 (fun z : ℂ => z * normalizedPrimeArchMomentGerm z) 0 = 0 := by
    rw [iteratedDeriv_id_mul_zero_succ normalizedPrimeArchMomentGerm 3 hG.contDiffAt,
      iteratedDeriv_normalizedPrimeArchMomentGerm_odd_zero (n := 3) (by decide)]
    norm_num
  have hZG5 : iteratedDeriv 5 (fun z : ℂ => z * normalizedPrimeArchMomentGerm z) 0 =
      120 * (normalizedPrimeArchMoment 2 : ℝ) := by
    rw [iteratedDeriv_id_mul_zero_succ normalizedPrimeArchMomentGerm 4 hG.contDiffAt,
      normalizedPrimeArchMomentGerm_fourth]
    ring
  have hXi1 : iteratedDeriv 1 XiC 0 = 0 :=
    iteratedDeriv_XiC_odd_zero (by decide)
  have hXi3 : iteratedDeriv 3 XiC 0 = 0 :=
    iteratedDeriv_XiC_odd_zero (by decide)
  have hXi5 : iteratedDeriv 5 XiC 0 = 0 :=
    iteratedDeriv_XiC_odd_zero (by decide)
  norm_num [Finset.sum_range_succ, Nat.choose, hZG0, hZG1, hZG2, hZG3, hZG4, hZG5,
    hXi1, hXi3, hXi5] at h
  convert h using 1
  ring

theorem iteratedDeriv_XiC_zero_eq_rawEvenMoment (n : ℕ) :
    iteratedDeriv (2 * n) XiC 0 =
      (((-1 : ℝ) ^ n * thetaCuspRawEvenMoment n : ℝ) : ℂ) := by
  calc
    iteratedDeriv (2 * n) XiC 0 =
        ((iteratedDeriv (2 * n) Xi 0 : ℝ) : ℂ) := by
      simpa using iteratedDeriv_XiC_ofReal (2 * n) 0
    _ = (((-1 : ℝ) ^ n * thetaCuspRawEvenMoment n : ℝ) : ℂ) := by
      rw [iteratedDeriv_Xi_zero_eq_rawEvenMoment]

theorem normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment :
    normalizedPrimeArchMoment 0 = thetaCuspNormalizedEvenMoment 1 := by
  have h := normalizedPrimeArch_recurrence_one_moment
  rw [iteratedDeriv_XiC_zero_eq_rawEvenMoment 1,
    show XiC 0 = ((thetaCuspRawEvenMoment 0 : ℝ) : ℂ) by
      simpa [iteratedDeriv_zero] using iteratedDeriv_XiC_zero_eq_rawEvenMoment 0] at h
  norm_num at h
  have hr : -thetaCuspRawEvenMoment 1 +
      normalizedPrimeArchMoment 0 * thetaCuspRawEvenMoment 0 = 0 := by
    exact_mod_cast h
  rw [thetaCuspNormalizedEvenMoment]
  apply (eq_div_iff thetaCuspRawEvenMoment_zero_pos.ne').2
  linarith

theorem normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment :
    normalizedPrimeArchMoment 1 =
      thetaCuspNormalizedEvenMoment 1 ^ 2 / 2 -
        thetaCuspNormalizedEvenMoment 2 / 6 := by
  have h := normalizedPrimeArch_recurrence_three
  rw [iteratedDeriv_XiC_zero_eq_rawEvenMoment 2,
    iteratedDeriv_XiC_zero_eq_rawEvenMoment 1,
    show XiC 0 = ((thetaCuspRawEvenMoment 0 : ℝ) : ℂ) by
      simpa [iteratedDeriv_zero] using iteratedDeriv_XiC_zero_eq_rawEvenMoment 0] at h
  norm_num at h
  have hr : thetaCuspRawEvenMoment 2 -
      3 * normalizedPrimeArchMoment 0 * thetaCuspRawEvenMoment 1 +
      6 * normalizedPrimeArchMoment 1 * thetaCuspRawEvenMoment 0 = 0 := by
    exact_mod_cast h
  rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment] at hr
  simp only [thetaCuspNormalizedEvenMoment] at hr ⊢
  field_simp [thetaCuspRawEvenMoment_zero_pos.ne'] at hr ⊢
  nlinarith

theorem normalizedPrimeArchMoment_two_eq_thetaCuspNormalizedEvenMoment :
    normalizedPrimeArchMoment 2 =
      thetaCuspNormalizedEvenMoment 3 / 120 -
        thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 2 / 8 +
        thetaCuspNormalizedEvenMoment 1 ^ 3 / 4 := by
  have h := normalizedPrimeArch_recurrence_five
  rw [iteratedDeriv_XiC_zero_eq_rawEvenMoment 3,
    iteratedDeriv_XiC_zero_eq_rawEvenMoment 2,
    iteratedDeriv_XiC_zero_eq_rawEvenMoment 1,
    show XiC 0 = ((thetaCuspRawEvenMoment 0 : ℝ) : ℂ) by
      simpa [iteratedDeriv_zero] using iteratedDeriv_XiC_zero_eq_rawEvenMoment 0] at h
  norm_num at h
  have hr : -thetaCuspRawEvenMoment 3 +
      5 * normalizedPrimeArchMoment 0 * thetaCuspRawEvenMoment 2 -
      60 * normalizedPrimeArchMoment 1 * thetaCuspRawEvenMoment 1 +
      120 * normalizedPrimeArchMoment 2 * thetaCuspRawEvenMoment 0 = 0 := by
    exact_mod_cast h
  rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment,
    normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment] at hr
  simp only [thetaCuspNormalizedEvenMoment] at hr ⊢
  field_simp [thetaCuspRawEvenMoment_zero_pos.ne'] at hr ⊢
  nlinarith

theorem normalizedPrimeArch_firstHankelMinor_eq_thetaCuspMoments :
    normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
        normalizedPrimeArchMoment 1 ^ 2 =
      thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 3 / 120 +
        thetaCuspNormalizedEvenMoment 1 ^ 2 * thetaCuspNormalizedEvenMoment 2 / 24 -
        thetaCuspNormalizedEvenMoment 2 ^ 2 / 36 := by
  rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment,
    normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment,
    normalizedPrimeArchMoment_two_eq_thetaCuspNormalizedEvenMoment]
  ring

theorem normalizedPrimeArch_firstHankelMinor_scaled_eq_thetaCuspMoments :
    360 * (normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
        normalizedPrimeArchMoment 1 ^ 2) =
      3 * thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 3 +
        15 * thetaCuspNormalizedEvenMoment 1 ^ 2 * thetaCuspNormalizedEvenMoment 2 -
        10 * thetaCuspNormalizedEvenMoment 2 ^ 2 := by
  rw [normalizedPrimeArch_firstHankelMinor_eq_thetaCuspMoments]
  ring

theorem primeArchSourceTraceHankel_linear (a b : ℝ) :
    (primeArchSourceTraceHankel (C a + C b * X)).re =
      a ^ 2 * normalizedPrimeArchMoment 0 +
        2 * a * b * normalizedPrimeArchMoment 1 +
        b ^ 2 * normalizedPrimeArchMoment 2 := by
  by_cases hb : b = 0
  · subst b
    have hreal : (C a + C (0 : ℝ) * X : Polynomial ℝ) = C a := by simp
    have hmap0 : (C a : Polynomial ℝ).map (algebraMap ℝ ℂ) = C (a : ℂ) := by simp
    have hpow : (C (a : ℂ) : Polynomial ℂ) ^ 2 = C ((a : ℂ) ^ 2) := by
      rw [C_pow]
    unfold primeArchSourceTraceHankel normalizedPrimeArchMoment normalizedPrimeArchMomentGerm
    rw [hreal, hmap0, hpow]
    rw [natDegree_C]
    norm_num only [Finset.sum_range_succ, coeff_C_zero, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    simp only [zero_add, zero_mul, add_zero, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  · have hbC : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb
    have hlin : (C (a : ℂ) + C (b : ℂ) * X : Polynomial ℂ).natDegree = 1 := by
      calc
        (C (a : ℂ) + C (b : ℂ) * X : Polynomial ℂ).natDegree =
            (C (b : ℂ) * X : Polynomial ℂ).natDegree :=
          natDegree_add_eq_right_of_natDegree_lt (by
            rw [natDegree_C, natDegree_C_mul_X (b : ℂ) hbC]
            norm_num)
        _ = 1 := natDegree_C_mul_X (b : ℂ) hbC
    have hdeg : ((C (a : ℂ) + C (b : ℂ) * X : Polynomial ℂ) ^ 2).natDegree = 2 := by
      rw [natDegree_pow, hlin]
    have hmap : (C a + C b * X).map (algebraMap ℝ ℂ) =
        (C (a : ℂ) + C (b : ℂ) * X : Polynomial ℂ) := by simp
    have hsq : (C (a : ℂ) + C (b : ℂ) * X : Polynomial ℂ) ^ 2 =
        C ((a : ℂ) ^ 2) +
          (C ((a : ℂ) * b) + C ((a : ℂ) * b)) * X +
          C ((b : ℂ) ^ 2) * X ^ 2 := by
      rw [show C ((a : ℂ) ^ 2) = C (a : ℂ) ^ 2 by rw [C_pow],
        show C ((b : ℂ) ^ 2) = C (b : ℂ) ^ 2 by rw [C_pow],
        show C ((a : ℂ) * b) = C (a : ℂ) * C (b : ℂ) by rw [C_mul]]
      ring
    unfold primeArchSourceTraceHankel normalizedPrimeArchMoment normalizedPrimeArchMomentGerm
    rw [hmap, hdeg, hsq]
    simp only [Finset.sum_range_succ, coeff_add, coeff_mul, coeff_C, coeff_X,
      coeff_X_pow]
    norm_num [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow]
    simp only [Complex.ofReal_re]
    ring

theorem thetaCuspRawEvenMoment_one_pos : 0 < thetaCuspRawEvenMoment 1 := by
  simpa [thetaCuspRawEvenMoment] using
    (mul_pos (show (0 : ℝ) < 2 by norm_num) integral_Ioi_thetaCuspSecondMoment_pos)

theorem normalizedPrimeArchMoment_zero_pos : 0 < normalizedPrimeArchMoment 0 := by
  rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment,
    thetaCuspNormalizedEvenMoment]
  exact div_pos thetaCuspRawEvenMoment_one_pos thetaCuspRawEvenMoment_zero_pos

theorem forall_primeArchSourceTraceHankel_linear_nonneg_iff_firstMinor :
    (∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re) ↔
      0 ≤ normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
        normalizedPrimeArchMoment 1 ^ 2 := by
  constructor
  · intro h
    have htest := h (-normalizedPrimeArchMoment 1) (normalizedPrimeArchMoment 0)
    rw [primeArchSourceTraceHankel_linear] at htest
    have hprod : 0 ≤ normalizedPrimeArchMoment 0 *
        (normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
          normalizedPrimeArchMoment 1 ^ 2) := by
      nlinarith
    nlinarith [normalizedPrimeArchMoment_zero_pos]
  · intro hminor a b
    rw [primeArchSourceTraceHankel_linear]
    have hsquare : 0 ≤
        (normalizedPrimeArchMoment 0 * a + normalizedPrimeArchMoment 1 * b) ^ 2 :=
      sq_nonneg _
    have hdefect : 0 ≤
        (normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
          normalizedPrimeArchMoment 1 ^ 2) * b ^ 2 :=
      mul_nonneg hminor (sq_nonneg b)
    nlinarith [normalizedPrimeArchMoment_zero_pos]

def ThetaCuspSixthMomentHankelInequality : Prop :=
  0 ≤ 3 * thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 3 +
    15 * thetaCuspNormalizedEvenMoment 1 ^ 2 * thetaCuspNormalizedEvenMoment 2 -
    10 * thetaCuspNormalizedEvenMoment 2 ^ 2

theorem normalizedPrimeArch_firstMinor_nonneg_iff_thetaCuspSixthMomentHankelInequality :
    0 ≤ normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
        normalizedPrimeArchMoment 1 ^ 2 ↔
      ThetaCuspSixthMomentHankelInequality := by
  rw [ThetaCuspSixthMomentHankelInequality]
  have hscaled := normalizedPrimeArch_firstHankelMinor_scaled_eq_thetaCuspMoments
  constructor <;> intro h <;> nlinarith

theorem forall_primeArchSourceTraceHankel_linear_nonneg_iff_thetaCuspSixthMomentHankelInequality :
    (∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re) ↔
      ThetaCuspSixthMomentHankelInequality := by
  rw [forall_primeArchSourceTraceHankel_linear_nonneg_iff_firstMinor,
    normalizedPrimeArch_firstMinor_nonneg_iff_thetaCuspSixthMomentHankelInequality]

/-! ### Fourth-moment reduction of the first nonconstant source test -/

theorem integrableOn_thetaCuspRawMoment (n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ n * thetaCuspFullSource x) (Ioi 0) := by
  have hmajor := thetaCuspSchwartzReal.integrable_pow_mul (volume : Measure ℝ) n
  apply Integrable.integrableOn
  apply hmajor.mono
  · exact ((continuous_id.pow n).mul
      contDiff_thetaCuspFullSource.continuous).aestronglyMeasurable
  · filter_upwards with x
    simp [Real.norm_eq_abs]

/-- Cauchy--Schwarz log-convexity for the second, fourth, and sixth moments of the positive
theta-cusp source. -/
theorem thetaCuspRawEvenMoment_two_sq_le_one_mul_three :
    thetaCuspRawEvenMoment 2 ^ 2 ≤
      thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℝ → ℝ := fun x => x * Real.sqrt (thetaCuspFullSource x)
  let g : ℝ → ℝ := fun x => x ^ 3 * Real.sqrt (thetaCuspFullSource x)
  have hphi : 0 ≤ᵐ[μ] thetaCuspFullSource := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (thetaCuspFullSource_pos_of_pos hx).le
  have hf_meas : AEStronglyMeasurable f μ := by
    exact (((continuous_id.mul
      (Real.continuous_sqrt.comp
        contDiff_thetaCuspFullSource.continuous))).aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  have hg_meas : AEStronglyMeasurable g μ := by
    exact ((((continuous_id.pow 3).mul
      (Real.continuous_sqrt.comp
        contDiff_thetaCuspFullSource.continuous))).aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  have hf_sq : Integrable (fun x => f x ^ 2) μ := by
    have h := integrableOn_thetaCuspRawMoment 2
    apply h.congr
    filter_upwards [hphi] with x hx
    dsimp [f]
    rw [mul_pow, Real.sq_sqrt hx]
  have hg_sq : Integrable (fun x => g x ^ 2) μ := by
    have h := integrableOn_thetaCuspRawMoment 6
    apply h.congr
    filter_upwards [hphi] with x hx
    dsimp [g]
    rw [mul_pow, Real.sq_sqrt hx]
    ring
  have hf : MemLp f 2 μ :=
    (memLp_two_iff_integrable_sq hf_meas).2 hf_sq
  have hg : MemLp g 2 μ :=
    (memLp_two_iff_integrable_sq hg_meas).2 hg_sq
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hg
  have hcs := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (p := (2 : ℝ)) (q := (2 : ℝ))
    (Real.HolderConjugate.two_two) hf' hg'
  have hfg : (∫ x, ‖f x‖ * ‖g x‖ ∂μ) =
      ∫ x in Ioi 0, x ^ 4 * thetaCuspFullSource x := by
    apply integral_congr_ae
    filter_upwards [hphi, ae_restrict_mem measurableSet_Ioi] with x hx hxi
    dsimp [f, g]
    rw [abs_of_nonneg (mul_nonneg hxi.le (Real.sqrt_nonneg _)),
      abs_of_nonneg (mul_nonneg (pow_nonneg hxi.le 3) (Real.sqrt_nonneg _))]
    calc
      x * √(thetaCuspFullSource x) * (x ^ 3 * √(thetaCuspFullSource x)) =
          x ^ 4 * (√(thetaCuspFullSource x)) ^ 2 := by ring
      _ = x ^ 4 * thetaCuspFullSource x := by rw [Real.sq_sqrt hx]
  have hf2 : (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) =
      ∫ x in Ioi 0, x ^ 2 * thetaCuspFullSource x := by
    apply integral_congr_ae
    filter_upwards [hphi] with x hx
    dsimp [f]
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
    calc
      |x * √(thetaCuspFullSource x)| ^ 2 =
          (x * √(thetaCuspFullSource x)) ^ 2 := sq_abs _
      _ = x ^ 2 * thetaCuspFullSource x := by
        rw [mul_pow, Real.sq_sqrt hx]
  have hg2 : (∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ) =
      ∫ x in Ioi 0, x ^ 6 * thetaCuspFullSource x := by
    apply integral_congr_ae
    filter_upwards [hphi] with x hx
    dsimp [g]
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
    calc
      |x ^ 3 * √(thetaCuspFullSource x)| ^ 2 =
          (x ^ 3 * √(thetaCuspFullSource x)) ^ 2 := sq_abs _
      _ = x ^ 6 * thetaCuspFullSource x := by
        rw [mul_pow, Real.sq_sqrt hx]
        ring
  rw [hfg, hf2, hg2] at hcs
  have hm1 : 0 ≤ ∫ x in Ioi 0, x ^ 2 * thetaCuspFullSource x := by
    exact integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (sq_nonneg x) (thetaCuspFullSource_pos_of_pos hx).le)
  have hm3 : 0 ≤ ∫ x in Ioi 0, x ^ 6 * thetaCuspFullSource x := by
    exact integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (pow_nonneg hx.le 6) (thetaCuspFullSource_pos_of_pos hx).le)
  have hm2 : 0 ≤ ∫ x in Ioi 0, x ^ 4 * thetaCuspFullSource x := by
    exact integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (pow_nonneg hx.le 4) (thetaCuspFullSource_pos_of_pos hx).le)
  have hcs' : (∫ x in Ioi 0, x ^ 4 * thetaCuspFullSource x) ≤
      Real.sqrt (∫ x in Ioi 0, x ^ 2 * thetaCuspFullSource x) *
        Real.sqrt (∫ x in Ioi 0, x ^ 6 * thetaCuspFullSource x) := by
    simpa only [← Real.sqrt_eq_rpow] using hcs
  have hright : 0 ≤
      Real.sqrt (∫ x in Ioi 0, x ^ 2 * thetaCuspFullSource x) *
        Real.sqrt (∫ x in Ioi 0, x ^ 6 * thetaCuspFullSource x) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq := (sq_le_sq₀ hm2 hright).2 hcs'
  rw [mul_pow] at hsq
  rw [Real.sq_sqrt hm1, Real.sq_sqrt hm3] at hsq
  norm_num [thetaCuspRawEvenMoment]
  nlinarith [hsq]

theorem thetaCuspRawEvenMoment_nonneg (n : ℕ) :
    0 ≤ thetaCuspRawEvenMoment n := by
  rw [thetaCuspRawEvenMoment]
  apply mul_nonneg (by norm_num)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg (pow_nonneg hx.le (2 * n))
    (thetaCuspFullSource_pos_of_pos hx).le

/-- A fourth-moment concentration bound on the positive theta-cusp source.  Unlike the target
sixth-moment inequality, it contains no sixth raw moment. -/
def ThetaCuspFourthMomentConcentration : Prop :=
  7 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 ≤
    15 * thetaCuspRawEvenMoment 1 ^ 2

theorem thetaCusp_raw_cubic_nonneg_of_fourthMomentConcentration
    (hconc : ThetaCuspFourthMomentConcentration) :
    0 ≤ 3 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 1 *
          thetaCuspRawEvenMoment 3 +
        15 * thetaCuspRawEvenMoment 1 ^ 2 * thetaCuspRawEvenMoment 2 -
        10 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 ^ 2 := by
  rw [ThetaCuspFourthMomentConcentration] at hconc
  have hlog := thetaCuspRawEvenMoment_two_sq_le_one_mul_three
  have h0 := thetaCuspRawEvenMoment_nonneg 0
  have h2 := thetaCuspRawEvenMoment_nonneg 2
  have hlog' :
      3 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 ^ 2 ≤
        3 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 1 *
          thetaCuspRawEvenMoment 3 := by
    nlinarith
  have hconc' :
      7 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 ^ 2 ≤
        15 * thetaCuspRawEvenMoment 1 ^ 2 * thetaCuspRawEvenMoment 2 := by
    nlinarith
  nlinarith

/-- The fourth-moment concentration bound discharges the exact sixth-moment criterion for the
first nonconstant continued prime--Gamma source Hankel test. -/
theorem thetaCuspSixthMomentHankelInequality_of_fourthMomentConcentration
    (hconc : ThetaCuspFourthMomentConcentration) :
    ThetaCuspSixthMomentHankelInequality := by
  have hcubic :=
    thetaCusp_raw_cubic_nonneg_of_fourthMomentConcentration hconc
  rw [ThetaCuspSixthMomentHankelInequality]
  simp only [thetaCuspNormalizedEvenMoment]
  have h0 := thetaCuspRawEvenMoment_zero_pos
  field_simp [h0.ne']
  nlinarith [hcubic]

/-- Under fourth-moment concentration, every real linear-polynomial test of the continued
prime--Gamma source trace-Hankel form is nonnegative. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_fourthMomentConcentration
    (hconc : ThetaCuspFourthMomentConcentration) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re := by
  rw [forall_primeArchSourceTraceHankel_linear_nonneg_iff_thetaCuspSixthMomentHankelInequality]
  exact thetaCuspSixthMomentHankelInequality_of_fourthMomentConcentration hconc

end RHTower
