import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalMovingAperture
import GaloisForLFunctions.«arithmetic-positivity-theory».CompactCriticalPolynomialWindowAndTemperednessBridge
import GaloisForLFunctions.«arithmetic-positivity-theory».LacunaryCriticalBlockPositivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Untruncated Collared Extension, Real-Lag Integration by Parts, Regularized Polar Normalization, and Simultaneous Moving-Aperture Shift Thresholds

The collared critical source `g_c = criticalCollaredSource S b` has pointwise envelope
`O(e^{x/2})` on `(-∞, 0]`, giving only critical half-decay `O(e^{-t/2})` on raw correlation bounds.
Consequently, naive envelope domination fails against the growing polar density `cosh(t/2)` and
absolute two-variable Fubini for the untruncated polar moment is unavailable (`∫ |g_c(u)| e^{-u/2} = ∞`).

This module resolves both analytic obstacles unconditionally:

1. **Real-Lag Integration by Parts (`intervalIntegral_realLag_phase_ibp`,
   `integral_Ioi_realLag_phase_ibp`):**
   Integrating the dilated phase factor `realPhaseCombination S b (e^t v)` by parts against its
   globally bounded primitive `criticalFactorialPhasePrimitive S b (e^t v) / e^t` gains an extra
   `e^{-t}` factor on `[log 2, ∞)`, upgrading the correlations of `criticalCollaredSource S b`,
   the sharp `L²` truncations `criticalCollaredSharpTruncation V S b` (explicitly retaining the
   moving upper boundary `(ψ(V/e^t) B_b(V/e^t)) G_b(V)/e^t`), and the smooth truncations
   `criticalTruncatedSource V S b` to `V`-uniform `O(e^{-3t/2})` supercritical decay.

2. **Regularized Polar Normalization (`integral_polar_autocorr_eq_moments_of_memLp`,
   `four_mul_integral_autocorr_cosh_criticalCollaredSource`,
   `integral_polar_autocorr_criticalCollaredSource`):**
   Applying compact `L²` polar Fubini to `g_V = (Icc (-log V) 0).indicator g_c` at each finite
   `V ≥ 1` factors the polar integral into `(∫ g_V e^{u/2}) (∫ g_V e^{-u/2})`, while the uniform
   `O(e^{-3t/2})` bound dominates `autocorr g_V t * cosh(t/2)` by `O(e^{-t})` uniformly in `V ≥ 1`,
   identifying `4 ∫_{t>0} autocorr g_c t cosh(t/2) = 2 R_c E_c` and
   `suzukiCriticalExtendedWeilEnergy g_c = criticalCollaredCompleteEnergy S b` as `V → ∞`.

3. **Untruncated Collared Complete First Variation and Uniform Moving-Aperture Shifts
   (`tendsto_suzukiCriticalCollaredSource_firstVariation`,
   `exists_suzukiCriticalUniformShift_of_collared_family`,
   `exists_dyadic_uniform_movingAperture_suzukiDeficit`,
   `exists_polynomial_window_uniform_movingAperture_suzukiDeficit`,
   `exists_lacunary_uniform_movingAperture_suzukiDeficit`):**
   Combining supercritical correlation decay with compactification of `V ∈ [V₀, ∞]` via
   `q = 1 / V ∈ [0, 1 / V₀]` and 2-homogeneity in `b` yields a single shift threshold `ω₀ > 0`
   independent of both `V` and `b`, valid simultaneously across all moving apertures `V ≥ V₀`
   and the untruncated collared limit `g_c` without `C²` smoothness.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Zeta23
open scoped BigOperators ENNReal NNReal CompactlySupported RealInnerProductSpace
open GaloisForLFunctions.BiScaleUncertainty.SobolevShear
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.ArithmeticPositivityTheory
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm

namespace RHTower
noncomputable section

private theorem norm_toLp_sub_eq_sqrt_integral_sq {f g : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ‖hf.toLp f - hg.toLp g‖ = Real.sqrt (∫ x, (f x - g x) ^ 2) := by
  have hsub : MemLp (f - g) 2 volume := hf.sub hg
  have heq : hsub.toLp (f - g) = hf.toLp f - hg.toLp g := MemLp.toLp_sub hf hg
  have hsq : ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, (f x - g x) ^ 2 := by
    rw [← heq, ← autocorr_zero_eq_norm_toLp_sq hsub]
    unfold autocorr
    simp only [Pi.sub_apply, add_zero, sq]
  rw [← Real.sqrt_sq (norm_nonneg (hf.toLp f - hg.toLp g)), hsq]

private theorem sourceAutocorrelation_eq_autocorr' (g : ℝ → ℝ) (x : ℝ) :
    sourceAutocorrelation g x = autocorr g x := by
  rw [← autocorr_neg]
  unfold sourceAutocorrelation autocorr
  simp only [sub_eq_add_neg]

/-! ## Section 1: Real-Lag Integration by Parts Against `criticalFactorialPhasePrimitive` -/

private theorem absolutelyContinuousOnInterval_of_hasDerivAt_continuousOn
    {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hf' : ContinuousOn f' (Icc a b)) :
    AbsolutelyContinuousOnInterval f a b := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf'
  have hs : Convex ℝ (uIcc a b) := by rw [uIcc_of_le hab]; exact convex_Icc a b
  have hdiff : ∀ x ∈ uIcc a b, DifferentiableAt ℝ f x := fun x hx => by
    rw [uIcc_of_le hab] at hx; exact (hf x hx).differentiableAt
  have hbd : ∀ x ∈ uIcc a b, ‖deriv f x‖₊ ≤ Real.toNNReal C := fun x hx => by
    rw [uIcc_of_le hab] at hx
    rw [← NNReal.coe_le_coe, coe_nnnorm, (hf x hx).deriv]
    exact (hC x hx).trans (Real.le_coe_toNNReal C)
  exact (hs.lipschitzOnWith_of_nnnorm_deriv_le hdiff hbd).absolutelyContinuousOnInterval

private theorem lipschitzWith_realPhaseCombination (S : Finset ℕ) (b : ℕ → ℝ) :
    LipschitzWith (Real.toNNReal (realPhaseLipschitz S b)) (realPhaseCombination S b) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (realPhaseLipschitz_nonneg S b), Real.dist_eq, Real.dist_eq]
  exact abs_realPhaseCombination_sub_le S b x y

/-- Pointwise derivative bound `|B_b'(v)| ≤ realPhaseLipschitz S b` everywhere on `ℝ`. -/
theorem abs_deriv_realPhaseCombination_le (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    |deriv (realPhaseCombination S b) v| ≤ realPhaseLipschitz S b := by
  have h := norm_deriv_le_of_lipschitz (x₀ := v) (lipschitzWith_realPhaseCombination S b)
  simpa only [Real.norm_eq_abs, Real.coe_toNNReal _ (realPhaseLipschitz_nonneg S b)] using h

private theorem hasDerivAt_dilated_phasePrimitive (S : Finset ℕ) (b : ℕ → ℝ)
    {r v : ℝ} (hr : 0 < r) (hv : 0 < v) :
    HasDerivAt (fun u => criticalFactorialPhasePrimitive S b (r * u) / r)
      (realPhaseCombination S b (r * v)) v := by
  have h1 := ((criticalFactorialPhasePrimitive_hasDerivAt S b (mul_pos hr hv)).comp v
    ((hasDerivAt_id v).const_mul r)).div_const r
  refine h1.congr_deriv ?_
  rw [factorialPhaseCombination_re_eq]
  field_simp [hr.ne']

/-- **Finite-Endpoint Real-Lag Integration by Parts.**
For every differentiable weight `W` on `[1, T]` (`1 ≤ T`, `W(1) = 0`) with continuous derivative
`W'` and every dilation `r > 0`, integrating `B_b(r v)` against `G_b(r v) / r` yields the exact
upper boundary `(W(T) B_b(T)) (G_b(r T) / r)` minus the `1/r`-scaled bulk integral. -/
theorem intervalIntegral_realLag_phase_ibp {W W' : ℝ → ℝ} {T r : ℝ}
    (hT : 1 ≤ T) (hr : 0 < r)
    (hW : ∀ v ∈ Icc (1 : ℝ) T, HasDerivAt W (W' v) v)
    (hW' : ContinuousOn W' (Icc (1 : ℝ) T)) (hW1 : W 1 = 0)
    (S : Finset ℕ) (b : ℕ → ℝ) :
    ∫ v in (1 : ℝ)..T, W v * (realPhaseCombination S b v * realPhaseCombination S b (r * v)) =
      (W T * realPhaseCombination S b T) * (criticalFactorialPhasePrimitive S b (r * T) / r) -
      ∫ v in (1 : ℝ)..T,
        (realPhaseCombination S b v * W' v + deriv (realPhaseCombination S b) v * W v) *
          (criticalFactorialPhasePrimitive S b (r * v) / r) := by
  set p := realPhaseCombination S b
  set G₀ : ℝ → ℝ := fun v => criticalFactorialPhasePrimitive S b (r * v) / r
  set q : ℝ → ℝ := fun v => W v * G₀ v
  have hp_cont : Continuous p := continuous_realPhaseCombination S b
  have hpr_cont : Continuous (fun v => p (r * v)) :=
    hp_cont.comp (continuous_const.mul continuous_id)
  have hW_cont : ContinuousOn W (Icc 1 T) := fun v hv => (hW v hv).continuousAt.continuousWithinAt
  have hG_cont : ContinuousOn G₀ (Icc 1 T) := fun v hv =>
    (hasDerivAt_dilated_phasePrimitive S b hr
      (lt_of_lt_of_le one_pos hv.1)).continuousAt.continuousWithinAt
  have hp_AC : AbsolutelyContinuousOnInterval p 1 T :=
    (lipschitzWith_realPhaseCombination S b).lipschitzOnWith.absolutelyContinuousOnInterval
  have hW_AC : AbsolutelyContinuousOnInterval W 1 T :=
    absolutelyContinuousOnInterval_of_hasDerivAt_continuousOn hT hW hW'
  have hG_AC : AbsolutelyContinuousOnInterval G₀ 1 T :=
    absolutelyContinuousOnInterval_of_hasDerivAt_continuousOn hT
      (fun v hv => hasDerivAt_dilated_phasePrimitive S b hr (lt_of_lt_of_le one_pos hv.1))
      hpr_cont.continuousOn
  have hq_AC : AbsolutelyContinuousOnInterval q 1 T := hW_AC.fun_mul hG_AC
  have hibp := hp_AC.integral_mul_deriv_eq_deriv_mul hq_AC
  have hq1 : q 1 = 0 := by simp [q, hW1]
  have hlhs_congr : ∫ v in (1 : ℝ)..T, p v * deriv q v =
      ∫ v in (1 : ℝ)..T, (W v * (p v * p (r * v)) + (p v * W' v) * G₀ v) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le hT] at hv
    have hdq : HasDerivAt q (W' v * G₀ v + W v * p (r * v)) v :=
      (hW v hv).mul (hasDerivAt_dilated_phasePrimitive S b hr (lt_of_lt_of_le one_pos hv.1))
    rw [hdq.deriv]
    ring
  have hi_main : IntervalIntegrable (fun v => W v * (p v * p (r * v))) volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT]
    exact hW_cont.mul ((hp_cont.mul hpr_cont).continuousOn)
  have hi_W' : IntervalIntegrable (fun v => (p v * W' v) * G₀ v) volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT]
    exact (hp_cont.continuousOn.mul hW').mul hG_cont
  have hi_dp : IntervalIntegrable (fun v => (deriv p v * W v) * G₀ v) volume 1 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    obtain ⟨Cq, hCq⟩ := isCompact_Icc.exists_bound_of_continuousOn (hW_cont.mul hG_cont)
    have hconst : IntegrableOn (fun _ : ℝ => realPhaseLipschitz S b * max Cq 0) (Ioc 1 T) :=
      continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    refine hconst.mono' ?_ ?_
      · have hm1 : AEStronglyMeasurable (deriv p) (volume.restrict (Ioc 1 T)) :=
          (measurable_deriv p).aestronglyMeasurable
        have hm2 : AEStronglyMeasurable (fun v => W v * G₀ v) (volume.restrict (Ioc 1 T)) :=
          ((hW_cont.mul hG_cont).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
        exact (hm1.mul hm2).congr (Eventually.of_forall fun v => by dsimp only [Pi.mul_apply]; ring)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      have hv_icc : v ∈ Icc 1 T := Ioc_subset_Icc_self hv
      have hq_le : |W v * G₀ v| ≤ max Cq 0 :=
        (Real.norm_eq_abs _ ▸ hCq v hv_icc).trans (le_max_left _ _)
      rw [Real.norm_eq_abs, show (deriv p v * W v) * G₀ v = deriv p v * (W v * G₀ v) by ring,
        abs_mul]
      exact mul_le_mul (abs_deriv_realPhaseCombination_le S b v) hq_le (abs_nonneg _)
        (realPhaseLipschitz_nonneg S b)
  rw [hlhs_congr, intervalIntegral.integral_add hi_main hi_W', hq1, mul_zero, sub_zero] at hibp
  have hrhs_eq : ∫ v in (1 : ℝ)..T, (p v * W' v + deriv p v * W v) * G₀ v =
      (∫ v in (1 : ℝ)..T, (p v * W' v) * G₀ v) +
        ∫ v in (1 : ℝ)..T, (deriv p v * W v) * G₀ v := by
    rw [← intervalIntegral.integral_add hi_W' hi_dp]
    exact intervalIntegral.integral_congr fun v _ => by ring
  rw [hrhs_eq]
  have hdp_eq : ∫ v in (1 : ℝ)..T, deriv p v * q v =
      ∫ v in (1 : ℝ)..T, (deriv p v * W v) * G₀ v :=
    intervalIntegral.integral_congr fun v _ => by dsimp only [q]; ring
  rw [hdp_eq] at hibp
  have hbd_eq : p T * q T = (W T * p T) * G₀ T := by dsimp only [q]; ring
  linarith

/-- **Finite-Endpoint Real-Lag `1/r` Decay Bound.** -/
theorem abs_intervalIntegral_realLag_phase_le {W W' : ℝ → ℝ} {T r : ℝ}
    (hT : 1 ≤ T) (hr : 0 < r)
    (hW : ∀ v ∈ Icc (1 : ℝ) T, HasDerivAt W (W' v) v)
    (hW' : ContinuousOn W' (Icc (1 : ℝ) T)) (hW1 : W 1 = 0)
    (S : Finset ℕ) (b : ℕ → ℝ) :
    |∫ v in (1 : ℝ)..T, W v * (realPhaseCombination S b v * realPhaseCombination S b (r * v))| ≤
      (|W T| * (2 * ∑ n ∈ S, |b n|) +
        (2 * ∑ n ∈ S, |b n|) * (∫ v in (1 : ℝ)..T, |W' v|) +
        realPhaseLipschitz S b * (∫ v in (1 : ℝ)..T, |W v|)) *
      ((12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)) / r) := by
  set p := realPhaseCombination S b
  set Bmax := 2 * ∑ n ∈ S, |b n|
  set Lp := realPhaseLipschitz S b
  set P := 12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)
  have hBmax : 0 ≤ Bmax := mul_nonneg zero_le_two (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hLp : 0 ≤ Lp := realPhaseLipschitz_nonneg S b
  have hG_bd : ∀ y, |criticalFactorialPhasePrimitive S b y / r| ≤ P / r := fun y => by
    rw [abs_div, abs_of_pos hr]
    exact div_le_div_of_nonneg_right (criticalFactorialPhasePrimitive_bound S b y) hr.le
  have hPr : 0 ≤ P / r := (abs_nonneg _).trans (hG_bd 0)
  have hW_cont : ContinuousOn W (Icc 1 T) := fun v hv => (hW v hv).continuousAt.continuousWithinAt
  have hG_cont : ContinuousOn (fun v => criticalFactorialPhasePrimitive S b (r * v) / r) (Icc 1 T) :=
    fun v hv => (hasDerivAt_dilated_phasePrimitive S b hr
      (lt_of_lt_of_le one_pos hv.1)).continuousAt.continuousWithinAt
  have hi_abs_W' : IntervalIntegrable (fun v => |W' v|) volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT]; exact continuous_abs.comp_continuousOn hW'
  have hi_abs_W : IntervalIntegrable (fun v => |W v|) volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT]; exact continuous_abs.comp_continuousOn hW_cont
  have hi_maj : IntervalIntegrable
      (fun v => (Bmax * |W' v| + Lp * |W v|) * (P / r)) volume 1 T :=
    ((hi_abs_W'.const_mul Bmax).add (hi_abs_W.const_mul Lp)).mul_const (P / r)
  have hi_int : IntervalIntegrable
      (fun v => |(p v * W' v + deriv p v * W v) *
        (criticalFactorialPhasePrimitive S b (r * v) / r)|) volume 1 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    have hmaj_on := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hi_maj
    refine hmaj_on.mono' ?_ ?_
    · have hm_p : AEStronglyMeasurable p (volume.restrict (Ioc 1 T)) :=
        (continuous_realPhaseCombination S b).aestronglyMeasurable
      have hm_W' : AEStronglyMeasurable W' (volume.restrict (Ioc 1 T)) :=
        (hW'.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
      have hm_dp : AEStronglyMeasurable (deriv p) (volume.restrict (Ioc 1 T)) :=
        (measurable_deriv p).aestronglyMeasurable
      have hm_W : AEStronglyMeasurable W (volume.restrict (Ioc 1 T)) :=
        (hW_cont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
      have hm_G : AEStronglyMeasurable
          (fun v => criticalFactorialPhasePrimitive S b (r * v) / r)
          (volume.restrict (Ioc 1 T)) :=
        (hG_cont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
      exact (((hm_p.mul hm_W').add (hm_dp.mul hm_W)).mul hm_G).norm
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with v _
      rw [Real.norm_eq_abs, abs_abs, abs_mul]
      have h1 : |p v * W' v + deriv p v * W v| ≤ Bmax * |W' v| + Lp * |W v| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (abs_realPhaseCombination_le_two_mul S b v)
            (abs_nonneg _)
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (abs_deriv_realPhaseCombination_le S b v)
            (abs_nonneg _)
      exact mul_le_mul h1 (hG_bd (r * v)) (abs_nonneg _) (by positivity)
  rw [intervalIntegral_realLag_phase_ibp hT hr hW hW' hW1 S b]
  have hbd_term : |(W T * p T) * (criticalFactorialPhasePrimitive S b (r * T) / r)| ≤
      (|W T| * Bmax) * (P / r) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (abs_realPhaseCombination_le_two_mul S b T) (abs_nonneg _))
      (hG_bd (r * T)) (abs_nonneg _) (by positivity)
  have hint_term : |∫ v in (1 : ℝ)..T,
      (p v * W' v + deriv p v * W v) * (criticalFactorialPhasePrimitive S b (r * v) / r)| ≤
      (Bmax * (∫ v in (1 : ℝ)..T, |W' v|) + Lp * (∫ v in (1 : ℝ)..T, |W v|)) * (P / r) := by
    calc |∫ v in (1 : ℝ)..T,
          (p v * W' v + deriv p v * W v) * (criticalFactorialPhasePrimitive S b (r * v) / r)|
        ≤ ∫ v in (1 : ℝ)..T,
            |(p v * W' v + deriv p v * W v) *
              (criticalFactorialPhasePrimitive S b (r * v) / r)| :=
          intervalIntegral.abs_integral_le_integral_abs hT
      _ ≤ ∫ v in (1 : ℝ)..T, (Bmax * |W' v| + Lp * |W v|) * (P / r) := by
          refine intervalIntegral.integral_mono_on hT hi_int hi_maj fun v _ => ?_
          rw [abs_mul]
          have h1 : |p v * W' v + deriv p v * W v| ≤ Bmax * |W' v| + Lp * |W v| := by
            refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [abs_mul]
              exact mul_le_mul_of_nonneg_right (abs_realPhaseCombination_le_two_mul S b v)
                (abs_nonneg _)
            · rw [abs_mul]
              exact mul_le_mul_of_nonneg_right (abs_deriv_realPhaseCombination_le S b v)
                (abs_nonneg _)
          exact mul_le_mul h1 (hG_bd (r * v)) (abs_nonneg _) (by positivity)
      _ = (Bmax * (∫ v in (1 : ℝ)..T, |W' v|) + Lp * (∫ v in (1 : ℝ)..T, |W v|)) * (P / r) := by
          rw [intervalIntegral.integral_mul_const,
            intervalIntegral.integral_add (hi_abs_W'.const_mul Bmax) (hi_abs_W.const_mul Lp),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  calc |(W T * p T) * (criticalFactorialPhasePrimitive S b (r * T) / r) -
        ∫ v in (1 : ℝ)..T,
          (p v * W' v + deriv p v * W v) * (criticalFactorialPhasePrimitive S b (r * v) / r)|
      ≤ |(W T * p T) * (criticalFactorialPhasePrimitive S b (r * T) / r)| +
        |∫ v in (1 : ℝ)..T,
          (p v * W' v + deriv p v * W v) * (criticalFactorialPhasePrimitive S b (r * v) / r)| :=
        abs_sub _ _
    _ ≤ (|W T| * Bmax) * (P / r) +
        (Bmax * (∫ v in (1 : ℝ)..T, |W' v|) + Lp * (∫ v in (1 : ℝ)..T, |W v|)) * (P / r) :=
        add_le_add hbd_term hint_term
    _ = (|W T| * Bmax + Bmax * (∫ v in (1 : ℝ)..T, |W' v|) + Lp * (∫ v in (1 : ℝ)..T, |W v|)) *
        (P / r) := by ring

/-- **Infinite-Horizon Real-Lag Integration by Parts.** -/
theorem integral_Ioi_realLag_phase_ibp {W W' : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hW : ∀ v ∈ Ici (1 : ℝ), HasDerivAt W (W' v) v)
    (hW' : ContinuousOn W' (Ici (1 : ℝ))) (hW1 : W 1 = 0)
    (hWt : Tendsto W atTop (𝓝 0))
    (hWi : IntegrableOn W (Ioi 1)) (hWi' : IntegrableOn W' (Ioi 1))
    (S : Finset ℕ) (b : ℕ → ℝ) :
    ∫ v in Ioi (1 : ℝ), W v * (realPhaseCombination S b v * realPhaseCombination S b (r * v)) =
      -∫ v in Ioi (1 : ℝ),
        (realPhaseCombination S b v * W' v + deriv (realPhaseCombination S b) v * W v) *
          (criticalFactorialPhasePrimitive S b (r * v) / r) := by
  set p := realPhaseCombination S b
  set Bmax := 2 * ∑ n ∈ S, |b n|
  set Lp := realPhaseLipschitz S b
  set P := 12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)
  have hG_bd : ∀ y, |criticalFactorialPhasePrimitive S b y / r| ≤ P / r := fun y => by
    rw [abs_div, abs_of_pos hr]
    exact div_le_div_of_nonneg_right (criticalFactorialPhasePrimitive_bound S b y) hr.le
  have hPr : 0 ≤ P / r := (abs_nonneg _).trans (hG_bd 0)
  have hp_cont : Continuous p := continuous_realPhaseCombination S b
  have hpr_cont : Continuous (fun v => p (r * v)) :=
    hp_cont.comp (continuous_const.mul continuous_id)
  have hint_lhs : IntegrableOn (fun v => W v * (p v * p (r * v))) (Ioi 1) := by
    refine (hWi.norm.mul_const (Bmax * Bmax)).mono' ?_ ?_
    · exact hWi.aestronglyMeasurable.mul (hp_cont.mul hpr_cont).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (abs_realPhaseCombination_le_two_mul S b v)
          (abs_realPhaseCombination_le_two_mul S b (r * v)) (abs_nonneg _)
          (mul_nonneg zero_le_two (Finset.sum_nonneg fun _ _ => abs_nonneg _)))
        (abs_nonneg _)
  have hG_cont : ContinuousOn (fun v => criticalFactorialPhasePrimitive S b (r * v) / r) (Ioi 1) :=
    fun v hv => (hasDerivAt_dilated_phasePrimitive S b hr
      (lt_trans one_pos hv)).continuousAt.continuousWithinAt
  have hint_rhs : IntegrableOn
      (fun v => (p v * W' v + deriv p v * W v) *
        (criticalFactorialPhasePrimitive S b (r * v) / r)) (Ioi 1) := by
    refine (((hWi'.norm.const_mul Bmax).add (hWi.norm.const_mul Lp)).mul_const (P / r)).mono' ?_ ?_
    · have hm_p : AEStronglyMeasurable p (volume.restrict (Ioi 1)) := hp_cont.aestronglyMeasurable
      have hm_dp : AEStronglyMeasurable (deriv p) (volume.restrict (Ioi 1)) :=
        (measurable_deriv p).aestronglyMeasurable
      exact (((hm_p.mul hWi'.aestronglyMeasurable).add
        (hm_dp.mul hWi.aestronglyMeasurable)).mul
        (hG_cont.aestronglyMeasurable measurableSet_Ioi))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |p v * W' v + deriv p v * W v| ≤ Bmax * |W' v| + Lp * |W v| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (abs_realPhaseCombination_le_two_mul S b v)
            (abs_nonneg _)
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (abs_deriv_realPhaseCombination_le S b v)
            (abs_nonneg _)
      exact mul_le_mul h1 (hG_bd (r * v)) (abs_nonneg _)
        (add_nonneg (mul_nonneg (mul_nonneg zero_le_two
          (Finset.sum_nonneg fun _ _ => abs_nonneg _)) (abs_nonneg _))
          (mul_nonneg (realPhaseLipschitz_nonneg S b) (abs_nonneg _)))
  have hlim_lhs := intervalIntegral_tendsto_integral_Ioi (μ := volume) 1 hint_lhs tendsto_id
  have hlim_rhs := intervalIntegral_tendsto_integral_Ioi (μ := volume) 1 hint_rhs tendsto_id
  have hlim_bd : Tendsto
      (fun T => (W T * p T) * (criticalFactorialPhasePrimitive S b (r * T) / r))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun T => ?_)
      (by simpa using hWt.norm.mul_const (Bmax * (P / r)))
    rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (abs_realPhaseCombination_le_two_mul S b T) (hG_bd (r * T))
        (abs_nonneg _) (mul_nonneg zero_le_two (Finset.sum_nonneg fun _ _ => abs_nonneg _)))
      (abs_nonneg _)
  have hlim_comb := (hlim_bd.sub hlim_rhs).congr' (by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    exact (intervalIntegral_realLag_phase_ibp hT hr
      (fun v hv => hW v hv.1) (hW'.mono fun v hv => hv.1) hW1 S b).symm)
  rw [zero_sub] at hlim_comb
  exact tendsto_nhds_unique hlim_lhs hlim_comb

/-- **Infinite-Horizon Real-Lag `1/r` Decay Bound.** -/
theorem abs_integral_Ioi_realLag_phase_le {W W' : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hW : ∀ v ∈ Ici (1 : ℝ), HasDerivAt W (W' v) v)
    (hW' : ContinuousOn W' (Ici (1 : ℝ))) (hW1 : W 1 = 0)
    (hWt : Tendsto W atTop (𝓝 0))
    (hWi : IntegrableOn W (Ioi 1)) (hWi' : IntegrableOn W' (Ioi 1))
    (S : Finset ℕ) (b : ℕ → ℝ) :
    |∫ v in Ioi (1 : ℝ), W v * (realPhaseCombination S b v * realPhaseCombination S b (r * v))| ≤
      ((2 * ∑ n ∈ S, |b n|) * (∫ v in Ioi (1 : ℝ), |W' v|) +
        realPhaseLipschitz S b * (∫ v in Ioi (1 : ℝ), |W v|)) *
      ((12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)) / r) := by
  set p := realPhaseCombination S b
  set Bmax := 2 * ∑ n ∈ S, |b n|
  set Lp := realPhaseLipschitz S b
  set P := 12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)
  have hBmax : 0 ≤ Bmax := mul_nonneg zero_le_two (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hLp : 0 ≤ Lp := realPhaseLipschitz_nonneg S b
  have hG_bd : ∀ y, |criticalFactorialPhasePrimitive S b y / r| ≤ P / r := fun y => by
    rw [abs_div, abs_of_pos hr]
    exact div_le_div_of_nonneg_right (criticalFactorialPhasePrimitive_bound S b y) hr.le
  have hG_cont : ContinuousOn (fun v => criticalFactorialPhasePrimitive S b (r * v) / r) (Ioi 1) :=
    fun v hv => (hasDerivAt_dilated_phasePrimitive S b hr
      (lt_trans one_pos hv)).continuousAt.continuousWithinAt
  have hmaj : IntegrableOn (fun v => (Bmax * |W' v| + Lp * |W v|) * (P / r)) (Ioi 1) :=
    ((hWi'.abs.const_mul Bmax).add (hWi.abs.const_mul Lp)).mul_const (P / r)
  have hint_abs : IntegrableOn
      (fun v => |(p v * W' v + deriv p v * W v) *
        (criticalFactorialPhasePrimitive S b (r * v) / r)|) (Ioi 1) := by
    refine hmaj.mono' ?_ ?_
    · have hm_p : AEStronglyMeasurable p (volume.restrict (Ioi 1)) :=
        (continuous_realPhaseCombination S b).aestronglyMeasurable
      have hm_dp : AEStronglyMeasurable (deriv p) (volume.restrict (Ioi 1)) :=
        (measurable_deriv p).aestronglyMeasurable
      exact (((hm_p.mul hWi'.aestronglyMeasurable).add
        (hm_dp.mul hWi.aestronglyMeasurable)).mul
        (hG_cont.aestronglyMeasurable measurableSet_Ioi)).norm
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
      rw [Real.norm_eq_abs, abs_abs, abs_mul]
      have h1 : |p v * W' v + deriv p v * W v| ≤ Bmax * |W' v| + Lp * |W v| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (abs_realPhaseCombination_le_two_mul S b v)
            (abs_nonneg _)
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (abs_deriv_realPhaseCombination_le S b v)
            (abs_nonneg _)
      exact mul_le_mul h1 (hG_bd (r * v)) (abs_nonneg _) (by positivity)
  rw [integral_Ioi_realLag_phase_ibp hr hW hW' hW1 hWt hWi hWi' S b, abs_neg]
  calc |∫ v in Ioi (1 : ℝ),
        (p v * W' v + deriv p v * W v) * (criticalFactorialPhasePrimitive S b (r * v) / r)|
      ≤ ∫ v in Ioi (1 : ℝ),
          |(p v * W' v + deriv p v * W v) *
            (criticalFactorialPhasePrimitive S b (r * v) / r)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ v in Ioi (1 : ℝ), (Bmax * |W' v| + Lp * |W v|) * (P / r) := by
        refine setIntegral_mono_on hint_abs hmaj measurableSet_Ioi fun v _ => ?_
        rw [abs_mul]
        have h1 : |p v * W' v + deriv p v * W v| ≤ Bmax * |W' v| + Lp * |W v| := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (abs_realPhaseCombination_le_two_mul S b v)
              (abs_nonneg _)
          · rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (abs_deriv_realPhaseCombination_le S b v)
              (abs_nonneg _)
        exact mul_le_mul h1 (hG_bd (r * v)) (abs_nonneg _) (by positivity)
    _ = (Bmax * (∫ v in Ioi (1 : ℝ), |W' v|) + Lp * (∫ v in Ioi (1 : ℝ), |W v|)) * (P / r) := by
        rw [integral_mul_const, integral_add (hWi'.abs.const_mul Bmax) (hWi.abs.const_mul Lp),
          integral_const_mul, integral_const_mul]

/-! ## Section 2: Clock-Change Identities and Uniform `O(e^{-3t/2})` Correlation Decay -/

/-- Finite-endpoint clock change `∫_{-log T}^0 e^x H(e^{-x}) dx = ∫_1^T H(v) / v² dv` (`1 ≤ T`). -/
theorem integral_Icc_neg_log_zero_exp_mul_comp_exp_neg {T : ℝ} (hT : 1 ≤ T) (H : ℝ → ℝ) :
    (∫ x in Icc (-Real.log T) 0, Real.exp x * H (Real.exp (-x))) =
      ∫ v in (1 : ℝ)..T, H v / v ^ 2 := by
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT
  have hpt : (Icc (-Real.log T) (0 : ℝ)).indicator (fun x => Real.exp x * H (Real.exp (-x))) =
      (Iic (0 : ℝ)).indicator
        (fun x => Real.exp x * (Iic T).indicator H (Real.exp (-x))) := by
    funext x
    by_cases hx0 : x ≤ 0
    · rw [Set.indicator_of_mem (show x ∈ Iic 0 from hx0)]
      have hiff : -Real.log T ≤ x ↔ Real.exp (-x) ≤ T := by
        rw [← Real.exp_log hT0, Real.exp_le_exp, Real.log_exp]
        constructor <;> intro h <;> linarith
      by_cases hxT : -Real.log T ≤ x
      · have hm1 : x ∈ Icc (-Real.log T) (0 : ℝ) := ⟨hxT, hx0⟩
        have hm2 : Real.exp (-x) ∈ Iic T := hiff.mp hxT
        rw [Set.indicator_of_mem hm1, Set.indicator_of_mem hm2]
      · have hm1 : x ∉ Icc (-Real.log T) (0 : ℝ) := fun hm => hxT hm.1
        have hm2 : Real.exp (-x) ∉ Iic T := fun hm => hxT (hiff.mpr hm)
        rw [Set.indicator_of_notMem hm1, Set.indicator_of_notMem hm2, mul_zero]
    · have hm1 : x ∉ Icc (-Real.log T) (0 : ℝ) := fun hm => hx0 hm.2
      have hm2 : x ∉ Iic (0 : ℝ) := hx0
      rw [Set.indicator_of_notMem hm1, Set.indicator_of_notMem hm2]
  rw [← integral_indicator measurableSet_Icc, hpt, integral_indicator measurableSet_Iic,
    integral_Iic_zero_exp_mul_comp_exp_neg ((Iic T).indicator H)]
  have hdiv : (fun v => (Iic T).indicator H v / v ^ 2) =
      (Iic T).indicator (fun v => H v / v ^ 2) := by
    funext v; by_cases hv : v ≤ T <;> simp [Set.indicator, hv]
  rw [hdiv, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic,
    intervalIntegral.integral_of_le hT]

/-- Finite-endpoint clock change `∫_{-log T}^0 K(e^{-x}) dx = ∫_1^T K(v) / v dv` (`1 ≤ T`). -/
theorem integral_Icc_neg_log_zero_comp_exp_neg {T : ℝ} (hT : 1 ≤ T) (K : ℝ → ℝ) :
    (∫ x in Icc (-Real.log T) 0, K (Real.exp (-x))) =
      ∫ v in (1 : ℝ)..T, K v / v := by
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT
  have hpt : (Icc (-Real.log T) (0 : ℝ)).indicator (fun x => K (Real.exp (-x))) =
      (Iic (0 : ℝ)).indicator (fun x => (Iic T).indicator K (Real.exp (-x))) := by
    funext x
    by_cases hx0 : x ≤ 0
    · rw [Set.indicator_of_mem (show x ∈ Iic 0 from hx0)]
      have hiff : -Real.log T ≤ x ↔ Real.exp (-x) ≤ T := by
        rw [← Real.exp_log hT0, Real.exp_le_exp, Real.log_exp]
        constructor <;> intro h <;> linarith
      by_cases hxT : -Real.log T ≤ x
      · have hm1 : x ∈ Icc (-Real.log T) (0 : ℝ) := ⟨hxT, hx0⟩
        have hm2 : Real.exp (-x) ∈ Iic T := hiff.mp hxT
        rw [Set.indicator_of_mem hm1, Set.indicator_of_mem hm2]
      · have hm1 : x ∉ Icc (-Real.log T) (0 : ℝ) := fun hm => hxT hm.1
        have hm2 : Real.exp (-x) ∉ Iic T := fun hm => hxT (hiff.mpr hm)
        rw [Set.indicator_of_notMem hm1, Set.indicator_of_notMem hm2]
    · have hm1 : x ∉ Icc (-Real.log T) (0 : ℝ) := fun hm => hx0 hm.2
      have hm2 : x ∉ Iic (0 : ℝ) := hx0
      rw [Set.indicator_of_notMem hm1, Set.indicator_of_notMem hm2]
  rw [← integral_indicator measurableSet_Icc, hpt, integral_indicator measurableSet_Iic,
    integral_Iic_zero_comp_exp_neg ((Iic T).indicator K)]
  have hdiv : (fun v => (Iic T).indicator K v / v) =
      (Iic T).indicator (fun v => K v / v) := by
    funext v; by_cases hv : v ≤ T <;> simp [Set.indicator, hv]
  rw [hdiv, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic,
    intervalIntegral.integral_of_le hT]

/-- Closed form of `criticalCollaredSource S b` without the indicator at `0`. -/
theorem criticalCollaredSource_eq (S : Finset ℕ) (b : ℕ → ℝ) (x : ℝ) :
    criticalCollaredSource S b x =
      Real.smoothTransition (Real.exp (-x) - 1) *
        (Real.exp (x / 2) * realPhaseCombination S b (Real.exp (-x))) := by
  unfold criticalCollaredSource criticalFactorialSource
  by_cases hx : x ≤ 0
  · rw [Set.indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx), factorialPhaseCombination_re_eq]
  · rw [Set.indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx),
      Real.smoothTransition.zero_of_nonpos (by
        have := Real.exp_le_exp.mpr (show -x ≤ 0 by simp only [not_le] at hx; linarith)
        rw [Real.exp_zero] at this; linarith)]
    simp

theorem continuous_criticalCollaredSource (S : Finset ℕ) (b : ℕ → ℝ) :
    Continuous (criticalCollaredSource S b) := by
  have he : Continuous fun x : ℝ => Real.exp (-x) := Real.continuous_exp.comp continuous_neg
  rw [show criticalCollaredSource S b = _ from funext (criticalCollaredSource_eq S b)]
  exact (Real.smoothTransition.continuous.comp (he.sub continuous_const)).mul
    ((Real.continuous_exp.comp (continuous_id.div_const 2)).mul
      ((continuous_realPhaseCombination S b).comp he))

theorem memLp_criticalCollaredSource (S : Finset ℕ) (b : ℕ → ℝ) :
    MemLp (criticalCollaredSource S b) 2 volume := by
  have hgc := admissibleSource_criticalCollaredSource S b
  have hint : Integrable fun y => criticalCollaredSource S b y ^ 2 := by
    have := (memLp_two_iff_integrable_sq_norm hgc.1.aestronglyMeasurable).mp hgc.2
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using this
  exact (memLp_two_iff_integrable_sq
    (continuous_criticalCollaredSource S b).aestronglyMeasurable).mpr hint

theorem memLp_criticalTruncatedSource (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) :
    MemLp (criticalTruncatedSource V S b) 2 volume := by
  have hg := admissibleSource_criticalTruncatedSource V S b
  have hint : Integrable fun y => criticalTruncatedSource V S b y ^ 2 := by
    have := (memLp_two_iff_integrable_sq_norm hg.1.aestronglyMeasurable).mp hg.2
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using this
  exact (memLp_two_iff_integrable_sq
    (continuous_criticalTruncatedSource V S b).aestronglyMeasurable).mpr hint

/-- **Sharp `L²` Truncation** `g_V = 1_{[-log V, 0]} g_c` of the collared critical source,
used to regularize the polar normalization at finite truncation `V ≥ 1`. -/
def criticalCollaredSharpTruncation (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (x : ℝ) : ℝ :=
  (Icc (-Real.log V) 0).indicator (criticalCollaredSource S b) x

theorem memLp_criticalCollaredSharpTruncation (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) :
    MemLp (criticalCollaredSharpTruncation V S b) 2 volume :=
  (memLp_criticalCollaredSource S b).indicator measurableSet_Icc

theorem hasCompactSupport_criticalCollaredSharpTruncation (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) :
    HasCompactSupport (criticalCollaredSharpTruncation V S b) :=
  HasCompactSupport.intro isCompact_Icc fun _ hx => Set.indicator_of_notMem hx _

private theorem abs_criticalCollarWeight_le_one (v : ℝ) : |criticalCollarWeight v| ≤ 1 := by
  rcases le_or_gt v 1 with hv | hv
  · rw [criticalCollarWeight_eq_zero hv, abs_zero]; exact zero_le_one
  · rw [criticalCollarWeight, abs_div, abs_of_nonneg (Real.smoothTransition.nonneg _),
      abs_of_pos (sq_pos_of_pos (lt_trans one_pos hv))]
    exact (div_le_one (sq_pos_of_pos (lt_trans one_pos hv))).mpr
      ((Real.smoothTransition.le_one _).trans (by nlinarith))

/-- **Real-Lag Correlation Identity for `criticalCollaredSource`.**
For every real lag `t ≥ log 2`, the collar of the shifted copy is identically `1` and
`autocorr (criticalCollaredSource S b) t = e^{-t/2} ∫_{v>1} ψ(v) B_b(v) B_b(e^t v) dv`. -/
theorem autocorr_criticalCollaredSource_eq_realLag (S : Finset ℕ) (b : ℕ → ℝ)
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    autocorr (criticalCollaredSource S b) t =
      Real.exp (-(t / 2)) * ∫ v in Ioi (1 : ℝ), criticalCollarWeight v *
        (realPhaseCombination S b v * realPhaseCombination S b (Real.exp t * v)) := by
  set R := realPhaseCombination S b
  set r := Real.exp t
  have hr2 : 2 ≤ r := by
    have := Real.exp_le_exp.mpr ht
    rwa [Real.exp_log two_pos] at this
  have hpt : ∀ x, criticalCollaredSource S b x * criticalCollaredSource S b (x - t) =
      (Iic (0 : ℝ)).indicator (fun x => Real.exp (-(t / 2)) * (Real.exp x *
        (Real.smoothTransition (Real.exp (-x) - 1) *
          (R (Real.exp (-x)) * R (r * Real.exp (-x)))))) x := by
    intro x
    by_cases hx : x ≤ 0
    · rw [Set.indicator_of_mem (show x ∈ Iic 0 from hx)]
      have hexp : Real.exp (-(x - t)) = r * Real.exp (-x) := by
        dsimp only [r]; rw [show -(x - t) = t + -x by ring, Real.exp_add]
      have he1 : 1 ≤ Real.exp (-x) := Real.one_le_exp (by linarith)
      have hc : Real.smoothTransition (Real.exp (-(x - t)) - 1) = 1 := by
        rw [hexp]; exact Real.smoothTransition.one_of_one_le (by nlinarith)
      have hexp_half : Real.exp (x / 2) * Real.exp ((x - t) / 2) =
          Real.exp (-(t / 2)) * Real.exp x := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      rw [criticalCollaredSource_eq, criticalCollaredSource_eq, hc, hexp]
      calc (Real.smoothTransition (Real.exp (-x) - 1) * (Real.exp (x / 2) * R (Real.exp (-x)))) *
            (1 * (Real.exp ((x - t) / 2) * R (r * Real.exp (-x))))
          = (Real.exp (x / 2) * Real.exp ((x - t) / 2)) *
              (Real.smoothTransition (Real.exp (-x) - 1) *
                (R (Real.exp (-x)) * R (r * Real.exp (-x)))) := by ring
        _ = _ := by rw [hexp_half]; ring
    · rw [Set.indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx), criticalCollaredSource_eq S b x,
        Real.smoothTransition.zero_of_nonpos (by
          have := Real.exp_le_exp.mpr (show -x ≤ 0 by simp only [not_le] at hx; linarith)
          rw [Real.exp_zero] at this; linarith)]
      ring
  rw [← autocorr_neg]
  unfold autocorr
  simp only [← sub_eq_add_neg]
  simp_rw [hpt]
  rw [integral_indicator measurableSet_Iic, integral_const_mul,
    integral_Iic_zero_exp_mul_comp_exp_neg
      (fun v => Real.smoothTransition (v - 1) * (R v * R (r * v)))]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  simp only [criticalCollarWeight, r]
  ring

/-- Beyond lag `log V`, the sharp truncation `criticalCollaredSharpTruncation V S b` (`1 ≤ V`) has
identically vanishing autocorrelation. -/
theorem autocorr_criticalCollaredSharpTruncation_eq_zero_of_log_le {V : ℝ} (hV : 1 ≤ V)
    (S : Finset ℕ) (b : ℕ → ℝ) {t : ℝ} (ht : Real.log V ≤ t) :
    autocorr (criticalCollaredSharpTruncation V S b) t = 0 := by
  rw [← autocorr_neg]
  unfold autocorr
  have hzero : ∀ x, criticalCollaredSharpTruncation V S b x *
      criticalCollaredSharpTruncation V S b (x + -t) = 0 := by
    intro x
    by_cases hx : x ∈ Icc (-Real.log V) 0
    · rcases hx.2.eq_or_lt with rfl | hx_neg
      · have h0 : criticalCollaredSharpTruncation V S b 0 = 0 := by
          simp [criticalCollaredSharpTruncation, criticalCollaredSource_eq,
            Real.smoothTransition.zero_of_nonpos]
        rw [h0, zero_mul]
      · have hxt : x + -t ∉ Icc (-Real.log V) 0 := fun hm => by linarith [hm.1]
        simp only [criticalCollaredSharpTruncation, Set.indicator_of_notMem hxt, mul_zero]
    · simp only [criticalCollaredSharpTruncation, Set.indicator_of_notMem hx, zero_mul]
  simp only [hzero, integral_zero]

/-- **Real-Lag Correlation and Moving-Boundary IBP Identity for `criticalCollaredSharpTruncation`.**
For `1 ≤ V` and `log 2 ≤ t` with `e^t ≤ V`, the sharp-truncation autocorrelation equals the
finite-horizon integral on `[1, V / e^t]`, which integrates by parts to retain the exact moving
upper boundary `(ψ(V / e^t) B_b(V / e^t)) (G_b(V) / e^t)`. -/
theorem autocorr_criticalCollaredSharpTruncation_eq_ibp {V : ℝ} (S : Finset ℕ) (b : ℕ → ℝ)
    {t : ℝ} (ht : Real.log 2 ≤ t) (htV : Real.exp t ≤ V) :
    autocorr (criticalCollaredSharpTruncation V S b) t =
      Real.exp (-(t / 2)) *
        ((criticalCollarWeight (V / Real.exp t) *
            realPhaseCombination S b (V / Real.exp t)) *
          (criticalFactorialPhasePrimitive S b V / Real.exp t) -
        ∫ v in (1 : ℝ)..(V / Real.exp t),
          (realPhaseCombination S b v * deriv criticalCollarWeight v +
            deriv (realPhaseCombination S b) v * criticalCollarWeight v) *
            (criticalFactorialPhasePrimitive S b (Real.exp t * v) / Real.exp t)) := by
  set R := realPhaseCombination S b
  set r := Real.exp t
  have hr0 : 0 < r := Real.exp_pos t
  have hr2 : 2 ≤ r := by
    have := Real.exp_le_exp.mpr ht
    rwa [Real.exp_log two_pos] at this
  have hV1 : 1 ≤ V := by linarith
  have hV0 : 0 < V := by linarith
  set T := V / r
  have hT1 : 1 ≤ T := (one_le_div hr0).mpr htV
  have hlogT : Real.log T = Real.log V - t := by
    dsimp only [T, r]; rw [Real.log_div hV0.ne' hr0.ne', Real.log_exp]
  have hpt : ∀ x, criticalCollaredSharpTruncation V S b x *
      criticalCollaredSharpTruncation V S b (x - t) =
      (Icc (-Real.log T) (0 : ℝ)).indicator (fun x => Real.exp (-(t / 2)) * (Real.exp x *
        (Real.smoothTransition (Real.exp (-x) - 1) *
          (R (Real.exp (-x)) * R (r * Real.exp (-x)))))) x := by
    intro x
    have ht_pos : 0 < t := lt_of_lt_of_le (Real.log_pos one_lt_two) ht
    by_cases hxT : x ∈ Icc (-Real.log T) 0
    · have hxV : x ∈ Icc (-Real.log V) 0 := ⟨by linarith [hxT.1], hxT.2⟩
      have hxtV : x - t ∈ Icc (-Real.log V) 0 := ⟨by linarith [hxT.1], by linarith [hxT.2]⟩
      rw [Set.indicator_of_mem hxT, criticalCollaredSharpTruncation,
        criticalCollaredSharpTruncation, Set.indicator_of_mem hxV, Set.indicator_of_mem hxtV]
      have hexp : Real.exp (-(x - t)) = r * Real.exp (-x) := by
        dsimp only [r]; rw [show -(x - t) = t + -x by ring, Real.exp_add]
      have he1 : 1 ≤ Real.exp (-x) := Real.one_le_exp (by linarith [hxT.2])
      have hc : Real.smoothTransition (Real.exp (-(x - t)) - 1) = 1 := by
        rw [hexp]; exact Real.smoothTransition.one_of_one_le (by nlinarith)
      have hexp_half : Real.exp (x / 2) * Real.exp ((x - t) / 2) =
          Real.exp (-(t / 2)) * Real.exp x := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      rw [criticalCollaredSource_eq, criticalCollaredSource_eq, hc, hexp]
      calc (Real.smoothTransition (Real.exp (-x) - 1) * (Real.exp (x / 2) * R (Real.exp (-x)))) *
            (1 * (Real.exp ((x - t) / 2) * R (r * Real.exp (-x))))
          = (Real.exp (x / 2) * Real.exp ((x - t) / 2)) *
              (Real.smoothTransition (Real.exp (-x) - 1) *
                (R (Real.exp (-x)) * R (r * Real.exp (-x)))) := by ring
        _ = _ := by rw [hexp_half]; ring
    · rw [Set.indicator_of_notMem hxT]
      by_cases hxV : x ∈ Icc (-Real.log V) 0
      · have hxtV : x - t ∉ Icc (-Real.log V) 0 := fun hm =>
          hxT ⟨by linarith [hm.1], hxV.2⟩
        rw [criticalCollaredSharpTruncation, criticalCollaredSharpTruncation,
          Set.indicator_of_notMem hxtV, mul_zero]
      · rw [criticalCollaredSharpTruncation, Set.indicator_of_notMem hxV, zero_mul]
  have hcorr_eq : autocorr (criticalCollaredSharpTruncation V S b) t =
      Real.exp (-(t / 2)) * ∫ v in (1 : ℝ)..T, criticalCollarWeight v * (R v * R (r * v)) := by
    rw [← autocorr_neg]
    unfold autocorr
    simp only [← sub_eq_add_neg]
    simp_rw [hpt]
    rw [integral_indicator measurableSet_Icc, integral_const_mul,
      integral_Icc_neg_log_zero_exp_mul_comp_exp_neg hT1
        (fun v => Real.smoothTransition (v - 1) * (R v * R (r * v)))]
    congr 1
    refine intervalIntegral.integral_congr fun v _ => ?_
    simp only [criticalCollarWeight]
    ring
  rw [hcorr_eq, intervalIntegral_realLag_phase_ibp hT1 hr0
    (fun v _ => hasDerivAt_criticalCollarWeight v)
    contDiff_deriv_criticalCollarWeight.continuous.continuousOn
    (criticalCollarWeight_eq_zero le_rfl) S b]
  have hrT : r * T = V := mul_div_cancel₀ V hr0.ne'
  rw [hrT]

/-- **Real-Lag Correlation Identity for `criticalTruncatedSource`.** -/
theorem autocorr_criticalTruncatedSource_eq_realLag {V : ℝ} (hV : 0 < V)
    (S : Finset ℕ) (b : ℕ → ℝ) {t : ℝ} (ht : Real.log 2 ≤ t) :
    autocorr (criticalTruncatedSource V S b) t =
      Real.exp (-(t / 2)) * ∫ v in Ioi (1 : ℝ),
        criticalTruncatedWeight (Real.exp t / V) v *
          (realPhaseCombination S b v * realPhaseCombination S b (Real.exp t * v)) := by
  set R := realPhaseCombination S b
  set r := Real.exp t
  have hr2 : 2 ≤ r := by
    have := Real.exp_le_exp.mpr ht
    rwa [Real.exp_log two_pos] at this
  have hpt : ∀ x, criticalTruncatedSource V S b x * criticalTruncatedSource V S b (x - t) =
      (Iic (0 : ℝ)).indicator (fun x => Real.exp (-(t / 2)) * (Real.exp x *
        (Real.smoothTransition (Real.exp (-x) - 1) * criticalUpperCutoff (r * Real.exp (-x) / V) *
          (R (Real.exp (-x)) * R (r * Real.exp (-x)))))) x := by
    intro x
    by_cases hx : x ≤ 0
    · rw [Set.indicator_of_mem (show x ∈ Iic 0 from hx)]
      have hexp : Real.exp (-(x - t)) = r * Real.exp (-x) := by
        dsimp only [r]; rw [show -(x - t) = t + -x by ring, Real.exp_add]
      have he1 : 1 ≤ Real.exp (-x) := Real.one_le_exp (by linarith)
      have hc : Real.smoothTransition (Real.exp (-(x - t)) - 1) = 1 := by
        rw [hexp]; exact Real.smoothTransition.one_of_one_le (by nlinarith)
      have hcut : criticalUpperCutoff (Real.exp (-x) / V) *
          criticalUpperCutoff (r * Real.exp (-x) / V) =
          criticalUpperCutoff (r * Real.exp (-x) / V) := by
        rcases le_or_gt 2 (r * Real.exp (-x) / V) with h | h
        · rw [criticalUpperCutoff_eq_zero h, mul_zero]
        · have : Real.exp (-x) / V ≤ 1 := by
            rw [div_le_one hV]
            have h' : r * Real.exp (-x) < 2 * V := by rwa [div_lt_iff₀ hV] at h
            nlinarith
          rw [criticalUpperCutoff_eq_one this, one_mul]
      have hexp_half : Real.exp (x / 2) * Real.exp ((x - t) / 2) =
          Real.exp (-(t / 2)) * Real.exp x := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      rw [criticalTruncatedSource_eq, criticalTruncatedSource_eq, hc, hexp]
      calc (criticalUpperCutoff (Real.exp (-x) / V) *
              (Real.smoothTransition (Real.exp (-x) - 1) * (Real.exp (x / 2) * R (Real.exp (-x))))) *
            (criticalUpperCutoff (r * Real.exp (-x) / V) *
              (1 * (Real.exp ((x - t) / 2) * R (r * Real.exp (-x)))))
          = (criticalUpperCutoff (Real.exp (-x) / V) *
              criticalUpperCutoff (r * Real.exp (-x) / V)) *
            ((Real.exp (x / 2) * Real.exp ((x - t) / 2)) *
              (Real.smoothTransition (Real.exp (-x) - 1) *
                (R (Real.exp (-x)) * R (r * Real.exp (-x))))) := by ring
        _ = _ := by rw [hcut, hexp_half]; ring
    · rw [Set.indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx),
        criticalTruncatedSource_eq V S b x,
        Real.smoothTransition.zero_of_nonpos (by
          have := Real.exp_le_exp.mpr (show -x ≤ 0 by simp only [not_le] at hx; linarith)
          rw [Real.exp_zero] at this; linarith)]
      ring
  rw [← autocorr_neg]
  unfold autocorr
  simp only [← sub_eq_add_neg]
  simp_rw [hpt]
  rw [integral_indicator measurableSet_Iic, integral_const_mul,
    integral_Iic_zero_exp_mul_comp_exp_neg (fun v => Real.smoothTransition (v - 1) *
      criticalUpperCutoff (r * v / V) * (R v * R (r * v)))]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  simp only [criticalTruncatedWeight, criticalCollarWeight, r]
  rw [show Real.exp t / V * v = Real.exp t * v / V by ring]
  ring

/-- Universal `V`-independent correlation decay envelope for `criticalCollaredSource S b`,
`criticalCollaredSharpTruncation V S b` (`V ≥ 1`), and `criticalTruncatedSource V S b` (`V > 0`). -/
def criticalCollaredDecayConstant (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  max (criticalCollarMassUpper * (∑ n ∈ S, b n ^ 2) * Real.exp ((3 / 2 : ℝ) * Real.log 2))
    (((2 * ∑ n ∈ S, |b n|) * (1 + criticalTruncatedReadoutConstant) +
      realPhaseLipschitz S b * criticalCollarMass) *
      (12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)))

private theorem autocorr_le_short_lag {f : ℝ → ℝ} (hf : MemLp f 2 volume) {U : ℝ}
    (h0 : autocorr f 0 ≤ U) {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < Real.log 2) :
    |autocorr f t| ≤ U * Real.exp ((3 / 2 : ℝ) * Real.log 2) * Real.exp (-(3 / 2 : ℝ) * t) := by
  have h1 : |autocorr f t| ≤ autocorr f 0 := abs_autocorr_le_zero_of_memLp hf t
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (h1.trans h0)
  have hexp1 : 1 ≤ Real.exp ((3 / 2 : ℝ) * Real.log 2) * Real.exp (-(3 / 2 : ℝ) * t) := by
    rw [← Real.exp_add]
    exact Real.one_le_exp (by linarith)
  calc |autocorr f t| ≤ U * 1 := by linarith
    _ ≤ U * (Real.exp ((3 / 2 : ℝ) * Real.log 2) * Real.exp (-(3 / 2 : ℝ) * t)) :=
        mul_le_mul_of_nonneg_left hexp1 hU0
    _ = U * Real.exp ((3 / 2 : ℝ) * Real.log 2) * Real.exp (-(3 / 2 : ℝ) * t) := by ring

private theorem exp_half_mul_div_exp_eq (t A B : ℝ) :
    Real.exp (-(t / 2)) * (A * (B / Real.exp t)) = (A * B) * Real.exp (-(3 / 2 : ℝ) * t) := by
  rw [div_eq_mul_inv B (Real.exp t), ← Real.exp_neg,
    show Real.exp (-(t / 2)) * (A * (B * Real.exp (-t))) =
      (A * B) * (Real.exp (-(t / 2)) * Real.exp (-t)) by ring, ← Real.exp_add]
  congr 2
  ring

/-- **Supercritical `O(e^{-3t/2})` Correlation Decay for `criticalCollaredSource`.** -/
theorem abs_autocorr_criticalCollaredSource_le (S : Finset ℕ) (b : ℕ → ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    |autocorr (criticalCollaredSource S b) t| ≤
      criticalCollaredDecayConstant S b * Real.exp (-(3 / 2 : ℝ) * t) := by
  rcases lt_or_ge t (Real.log 2) with ht2 | ht2
  · have h0 : autocorr (criticalCollaredSource S b) 0 ≤
        criticalCollarMassUpper * ∑ n ∈ S, b n ^ 2 := by
      rw [← sourceAutocorrelation_eq_autocorr']
      exact sourceAutocorrelation_criticalCollaredSource_zero_le S b
    exact (autocorr_le_short_lag (memLp_criticalCollaredSource S b) h0 ht ht2).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · rw [autocorr_criticalCollaredSource_eq_realLag S b ht2, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    have hibp := abs_integral_Ioi_realLag_phase_le (Real.exp_pos t)
      (fun v _ => hasDerivAt_criticalCollarWeight v)
      contDiff_deriv_criticalCollarWeight.continuous.continuousOn
      (criticalCollarWeight_eq_zero le_rfl) tendsto_criticalCollarWeight_atTop
      integrableOn_criticalCollarWeight integrableOn_deriv_criticalCollarWeight S b
    have hle_readout : (∫ v in Ioi (1 : ℝ), |deriv criticalCollarWeight v|) ≤
        1 + criticalTruncatedReadoutConstant := by
      unfold criticalTruncatedReadoutConstant
      have h1 := smoothTransitionSlope_nonneg
      have h2 : 0 ≤ criticalCollarMass := integral_nonneg fun _ => abs_nonneg _
      linarith [mul_nonneg (mul_nonneg zero_le_two h1) h2]
    have hP : 0 ≤ 12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ) :=
      mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => by positivity)
    have hB : 0 ≤ 2 * ∑ n ∈ S, |b n| :=
      mul_nonneg zero_le_two (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    calc Real.exp (-(t / 2)) * |∫ v in Ioi (1 : ℝ), criticalCollarWeight v *
            (realPhaseCombination S b v * realPhaseCombination S b (Real.exp t * v))|
        ≤ Real.exp (-(t / 2)) * (((2 * ∑ n ∈ S, |b n|) *
              (∫ v in Ioi (1 : ℝ), |deriv criticalCollarWeight v|) +
            realPhaseLipschitz S b * criticalCollarMass) *
            ((12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)) / Real.exp t)) :=
          mul_le_mul_of_nonneg_left hibp (Real.exp_pos _).le
      _ ≤ Real.exp (-(t / 2)) * (((2 * ∑ n ∈ S, |b n|) * (1 + criticalTruncatedReadoutConstant) +
            realPhaseLipschitz S b * criticalCollarMass) *
            ((12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)) / Real.exp t)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (add_le_add (mul_le_mul_of_nonneg_left hle_readout hB) le_rfl)
            (div_nonneg hP (Real.exp_pos t).le)) (Real.exp_pos _).le
      _ = (((2 * ∑ n ∈ S, |b n|) * (1 + criticalTruncatedReadoutConstant) +
            realPhaseLipschitz S b * criticalCollarMass) *
            (12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ))) * Real.exp (-(3 / 2 : ℝ) * t) := by
          rw [exp_half_mul_div_exp_eq]
      _ ≤ criticalCollaredDecayConstant S b * Real.exp (-(3 / 2 : ℝ) * t) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- **`V`-Uniform Supercritical `O(e^{-3t/2})` Correlation Decay for `criticalCollaredSharpTruncation`.** -/
theorem abs_autocorr_criticalCollaredSharpTruncation_le {V : ℝ} (hV : 1 ≤ V)
    (S : Finset ℕ) (b : ℕ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    |autocorr (criticalCollaredSharpTruncation V S b) t| ≤
      criticalCollaredDecayConstant S b * Real.exp (-(3 / 2 : ℝ) * t) := by
  have hK0 : 0 ≤ criticalCollaredDecayConstant S b := by
    have := abs_autocorr_criticalCollaredSource_le S b le_rfl
    simpa using (abs_nonneg _).trans this
  rcases lt_or_ge t (Real.log 2) with ht2 | ht2
  · have h0 : autocorr (criticalCollaredSharpTruncation V S b) 0 ≤
        criticalCollarMassUpper * ∑ n ∈ S, b n ^ 2 := by
      have hle_gc : autocorr (criticalCollaredSharpTruncation V S b) 0 ≤
          autocorr (criticalCollaredSource S b) 0 := by
        have hgc := memLp_criticalCollaredSource S b
        have hint : Integrable fun x => criticalCollaredSource S b x ^ 2 := hgc.integrable_sq
        unfold autocorr
        simp only [add_zero, ← sq]
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) hint
          (Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ Icc (-Real.log V) 0 <;>
          simp [criticalCollaredSharpTruncation, hx, sq_nonneg]
      refine hle_gc.trans ?_
      rw [← sourceAutocorrelation_eq_autocorr']
      exact sourceAutocorrelation_criticalCollaredSource_zero_le S b
    exact (autocorr_le_short_lag (memLp_criticalCollaredSharpTruncation V S b) h0 ht ht2).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · rcases lt_or_ge (Real.exp t) V with htV | htV
    · set T := V / Real.exp t
      have hT1 : 1 ≤ T := (one_le_div (Real.exp_pos t)).mpr htV.le
      have hcorr_eq : autocorr (criticalCollaredSharpTruncation V S b) t =
          Real.exp (-(t / 2)) * ∫ v in (1 : ℝ)..T, criticalCollarWeight v *
            (realPhaseCombination S b v * realPhaseCombination S b (Real.exp t * v)) := by
        rw [autocorr_criticalCollaredSharpTruncation_eq_ibp S b ht2 htV.le,
          intervalIntegral_realLag_phase_ibp hT1 (Real.exp_pos t)
            (fun v _ => hasDerivAt_criticalCollarWeight v)
            contDiff_deriv_criticalCollarWeight.continuous.continuousOn
            (criticalCollarWeight_eq_zero le_rfl) S b,
          mul_div_cancel₀ V (Real.exp_pos t).ne']
      rw [hcorr_eq, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hibp := abs_intervalIntegral_realLag_phase_le hT1 (Real.exp_pos t)
        (fun v _ => hasDerivAt_criticalCollarWeight v)
        contDiff_deriv_criticalCollarWeight.continuous.continuousOn
        (criticalCollarWeight_eq_zero le_rfl) S b
      have hWT : |criticalCollarWeight T| ≤ 1 := abs_criticalCollarWeight_le_one T
      have hW'_int : (∫ v in (1 : ℝ)..T, |deriv criticalCollarWeight v|) ≤
          criticalTruncatedReadoutConstant := by
        rw [intervalIntegral.integral_of_le hT1]
        have hsub : (∫ v in Ioc (1 : ℝ) T, |deriv criticalCollarWeight v|) ≤
            ∫ v in Ioi (1 : ℝ), |deriv criticalCollarWeight v| :=
          setIntegral_mono_set integrableOn_deriv_criticalCollarWeight.abs
            (Eventually.of_forall fun _ => abs_nonneg _)
            (Eventually.of_forall Ioc_subset_Ioi_self)
        unfold criticalTruncatedReadoutConstant
        have h1 := smoothTransitionSlope_nonneg
        have h2 : 0 ≤ criticalCollarMass := integral_nonneg fun _ => abs_nonneg _
        linarith [mul_nonneg (mul_nonneg zero_le_two h1) h2]
      have hW_int : (∫ v in (1 : ℝ)..T, |criticalCollarWeight v|) ≤ criticalCollarMass := by
        rw [intervalIntegral.integral_of_le hT1]
        exact setIntegral_mono_set integrableOn_criticalCollarWeight.abs
          (Eventually.of_forall fun _ => abs_nonneg _)
          (Eventually.of_forall Ioc_subset_Ioi_self)
      have hB : 0 ≤ 2 * ∑ n ∈ S, |b n| :=
        mul_nonneg zero_le_two (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      have hLp : 0 ≤ realPhaseLipschitz S b := realPhaseLipschitz_nonneg S b
      have hP : 0 ≤ 12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ) :=
        mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => by positivity)
      have hsum_le : |criticalCollarWeight T| * (2 * ∑ n ∈ S, |b n|) +
          (2 * ∑ n ∈ S, |b n|) * (∫ v in (1 : ℝ)..T, |deriv criticalCollarWeight v|) +
          realPhaseLipschitz S b * (∫ v in (1 : ℝ)..T, |criticalCollarWeight v|) ≤
          (2 * ∑ n ∈ S, |b n|) * (1 + criticalTruncatedReadoutConstant) +
            realPhaseLipschitz S b * criticalCollarMass := by
        have h1 := mul_le_mul_of_nonneg_right hWT hB
        have h2 := mul_le_mul_of_nonneg_left hW'_int hB
        have h3 := mul_le_mul_of_nonneg_left hW_int hLp
        linarith
      calc Real.exp (-(t / 2)) * |∫ v in (1 : ℝ)..T, criticalCollarWeight v *
              (realPhaseCombination S b v * realPhaseCombination S b (Real.exp t * v))|
          ≤ Real.exp (-(t / 2)) * (((2 * ∑ n ∈ S, |b n|) * (1 + criticalTruncatedReadoutConstant) +
              realPhaseLipschitz S b * criticalCollarMass) *
              ((12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)) / Real.exp t)) :=
            mul_le_mul_of_nonneg_left
              (hibp.trans (mul_le_mul_of_nonneg_right hsum_le (div_nonneg hP (Real.exp_pos t).le)))
              (Real.exp_pos _).le
        _ = (((2 * ∑ n ∈ S, |b n|) * (1 + criticalTruncatedReadoutConstant) +
              realPhaseLipschitz S b * criticalCollarMass) *
              (12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ))) * Real.exp (-(3 / 2 : ℝ) * t) := by
            rw [exp_half_mul_div_exp_eq]
        _ ≤ criticalCollaredDecayConstant S b * Real.exp (-(3 / 2 : ℝ) * t) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
    · have hlogV : Real.log V ≤ t := by
        have := Real.log_le_log (lt_of_lt_of_le one_pos hV) htV
        rwa [Real.log_exp] at this
      rw [autocorr_criticalCollaredSharpTruncation_eq_zero_of_log_le hV S b hlogV, abs_zero]
      exact mul_nonneg hK0 (Real.exp_pos _).le

/-- **`V`-Uniform Supercritical `O(e^{-3t/2})` Correlation Decay for `criticalTruncatedSource`.** -/
theorem abs_autocorr_criticalTruncatedSource_le {V : ℝ} (hV : 0 < V)
    (S : Finset ℕ) (b : ℕ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    |autocorr (criticalTruncatedSource V S b) t| ≤
      criticalCollaredDecayConstant S b * Real.exp (-(3 / 2 : ℝ) * t) := by
  rcases lt_or_ge t (Real.log 2) with ht2 | ht2
  · have h0 : autocorr (criticalTruncatedSource V S b) 0 ≤
        criticalCollarMassUpper * ∑ n ∈ S, b n ^ 2 := by
      rw [← sourceAutocorrelation_eq_autocorr']
      exact sourceAutocorrelation_criticalTruncatedSource_zero_le V S b
    exact (autocorr_le_short_lag (memLp_criticalTruncatedSource V S b) h0 ht ht2).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · rw [autocorr_criticalTruncatedSource_eq_realLag hV S b ht2, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    set lam := Real.exp t / V
    have hlam : 0 ≤ lam := by positivity
    have hW'_cont : Continuous (criticalTruncatedWeightDeriv lam) := by
      unfold criticalTruncatedWeightDeriv
      have hdσ : ContDiff ℝ (⊤ : ℕ∞) (deriv Real.smoothTransition) :=
        (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2
      exact (contDiff_deriv_criticalCollarWeight.continuous.mul
        (continuous_criticalUpperCutoff.comp (continuous_const.mul continuous_id))).add
        (contDiff_criticalCollarWeight.continuous.mul (continuous_const.mul
          (hdσ.continuous.comp ((continuous_const.mul continuous_id).sub continuous_const))).neg)
    have hWt : Tendsto (criticalTruncatedWeight lam) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      exact squeeze_zero (fun _ => norm_nonneg _)
        (fun v => by rw [Real.norm_eq_abs]; exact abs_criticalTruncatedWeight_le lam v)
        tendsto_criticalCollarWeight_atTop.abs
    have hibp := abs_integral_Ioi_realLag_phase_le (Real.exp_pos t)
      (fun v _ => hasDerivAt_criticalTruncatedWeight lam v)
      hW'_cont.continuousOn
      (by rw [criticalTruncatedWeight, criticalCollarWeight_eq_zero le_rfl, zero_mul])
      hWt (integrableOn_criticalTruncatedWeight lam)
      (integrableOn_criticalTruncatedWeightDeriv hlam) S b
    have hW'_int : (∫ v in Ioi (1 : ℝ), |criticalTruncatedWeightDeriv lam v|) ≤
        1 + criticalTruncatedReadoutConstant := by
      have h1 : (∫ v in Ioi (1 : ℝ), |criticalTruncatedWeightDeriv lam v|) ≤
          criticalTruncatedReadoutConstant := by
        unfold criticalTruncatedReadoutConstant criticalCollarMass
        calc (∫ v in Ioi (1 : ℝ), |criticalTruncatedWeightDeriv lam v|)
            ≤ ∫ v in Ioi (1 : ℝ), (|deriv criticalCollarWeight v| +
                2 * smoothTransitionSlope * |criticalCollarWeight v|) :=
              setIntegral_mono_on (integrableOn_criticalTruncatedWeightDeriv hlam).abs
                (integrableOn_deriv_criticalCollarWeight.abs.add
                  (integrableOn_criticalCollarWeight.abs.const_mul _)) measurableSet_Ioi
                fun v hv => abs_criticalTruncatedWeightDeriv_le hlam (le_of_lt hv)
          _ = _ := by
              rw [integral_add integrableOn_deriv_criticalCollarWeight.abs
                (integrableOn_criticalCollarWeight.abs.const_mul _), integral_const_mul]
      linarith
    have hW_int : (∫ v in Ioi (1 : ℝ), |criticalTruncatedWeight lam v|) ≤ criticalCollarMass :=
      setIntegral_mono_on (integrableOn_criticalTruncatedWeight lam).abs
        integrableOn_criticalCollarWeight.abs measurableSet_Ioi
        fun v _ => abs_criticalTruncatedWeight_le lam v
    have hB : 0 ≤ 2 * ∑ n ∈ S, |b n| :=
      mul_nonneg zero_le_two (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    have hLp : 0 ≤ realPhaseLipschitz S b := realPhaseLipschitz_nonneg S b
    have hP : 0 ≤ 12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ) :=
      mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => by positivity)
    have hsum_le : (2 * ∑ n ∈ S, |b n|) *
          (∫ v in Ioi (1 : ℝ), |criticalTruncatedWeightDeriv lam v|) +
        realPhaseLipschitz S b * (∫ v in Ioi (1 : ℝ), |criticalTruncatedWeight lam v|) ≤
        (2 * ∑ n ∈ S, |b n|) * (1 + criticalTruncatedReadoutConstant) +
          realPhaseLipschitz S b * criticalCollarMass :=
      add_le_add (mul_le_mul_of_nonneg_left hW'_int hB) (mul_le_mul_of_nonneg_left hW_int hLp)
    calc Real.exp (-(t / 2)) * |∫ v in Ioi (1 : ℝ), criticalTruncatedWeight lam v *
            (realPhaseCombination S b v * realPhaseCombination S b (Real.exp t * v))|
        ≤ Real.exp (-(t / 2)) * (((2 * ∑ n ∈ S, |b n|) * (1 + criticalTruncatedReadoutConstant) +
            realPhaseLipschitz S b * criticalCollarMass) *
            ((12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)) / Real.exp t)) :=
          mul_le_mul_of_nonneg_left
            (hibp.trans (mul_le_mul_of_nonneg_right hsum_le (div_nonneg hP (Real.exp_pos t).le)))
            (Real.exp_pos _).le
      _ = (((2 * ∑ n ∈ S, |b n|) * (1 + criticalTruncatedReadoutConstant) +
            realPhaseLipschitz S b * criticalCollarMass) *
            (12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ))) * Real.exp (-(3 / 2 : ℝ) * t) := by
          rw [exp_half_mul_div_exp_eq]
      _ ≤ criticalCollaredDecayConstant S b * Real.exp (-(3 / 2 : ℝ) * t) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-! ## Section 3: Compact `L²` Polar Moment Factorization and Regularized Polar Normalization -/

private theorem integrable_exp_mul_of_measurable_compact {f₀ : ℝ → ℝ} {R c : ℝ}
    (hf₀_meas : Measurable f₀) (hf₀ : MemLp f₀ 2 volume) (hR0 : 0 ≤ R)
    (hsupp : ∀ x, x ∉ Icc (-R) R → f₀ x = 0) :
    Integrable (fun u => Real.exp (c * u) * f₀ u) := by
  set w : ℝ → ℝ := (Icc (-R) R).indicator (fun u => Real.exp (c * u))
  have hw_cont : ContinuousOn (fun u => Real.exp (c * u)) (Icc (-R) R) := by fun_prop
  obtain ⟨Cw, hCw⟩ := isCompact_Icc.exists_bound_of_continuousOn hw_cont
  have hw_lp : MemLp w 2 volume := by
    refine (memLp_indicator_const 2 measurableSet_Icc (max Cw 0)
      (Or.inr measure_Icc_lt_top.ne)).mono' ?_ ?_
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.indicator
        measurableSet_Icc).aestronglyMeasurable
    · filter_upwards with u
      by_cases hu : u ∈ Icc (-R) R
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
        exact (hCw u hu).trans (le_max_left _ _)
      · simp [w, hu]
  have hint := hw_lp.integrable_mul hf₀
  refine hint.congr (Eventually.of_forall fun u => ?_)
  by_cases hu : u ∈ Icc (-R) R
  · simp [w, hu]
  · simp [w, hu, hsupp u hu]

private theorem integral_polar_autocorr_of_measurable_compact {f₀ : ℝ → ℝ} {R : ℝ}
    (hf₀_meas : Measurable f₀) (hf₀ : MemLp f₀ 2 volume) (hR0 : 0 ≤ R)
    (hsupp : ∀ x, x ∉ Icc (-R) R → f₀ x = 0) :
    (∫ x in Ici (0 : ℝ), polarDensity x * autocorr f₀ x) =
      (∫ u, Real.exp (u / 2) * f₀ u) * (∫ u, Real.exp (-(u / 2)) * f₀ u) := by
  set p₀ : ℝ → ℝ := fun u => Real.exp (u / 2) * f₀ u
  set q₀ : ℝ → ℝ := fun v => Real.exp (-(v / 2)) * f₀ v
  have hp_meas : Measurable p₀ := (by fun_prop : Measurable fun u => Real.exp (u / 2)).mul hf₀_meas
  have hq_meas : Measurable q₀ :=
    (by fun_prop : Measurable fun v => Real.exp (-(v / 2))).mul hf₀_meas
  have hp_int : Integrable p₀ := by
    simpa only [p₀, show ∀ u : ℝ, (1 / 2 : ℝ) * u = u / 2 from fun _ => by ring] using
      integrable_exp_mul_of_measurable_compact hf₀_meas hf₀ hR0 hsupp (c := 1 / 2)
  have hq_int : Integrable q₀ := by
    simpa only [q₀, show ∀ v : ℝ, (-1 / 2 : ℝ) * v = -(v / 2) from fun _ => by ring] using
      integrable_exp_mul_of_measurable_compact hf₀_meas hf₀ hR0 hsupp (c := -1 / 2)
  set F : ℝ × ℝ → ℝ := fun z => p₀ z.1 * q₀ (z.1 + z.2)
  have hF_meas : Measurable F :=
    (hp_meas.comp measurable_fst).mul (hq_meas.comp (measurable_fst.add measurable_snd))
  have hF_int : Integrable F (volume.prod volume) := by
    rw [integrable_prod_iff hF_meas.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun u => (hq_int.comp_add_left u).const_mul (p₀ u), ?_⟩
    have hnorm_eq : (fun u => ∫ x, ‖p₀ u * q₀ (u + x)‖) =
        fun u => ‖p₀ u‖ * ∫ x, ‖q₀ x‖ := by
      funext u
      simp_rw [norm_mul]
      rw [integral_const_mul, integral_add_left_eq_self (fun y => ‖q₀ y‖) u]
    rw [hnorm_eq]
    exact hp_int.norm.mul_const _
  have hswap := integral_integral_swap hF_int
  have hrhs : (∫ u, ∫ x, F (u, x)) = (∫ u, p₀ u) * (∫ v, q₀ v) := by
    have hinner : ∀ u, (∫ x, F (u, x)) = p₀ u * (∫ v, q₀ v) := fun u => by
      dsimp only [F]
      rw [integral_const_mul, integral_add_left_eq_self q₀ u]
    simp_rw [hinner]
    rw [integral_mul_const]
  have hlhs : (∫ x, ∫ u, F (u, x)) = ∫ x, autocorr f₀ x * Real.exp (-x / 2) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have hpt : ∀ u, F (u, x) = (f₀ u * f₀ (u + x)) * Real.exp (-x / 2) := fun u => by
      dsimp only [F, p₀, q₀]
      have hexp : Real.exp (u / 2) * Real.exp (-((u + x) / 2)) = Real.exp (-x / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      calc (Real.exp (u / 2) * f₀ u) * (Real.exp (-((u + x) / 2)) * f₀ (u + x))
          = (f₀ u * f₀ (u + x)) * (Real.exp (u / 2) * Real.exp (-((u + x) / 2))) := by ring
        _ = (f₀ u * f₀ (u + x)) * Real.exp (-x / 2) := by rw [hexp]
    simp_rw [hpt]
    rw [integral_mul_const]
    rfl
  have hm : (∫ x, autocorr f₀ x * Real.exp (-x / 2)) = (∫ u, p₀ u) * (∫ v, q₀ v) := by
    rw [← hlhs, ← hswap, hrhs]
  have hp : (∫ x, autocorr f₀ x * Real.exp (x / 2)) = (∫ u, p₀ u) * (∫ v, q₀ v) := by
    rw [← integral_neg_eq_self (fun x => autocorr f₀ x * Real.exp (x / 2))]
    simpa only [autocorr_neg] using hm
  have hc_ac : Continuous (autocorr f₀) := by
    have h := continuous_autocorr_of_memLp (hf₀.toLp f₀)
    exact h.congr fun x => autocorr_congr_ae hf₀.coeFn_toLp x
  have hs_ac : HasCompactSupport (autocorr f₀) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * R)) (b := 2 * R)) fun x hx => ?_
    unfold autocorr
    have hz : ∀ u, f₀ u * f₀ (u + x) = 0 := fun u => by
      by_cases hu : u ∈ Icc (-R) R
      · have hux : u + x ∉ Icc (-R) R := fun hm =>
          hx ⟨by linarith [hu.2, hm.1], by linarith [hu.1, hm.2]⟩
        rw [hsupp (u + x) hux, mul_zero]
      · rw [hsupp u hu, zero_mul]
    simp only [hz, integral_zero]
  have hip : Integrable (fun x => autocorr f₀ x * Real.exp (x / 2)) :=
    (hc_ac.mul (by fun_prop)).integrable_of_hasCompactSupport hs_ac.mul_right
  have him : Integrable (fun x => autocorr f₀ x * Real.exp (-x / 2)) :=
    (hc_ac.mul (by fun_prop)).integrable_of_hasCompactSupport hs_ac.mul_right
  have hcosh : (∫ x, autocorr f₀ x * Real.cosh (x / 2)) = (∫ u, p₀ u) * (∫ v, q₀ v) := by
    have he : (fun x => autocorr f₀ x * Real.cosh (x / 2)) =
        fun x => (autocorr f₀ x * Real.exp (x / 2) + autocorr f₀ x * Real.exp (-x / 2)) / 2 := by
      funext x; rw [Real.cosh_eq]; simp only [neg_div]; ring
    rw [he, integral_div, integral_add hip him, hp, hm]
    ring
  have heven : (fun x => autocorr f₀ |x| * Real.cosh (|x| / 2)) =
      fun x => autocorr f₀ x * Real.cosh (x / 2) := by
    funext x
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · simp only [abs_of_nonpos hx, neg_div, Real.cosh_neg, autocorr_neg]
  have hh := integral_comp_abs (f := fun x => autocorr f₀ x * Real.cosh (x / 2))
  rw [heven] at hh
  have he : (fun x => polarDensity x * autocorr f₀ x) =
      fun x => 2 * (autocorr f₀ x * Real.cosh (x / 2)) := by
    funext x; unfold polarDensity; ring
  rw [he, integral_const_mul, integral_Ici_eq_integral_Ioi, ← hh, hcosh]

/-- **Compact `L²` Polar Moment Factorization.**
For every compactly supported `f ∈ L²(ℝ)` (including discontinuous sharp truncations),
`∫_{x ≥ 0} polarDensity x * autocorr f x = (∫ e^{u/2} f u) * (∫ e^{-u/2} f u)`. -/
theorem integral_polar_autocorr_eq_moments_of_memLp {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hfc : HasCompactSupport f) :
    (∫ x in Ici (0 : ℝ), polarDensity x * autocorr f x) =
      (∫ u, Real.exp (u / 2) * f u) * (∫ u, Real.exp (-(u / 2)) * f u) := by
  obtain ⟨R₀, hR₀⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  set R := max R₀ 0
  have hR0 : 0 ≤ R := le_max_right _ _
  have hf_out : ∀ x, x ∉ Icc (-R) R → f x = 0 := fun x hx => by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hb := hR₀ hmem
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hb
    exact hx (abs_le.mp (hb.trans (le_max_left _ _)))
  set f₀ : ℝ → ℝ := (Icc (-R) R).indicator (hf.1.aemeasurable.mk f)
  have hf₀_meas : Measurable f₀ := hf.1.aemeasurable.measurable_mk.indicator measurableSet_Icc
  have hf_ae : f =ᵐ[volume] f₀ := by
    filter_upwards [hf.1.aemeasurable.ae_eq_mk] with x hx
    by_cases hmem : x ∈ Icc (-R) R
    · simp [f₀, hmem, hx]
    · simp [f₀, hmem, hf_out x hmem]
  have hf₀_lp : MemLp f₀ 2 volume := hf.ae_eq hf_ae
  have hf₀_out : ∀ x, x ∉ Icc (-R) R → f₀ x = 0 := fun x hx => Set.indicator_of_notMem hx _
  have hac_eq : autocorr f = autocorr f₀ := funext (autocorr_congr_ae hf_ae)
  have hm1 : (∫ u, Real.exp (u / 2) * f u) = ∫ u, Real.exp (u / 2) * f₀ u :=
    integral_congr_ae (hf_ae.mono fun u hu => by rw [hu])
  have hm2 : (∫ u, Real.exp (-(u / 2)) * f u) = ∫ u, Real.exp (-(u / 2)) * f₀ u :=
    integral_congr_ae (hf_ae.mono fun u hu => by rw [hu])
  rw [hac_eq, hm1, hm2]
  exact integral_polar_autocorr_of_measurable_compact hf₀_meas hf₀_lp hR0 hf₀_out

/-- Exact finite-`V` polar moment factorization on `criticalCollaredSharpTruncation V S b` (`V ≥ 1`). -/
theorem integral_polar_autocorr_criticalCollaredSharpTruncation {V : ℝ} (hV : 1 ≤ V)
    (S : Finset ℕ) (b : ℕ → ℝ) :
    (∫ x in Ici (0 : ℝ), polarDensity x * autocorr (criticalCollaredSharpTruncation V S b) x) =
      (∫ v in (1 : ℝ)..V, criticalCollarWeight v *
        (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re) *
      (∫ v in (1 : ℝ)..V, criticalCollarEndpointWeight v *
        (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re) := by
  rw [integral_polar_autocorr_eq_moments_of_memLp
    (memLp_criticalCollaredSharpTruncation V S b)
    (hasCompactSupport_criticalCollaredSharpTruncation V S b)]
  set F : ℝ → ℝ := fun v => (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re
  have h1 : (∫ u, Real.exp (u / 2) * criticalCollaredSharpTruncation V S b u) =
      ∫ v in (1 : ℝ)..V, criticalCollarWeight v * F v := by
    have hpt : (fun u => Real.exp (u / 2) * criticalCollaredSharpTruncation V S b u) =
        (Icc (-Real.log V) 0).indicator (fun u => Real.exp u *
          (Real.smoothTransition (Real.exp (-u) - 1) * F (Real.exp (-u)))) := by
      funext u
      by_cases hu : u ∈ Icc (-Real.log V) 0
      · rw [Set.indicator_of_mem hu, criticalCollaredSharpTruncation, Set.indicator_of_mem hu,
          criticalCollaredSource_eq, ← factorialPhaseCombination_re_eq]
        have hexp : Real.exp (u / 2) * Real.exp (u / 2) = Real.exp u := by
          rw [← Real.exp_add]; ring_nf
        dsimp only [F]
        calc Real.exp (u / 2) *
              (Real.smoothTransition (Real.exp (-u) - 1) * (Real.exp (u / 2) * F (Real.exp (-u))))
            = (Real.exp (u / 2) * Real.exp (u / 2)) *
                (Real.smoothTransition (Real.exp (-u) - 1) * F (Real.exp (-u))) := by ring
          _ = _ := by rw [hexp]
      · simp [criticalCollaredSharpTruncation, hu]
    rw [hpt, integral_indicator measurableSet_Icc,
      integral_Icc_neg_log_zero_exp_mul_comp_exp_neg hV
        (fun v => Real.smoothTransition (v - 1) * F v)]
    refine intervalIntegral.integral_congr fun v _ => ?_
    simp only [criticalCollarWeight]; ring
  have h2 : (∫ u, Real.exp (-(u / 2)) * criticalCollaredSharpTruncation V S b u) =
      ∫ v in (1 : ℝ)..V, criticalCollarEndpointWeight v * F v := by
    have hpt : (fun u => Real.exp (-(u / 2)) * criticalCollaredSharpTruncation V S b u) =
        (Icc (-Real.log V) 0).indicator
          (fun u => Real.smoothTransition (Real.exp (-u) - 1) * F (Real.exp (-u))) := by
      funext u
      by_cases hu : u ∈ Icc (-Real.log V) 0
      · rw [Set.indicator_of_mem hu, criticalCollaredSharpTruncation, Set.indicator_of_mem hu,
          criticalCollaredSource_eq, ← factorialPhaseCombination_re_eq]
        have hexp : Real.exp (-(u / 2)) * Real.exp (u / 2) = 1 := by
          rw [← Real.exp_add]; simp
        dsimp only [F]
        calc Real.exp (-(u / 2)) *
              (Real.smoothTransition (Real.exp (-u) - 1) * (Real.exp (u / 2) * F (Real.exp (-u))))
            = (Real.exp (-(u / 2)) * Real.exp (u / 2)) *
                (Real.smoothTransition (Real.exp (-u) - 1) * F (Real.exp (-u))) := by ring
          _ = _ := by rw [hexp]; ring
      · simp [criticalCollaredSharpTruncation, hu]
    rw [hpt, integral_indicator measurableSet_Icc,
      integral_Icc_neg_log_zero_comp_exp_neg hV
        (fun v => Real.smoothTransition (v - 1) * F v)]
    refine intervalIntegral.integral_congr fun v _ => ?_
    simp only [criticalCollarEndpointWeight]; ring
  rw [h1, h2]

private theorem tendsto_sharpTruncation_toLp (S : Finset ℕ) (b : ℕ → ℝ) :
    Tendsto (fun k : ℕ => (memLp_criticalCollaredSharpTruncation ((k + 1 : ℕ) : ℝ) S b).toLp
      (criticalCollaredSharpTruncation ((k + 1 : ℕ) : ℝ) S b))
      atTop (𝓝 ((memLp_criticalCollaredSource S b).toLp (criticalCollaredSource S b))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hgc := memLp_criticalCollaredSource S b
  have hint_sq : Integrable (fun x => criticalCollaredSource S b x ^ 2) := hgc.integrable_sq
  have hsq_tendsto : Tendsto (fun k : ℕ => ∫ x,
      (criticalCollaredSharpTruncation ((k + 1 : ℕ) : ℝ) S b x -
        criticalCollaredSource S b x) ^ 2) atTop (𝓝 0) := by
    have hlim := tendsto_integral_of_dominated_convergence
      (fun x => criticalCollaredSource S b x ^ 2)
      (fun k => ((memLp_criticalCollaredSharpTruncation ((k + 1 : ℕ) : ℝ) S b).sub
        hgc).integrable_sq.aestronglyMeasurable)
      hint_sq
      (fun k => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        by_cases hx : x ∈ Icc (-Real.log ((k + 1 : ℕ) : ℝ)) 0 <;>
          simp [criticalCollaredSharpTruncation, hx, sq_nonneg])
      (Eventually.of_forall fun x => by
        by_cases hx0 : x ≤ 0
        · refine tendsto_const_nhds.congr' ?_
          obtain ⟨K₀, hK₀⟩ := exists_nat_gt (Real.exp (-x))
          filter_upwards [eventually_ge_atTop K₀] with k hk
          have hk1 : Real.exp (-x) ≤ ((k + 1 : ℕ) : ℝ) := by
            have : (K₀ : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (show K₀ ≤ k + 1 by omega)
            exact hK₀.le.trans this
          have hlog : -Real.log ((k + 1 : ℕ) : ℝ) ≤ x := by
            have := Real.log_le_log (Real.exp_pos _) hk1
            rw [Real.log_exp] at this; linarith
          simp [criticalCollaredSharpTruncation, Set.indicator_of_mem ⟨hlog, hx0⟩]
        · refine tendsto_const_nhds.congr' (Eventually.of_forall fun k => ?_)
          have hx_pos : 0 < x := not_le.mp hx0
          have hgc0 : criticalCollaredSource S b x = 0 := by
            rw [criticalCollaredSource_eq, Real.smoothTransition.zero_of_nonpos (by
              have := Real.exp_le_exp.mpr (show -x ≤ 0 by linarith)
              rw [Real.exp_zero] at this; linarith), zero_mul]
          simp [criticalCollaredSharpTruncation, Set.indicator_of_notMem fun hm => hx0 hm.2, hgc0])
    simpa only [integral_zero] using hlim
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq_tendsto
  rw [Real.sqrt_zero] at hsqrt
  exact hsqrt.congr fun k => (norm_toLp_sub_eq_sqrt_integral_sq
    (memLp_criticalCollaredSharpTruncation ((k + 1 : ℕ) : ℝ) S b) hgc).symm

/-- **Regularized Polar Normalization for `criticalCollaredSource`.**
Although `∫ |g_c(u)| e^{-u/2} du = ∞` makes absolute two-variable Fubini unavailable, passing the
sharp `L²` truncations `g_V` (`V = k + 1 → ∞`) under the `V`-uniform `O(e^{-3t/2})` correlation
envelope identifies `∫_{x ≥ 0} polarDensity x * autocorr g_c x = R_c * E_c`. -/
theorem integral_polar_autocorr_criticalCollaredSource (S : Finset ℕ) (b : ℕ → ℝ) :
    (∫ x in Ici (0 : ℝ), polarDensity x * autocorr (criticalCollaredSource S b) x) =
      criticalCollaredPolarReadout S b * criticalCollaredPolarEndpoint S b := by
  set K := criticalCollaredDecayConstant S b
  have hK0 : 0 ≤ K := by
    have := abs_autocorr_criticalCollaredSource_le S b le_rfl
    simpa using (abs_nonneg _).trans this
  have hpolar_le : ∀ {t : ℝ}, 0 ≤ t → ∀ {A : ℝ}, 0 ≤ A →
      A * Real.exp (-(3 / 2 : ℝ) * t) * polarDensity t ≤ (2 * A) * Real.exp (-t) := by
    intro t ht A hA
    unfold polarDensity
    rw [Real.cosh_eq]
    have hexp_le : Real.exp (-(t / 2)) ≤ Real.exp (t / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have hcosh_le : 2 * ((Real.exp (t / 2) + Real.exp (-(t / 2))) / 2) ≤ 2 * Real.exp (t / 2) := by
      linarith
    calc A * Real.exp (-(3 / 2 : ℝ) * t) * (2 * ((Real.exp (t / 2) + Real.exp (-(t / 2))) / 2))
        ≤ A * Real.exp (-(3 / 2 : ℝ) * t) * (2 * Real.exp (t / 2)) :=
          mul_le_mul_of_nonneg_left hcosh_le (mul_nonneg hA (Real.exp_pos _).le)
      _ = (2 * A) * (Real.exp (-(3 / 2 : ℝ) * t) * Real.exp (t / 2)) := by ring
      _ = (2 * A) * Real.exp (-t) := by rw [← Real.exp_add]; congr 2; ring
  have hmaj : IntegrableOn (fun t => (2 * K) * Real.exp (-t)) (Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).const_mul (2 * K)
  have htoLp := tendsto_sharpTruncation_toLp S b
  have hac_pt : ∀ t, Tendsto
      (fun k : ℕ => autocorr (criticalCollaredSharpTruncation ((k + 1 : ℕ) : ℝ) S b) t)
      atTop (𝓝 (autocorr (criticalCollaredSource S b) t)) := fun t => by
    have h := ((continuous_autocorr_L2_source t).tendsto
      ((memLp_criticalCollaredSource S b).toLp (criticalCollaredSource S b))).comp htoLp
    rw [autocorr_congr_ae (memLp_criticalCollaredSource S b).coeFn_toLp t] at h
    exact h.congr fun k =>
      autocorr_congr_ae (memLp_criticalCollaredSharpTruncation ((k + 1 : ℕ) : ℝ) S b).coeFn_toLp t
  have hlhs_tendsto : Tendsto (fun k : ℕ =>
      ∫ x in Ici (0 : ℝ), polarDensity x *
        autocorr (criticalCollaredSharpTruncation ((k + 1 : ℕ) : ℝ) S b) x) atTop
      (𝓝 (∫ x in Ici (0 : ℝ), polarDensity x * autocorr (criticalCollaredSource S b) x)) := by
    simp_rw [integral_Ici_eq_integral_Ioi]
    refine tendsto_integral_of_dominated_convergence
      (fun t => (2 * K) * Real.exp (-t))
      (fun k => by
        have hc : Continuous (autocorr (criticalCollaredSharpTruncation ((k + 1 : ℕ) : ℝ) S b)) := by
          have h := continuous_autocorr_of_memLp
            ((memLp_criticalCollaredSharpTruncation ((k + 1 : ℕ) : ℝ) S b).toLp _)
          exact h.congr fun x => autocorr_congr_ae
            (memLp_criticalCollaredSharpTruncation ((k + 1 : ℕ) : ℝ) S b).coeFn_toLp x
        exact ((by fun_prop : Continuous polarDensity).mul hc).aestronglyMeasurable)
      hmaj
      (fun k => by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
        have hpol_nn : 0 ≤ polarDensity t := by unfold polarDensity; positivity
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpol_nn, mul_comm]
        exact (mul_le_mul_of_nonneg_right
          (abs_autocorr_criticalCollaredSharpTruncation_le hk1 S b (le_of_lt ht))
          hpol_nn).trans (hpolar_le (le_of_lt ht) hK0))
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
        exact tendsto_const_nhds.mul (hac_pt t))
  set F : ℝ → ℝ := fun v => (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re
  have hFc : Continuous F := Complex.continuous_re.comp (continuous_factorialPhaseCombination _ _)
  have hR_tendsto : Tendsto (fun k : ℕ =>
      ∫ v in (1 : ℝ)..((k + 1 : ℕ) : ℝ), criticalCollarWeight v * F v) atTop
      (𝓝 (criticalCollaredPolarReadout S b)) := by
    have hint : IntegrableOn (fun v => criticalCollarWeight v * F v) (Ioi 1) :=
      integrableOn_criticalCollarWeight.mul_bdd hFc.aestronglyMeasurable
        (Eventually.of_forall fun v => by
          rw [Real.norm_eq_abs, factorialPhaseCombination_re_eq]
          exact abs_realPhaseCombination_le_two_mul S b v)
    have hV_top : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ)) atTop atTop := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    exact intervalIntegral_tendsto_integral_Ioi (μ := volume) 1 hint hV_top
  have hE_tendsto : Tendsto (fun k : ℕ =>
      ∫ v in (1 : ℝ)..((k + 1 : ℕ) : ℝ), criticalCollarEndpointWeight v * F v) atTop
      (𝓝 (criticalCollaredPolarEndpoint S b)) := by
    have hV_top : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ)) atTop atTop := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    exact (tendsto_integral_criticalCollarEndpointWeight_mul S b).comp hV_top
  have hrhs_tendsto := (hR_tendsto.mul hE_tendsto).congr fun k => by
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    exact (integral_polar_autocorr_criticalCollaredSharpTruncation hk1 S b).symm
  exact tendsto_nhds_unique hlhs_tendsto hrhs_tendsto

/-- Explicit `cosh(t/2)` form of the regularized polar normalization:
`4 ∫_{t > 0} autocorr g_c t * cosh(t/2) dt = 2 R_c E_c`. -/
theorem four_mul_integral_autocorr_cosh_criticalCollaredSource (S : Finset ℕ) (b : ℕ → ℝ) :
    4 * (∫ t in Ioi (0 : ℝ), autocorr (criticalCollaredSource S b) t * Real.cosh (t / 2)) =
      2 * (criticalCollaredPolarReadout S b * criticalCollaredPolarEndpoint S b) := by
  have h := congrArg (2 * ·) (integral_polar_autocorr_criticalCollaredSource S b)
  have hlhs : 2 * (∫ x in Ici (0 : ℝ),
      polarDensity x * autocorr (criticalCollaredSource S b) x) =
      4 * (∫ t in Ioi (0 : ℝ),
        autocorr (criticalCollaredSource S b) t * Real.cosh (t / 2)) := by
    rw [integral_Ici_eq_integral_Ioi]
    have hpt : (fun x => polarDensity x * autocorr (criticalCollaredSource S b) x) =
        fun x => 2 * (autocorr (criticalCollaredSource S b) x * Real.cosh (x / 2)) := by
      funext x; unfold polarDensity; ring
    rw [hpt, integral_const_mul]
    ring
  rwa [hlhs] at h

/-- Identification of `suzukiCriticalExtendedWeilEnergy` with `criticalCollaredCompleteEnergy` on
every collared critical source `criticalCollaredSource S b`. -/
theorem suzukiCriticalExtendedWeilEnergy_criticalCollaredSource (S : Finset ℕ) (b : ℕ → ℝ) :
    suzukiCriticalExtendedWeilEnergy (criticalCollaredSource S b) =
      criticalCollaredCompleteEnergy S b := by
  have hac0 : autocorr (criticalCollaredSource S b) 0 =
      sourceAutocorrelation (criticalCollaredSource S b) 0 :=
    (sourceAutocorrelation_eq_autocorr' _ 0).symm
  have hprime : (∑' n : ℕ, primeTerm (autocorr (criticalCollaredSource S b)) n) =
      criticalCollaredPrimeEnergy S b := by
    unfold criticalCollaredPrimeEnergy
    refine tsum_congr fun r => ?_
    unfold primeTerm criticalCollaredPrimeAtom primeWeight
    split_ifs
    · rw [← autocorr_neg]; unfold autocorr; simp only [sub_eq_add_neg]; rfl
    · simp
  have hpol := integral_polar_autocorr_criticalCollaredSource S b
  unfold suzukiCriticalExtendedWeilEnergy criticalCollaredCompleteEnergy
  congr 1
  rw [EReal.coe_eq_coe_iff]
  unfold fullPairing
  rw [hac0, hprime, hpol]
  ring

/-- Identification of `suzukiCriticalExtendedWeilEnergy` with `criticalTruncatedCompleteEnergy` and
`compactFullWeilEnergy` on every compact doubly collared source `criticalTruncatedSource V S b`. -/
theorem suzukiCriticalExtendedWeilEnergy_criticalTruncatedSource {V : ℝ} (hV : 0 < V)
    (S : Finset ℕ) (b : ℕ → ℝ) :
    suzukiCriticalExtendedWeilEnergy (criticalTruncatedSource V S b) =
      criticalTruncatedCompleteEnergy V S b := by
  set f := criticalTruncatedTest hV S b
  have hfg : (f : ℝ → ℝ) = criticalTruncatedSource V S b := rfl
  have hac0 : autocorr (criticalTruncatedSource V S b) 0 =
      sourceAutocorrelation (criticalTruncatedSource V S b) 0 :=
    (sourceAutocorrelation_eq_autocorr' _ 0).symm
  have hprime : (∑' n : ℕ, primeTerm (autocorr (criticalTruncatedSource V S b)) n) =
      criticalTruncatedPrimeEnergy V S b := by
    unfold criticalTruncatedPrimeEnergy
    refine tsum_congr fun r => ?_
    unfold primeTerm criticalTruncatedPrimeAtom primeWeight
    split_ifs
    · rw [← autocorr_neg]; unfold autocorr; simp only [sub_eq_add_neg]; rfl
    · simp
  have hpol : (∫ x in Ici (0 : ℝ), polarDensity x * autocorr (criticalTruncatedSource V S b) x) =
      criticalTruncatedPolarReadout V S b * criticalTruncatedPolarEndpoint V S b := by
    have hp := integral_polar_autocorr_eq_moments f
    rw [hfg] at hp
    have hR : (∫ u, Real.exp (u / 2) * criticalTruncatedSource V S b u) =
        criticalTruncatedPolarReadout V S b := by
      unfold criticalTruncatedPolarReadout
      exact integral_congr_ae (Eventually.of_forall fun u => by ring)
    have hE : (∫ u, Real.exp (-(u / 2)) * criticalTruncatedSource V S b u) =
        criticalTruncatedPolarEndpoint V S b := by
      unfold criticalTruncatedPolarEndpoint
      exact integral_congr_ae (Eventually.of_forall fun u => by ring)
    rw [hp, hR, hE]
  unfold suzukiCriticalExtendedWeilEnergy criticalTruncatedCompleteEnergy
  congr 1
  rw [EReal.coe_eq_coe_iff]
  unfold fullPairing
  rw [hac0, hprime, hpol]
  ring

/-! ## Section 4: Untruncated Collared Complete First Variation and Tannery Transfer to Windows and Lacunary Blocks -/

/-- **Untruncated Collared Complete First Variation Theorem.**
Every collared critical source `criticalCollaredSource S b` has exact positive-shift Suzuki first
variation equal to `criticalCollaredCompleteEnergy S b`. -/
theorem tendsto_suzukiCriticalCollaredSource_firstVariation (S : Finset ℕ) (b : ℕ → ℝ) :
    Tendsto (fun omega : ℝ =>
      (((autocorr (criticalCollaredSource S b) 0 -
        suzukiCriticalSourcePairing (criticalCollaredSource S b) omega) / omega : ℝ) : EReal))
      (𝓝[>] 0) (𝓝 (criticalCollaredCompleteEnergy S b)) := by
  rw [← suzukiCriticalExtendedWeilEnergy_criticalCollaredSource S b]
  exact tendsto_suzukiCriticalSourcePairing_extended_firstVariation_of_exp_decay
    (memLp_criticalCollaredSource S b) (by norm_num : (1 / 2 : ℝ) < 3 / 2)
    fun _ ht => abs_autocorr_criticalCollaredSource_le S b ht

/-- Strong `L²(ℝ)` convergence `criticalTruncatedSource V S b → criticalCollaredSource S b` as
`V → ∞`, at explicit rate `‖g^V - g_c‖₂ ≤ √(U ∑ b_n² / V)` for `V ≥ 1`. -/
theorem norm_criticalTruncatedSource_sub_collared_toLp_le {V : ℝ} (hV : 1 ≤ V)
    (S : Finset ℕ) (b : ℕ → ℝ) :
    ‖(memLp_criticalTruncatedSource V S b).toLp (criticalTruncatedSource V S b) -
      (memLp_criticalCollaredSource S b).toLp (criticalCollaredSource S b)‖ ≤
      Real.sqrt (criticalCollarMassUpper / V * ∑ n ∈ S, b n ^ 2) := by
  rw [norm_toLp_sub_eq_sqrt_integral_sq]
  refine Real.sqrt_le_sqrt ?_
  have hpt : (fun x => (criticalTruncatedSource V S b x - criticalCollaredSource S b x) ^ 2) =
      fun x => criticalTruncationTail V S b x ^ 2 := by
    funext x
    have h := criticalTruncatedSource_add_tail V S b x
    have hsub : criticalTruncatedSource V S b x - criticalCollaredSource S b x =
        -criticalTruncationTail V S b x := by linarith
    rw [hsub, neg_sq]
  rw [hpt]
  exact integral_criticalTruncationTail_sq_le hV S b

theorem tendsto_criticalTruncatedSource_toLp {V : ℕ → ℝ} (hV : Tendsto V atTop atTop)
    (S : Finset ℕ) (b : ℕ → ℝ) :
    Tendsto (fun j => (memLp_criticalTruncatedSource (V j) S b).toLp
      (criticalTruncatedSource (V j) S b))
      atTop (𝓝 ((memLp_criticalCollaredSource S b).toLp (criticalCollaredSource S b))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set C := criticalCollarMassUpper * ∑ n ∈ S, b n ^ 2
  have hinv : Tendsto (fun j => C * (V j)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_inv_atTop_zero.comp hV).const_mul C
  have hsqrt : Tendsto (fun j => Real.sqrt (criticalCollarMassUpper / V j * ∑ n ∈ S, b n ^ 2))
      atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hinv
    rw [Real.sqrt_zero] at h
    exact h.congr fun j => by dsimp only [Function.comp_apply, C]; congr 1; ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsqrt
    (Eventually.of_forall fun _ => norm_nonneg _) ?_
  filter_upwards [hV.eventually (eventually_ge_atTop 1)] with j hj
  exact norm_criticalTruncatedSource_sub_collared_toLp_le hj S b

/-- **Tannery Convergence of the Truncated Prime Channel to the Collared Prime Channel.** -/
theorem tendsto_criticalTruncatedPrimeEnergy_atTop (S : Finset ℕ) (b : ℕ → ℝ) :
    Tendsto (fun j : ℕ => criticalTruncatedPrimeEnergy ((j + 1 : ℕ) : ℝ) S b)
      atTop (𝓝 (criticalCollaredPrimeEnergy S b)) := by
  set K := criticalCollaredDecayConstant S b
  have hK0 : 0 ≤ K := by
    have := abs_autocorr_criticalCollaredSource_le S b le_rfl
    simpa using (abs_nonneg _).trans this
  have hsum : Summable (fun r : ℕ =>
      K * ((ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) ^ (2 : ℝ))) :=
    (RHTower.summable_vonMangoldt_div_rpow_mertensVonMangoldtEulerConstant
      (by norm_num : (1 : ℝ) < 2)).mul_left K
  have hV_top : Tendsto (fun j : ℕ => ((j + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have htoLp := tendsto_criticalTruncatedSource_toLp hV_top S b
  refine tendsto_tsum_of_dominated_convergence hsum (fun r => ?_) ?_
  · by_cases hr : 2 ≤ r
    · have hac : Tendsto (fun j : ℕ =>
          autocorr (criticalTruncatedSource ((j + 1 : ℕ) : ℝ) S b) (Real.log r))
          atTop (𝓝 (autocorr (criticalCollaredSource S b) (Real.log r))) := by
        have h := ((continuous_autocorr_L2_source (Real.log r)).tendsto
          ((memLp_criticalCollaredSource S b).toLp (criticalCollaredSource S b))).comp htoLp
        rw [autocorr_congr_ae (memLp_criticalCollaredSource S b).coeFn_toLp] at h
        exact h.congr fun j =>
          autocorr_congr_ae (memLp_criticalTruncatedSource ((j + 1 : ℕ) : ℝ) S b).coeFn_toLp _
      have heq_t : ∀ j : ℕ, criticalTruncatedPrimeAtom ((j + 1 : ℕ) : ℝ) S b r =
          ((ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt r) *
            autocorr (criticalTruncatedSource ((j + 1 : ℕ) : ℝ) S b) (Real.log r) := fun j => by
        unfold criticalTruncatedPrimeAtom
        rw [if_pos hr, ← autocorr_neg]
        unfold autocorr; simp only [sub_eq_add_neg]
      have heq_c : criticalCollaredPrimeAtom S b r =
          ((ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt r) *
            autocorr (criticalCollaredSource S b) (Real.log r) := by
        unfold criticalCollaredPrimeAtom
        rw [if_pos hr, ← autocorr_neg]
        unfold autocorr; simp only [sub_eq_add_neg]
      rw [heq_c]
      exact (hac.const_mul _).congr fun j => (heq_t j).symm
    · simp only [criticalTruncatedPrimeAtom, criticalCollaredPrimeAtom, if_neg hr, zero_mul]
      exact tendsto_const_nhds
  · refine Eventually.of_forall fun j r => ?_
    by_cases hr : 2 ≤ r
    · have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
      have hlog : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast (show 1 ≤ r by omega))
      have hj0 : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
      have hcorr := abs_autocorr_criticalTruncatedSource_le hj0 S b hlog
      have heq_t : criticalTruncatedPrimeAtom ((j + 1 : ℕ) : ℝ) S b r =
          ((ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt r) *
            autocorr (criticalTruncatedSource ((j + 1 : ℕ) : ℝ) S b) (Real.log r) := by
        unfold criticalTruncatedPrimeAtom
        rw [if_pos hr, ← autocorr_neg]
        unfold autocorr; simp only [sub_eq_add_neg]
      rw [heq_t, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))]
      have hexp_r : Real.exp (-(3 / 2 : ℝ) * Real.log r) = (r : ℝ) ^ (-(3 / 2 : ℝ)) := by
        rw [Real.rpow_def_of_pos hr0]; congr 1; ring
      have hpow_combine : (Real.sqrt r)⁻¹ * (r : ℝ) ^ (-(3 / 2 : ℝ)) =
          ((r : ℝ) ^ (2 : ℝ))⁻¹ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hr0.le, ← Real.rpow_add hr0,
          ← Real.rpow_neg hr0.le]
        congr 1; ring
      calc ((ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt r) *
            |autocorr (criticalTruncatedSource ((j + 1 : ℕ) : ℝ) S b) (Real.log r)|
          ≤ ((ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt r) *
              (K * Real.exp (-(3 / 2 : ℝ) * Real.log r)) :=
            mul_le_mul_of_nonneg_left hcorr
              (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
        _ = K * ((ArithmeticFunction.vonMangoldt r : ℝ) *
              ((Real.sqrt r)⁻¹ * (r : ℝ) ^ (-(3 / 2 : ℝ)))) := by
            rw [hexp_r, div_eq_mul_inv]; ring
        _ = K * ((ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) ^ (2 : ℝ)) := by
            rw [hpow_combine, div_eq_mul_inv]
    · simp only [criticalTruncatedPrimeAtom, if_neg hr, zero_mul, norm_zero]
      exact mul_nonneg hK0 (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg r) _))

/-- Logarithmic prime-window bound for untruncated collared critical sources on `ScaleWindow S M L`. -/
theorem abs_criticalCollaredPrimeEnergy_le_of_window {S : Finset ℕ} {M L : ℕ}
    (hM : 1 ≤ M) (hL : 1 ≤ L) (hS : ScaleWindow S M L) (b : ℕ → ℝ) :
    |criticalCollaredPrimeEnergy S b| ≤
      criticalTruncatedWindowPrimeSlope * (3 + Real.log L) * ∑ n ∈ S, b n ^ 2 := by
  refine le_of_tendsto' (tendsto_criticalTruncatedPrimeEnergy_atTop S b).abs fun j => ?_
  exact abs_criticalTruncatedPrimeEnergy_le_of_window (by positivity) hM hL hS b

/-- `ℓ²` prime-channel bound for untruncated collared critical sources on arbitrary-depth lacunary
block unions. -/
theorem abs_criticalCollaredPrimeEnergy_le_of_lacunary {J : ℕ} {M : ℕ → ℕ} {S : ℕ → Finset ℕ}
    (h : IsLacunaryBlockFamily J M S) (b : ℕ → ℝ) :
    |criticalCollaredPrimeEnergy ((Finset.range J).biUnion S) b| ≤
      lacunaryPrimeConstant * ∑ n ∈ (Finset.range J).biUnion S, b n ^ 2 := by
  refine le_of_tendsto'
    (tendsto_criticalTruncatedPrimeEnergy_atTop ((Finset.range J).biUnion S) b).abs fun j => ?_
  exact abs_criticalTruncatedPrimeEnergy_le_of_lacunary (by positivity) h b

/-- Gamma + polar base channel constant of untruncated collared critical sources. -/
def criticalCollaredWindowBaseConstant : ℝ :=
  |EF.gammaBracket 0| * criticalCollarMassUpper +
    288 * (∫ v in Ioi 1, |deriv criticalCollarWeight v|) *
      (∫ v in Ioi 1, |deriv criticalCollarEndpointWeight v|)

/-- Lacunary channel constant of untruncated collared critical sources. -/
def criticalCollaredLacunaryChannelConstant : ℝ :=
  criticalCollaredWindowBaseConstant + 2 * lacunaryPrimeConstant

private theorem neg_le_criticalCollaredGammaPolar {S : Finset ℕ} (b : ℕ → ℝ) {M : ℕ}
    (hM : 2 ≤ M) (hlower : ∀ n ∈ S, M ≤ n + 1) :
    -(criticalCollaredWindowBaseConstant * ∑ n ∈ S, b n ^ 2) ≤
      EF.gammaBracket 0 * sourceAutocorrelation (criticalCollaredSource S b) 0 +
        2 * (criticalCollaredPolarReadout S b * criticalCollaredPolarEndpoint S b) := by
  set E := ∑ n ∈ S, b n ^ 2
  set ac := sourceAutocorrelation (criticalCollaredSource S b) 0
  set a := ∫ v in Ioi 1, |deriv criticalCollarWeight v|
  set c := ∫ v in Ioi 1, |deriv criticalCollarEndpointWeight v|
  set T := ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)
  have ha : 0 ≤ a := integral_nonneg fun _ => abs_nonneg _
  have hc : 0 ≤ c := integral_nonneg fun _ => abs_nonneg _
  have hM0 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hac0 : 0 ≤ ac := by
    unfold ac sourceAutocorrelation
    exact integral_nonneg fun y => by simp only [sub_zero]; exact mul_self_nonneg _
  have hac := sourceAutocorrelation_criticalCollaredSource_zero_le S b
  have hΩ : -(|EF.gammaBracket 0| * (criticalCollarMassUpper * E)) ≤ EF.gammaBracket 0 * ac := by
    have h1 : -(|EF.gammaBracket 0| * ac) ≤ EF.gammaBracket 0 * ac := by
      have := neg_abs_le (EF.gammaBracket 0 * ac)
      rwa [abs_mul, abs_of_nonneg hac0] at this
    have h2 : |EF.gammaBracket 0| * ac ≤ |EF.gammaBracket 0| * (criticalCollarMassUpper * E) :=
      mul_le_mul_of_nonneg_left hac (abs_nonneg _)
    linarith
  have hT2 := sq_sum_abs_div_succ_le S b hM hlower
  have hpol : |criticalCollaredPolarReadout S b * criticalCollaredPolarEndpoint S b| ≤
      144 * a * c * E := by
    rw [abs_mul]
    have h1 := abs_criticalCollaredPolarReadout_le S b
    have h2 := abs_criticalCollaredPolarEndpoint_le S b
    have h12 := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    have hTE : T ^ 2 ≤ E := hT2.trans (by
      have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have : 2 / (M : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hM0
      nlinarith)
    calc _ ≤ a * (12 * T) * (c * (12 * T)) := h12
      _ = 144 * a * c * T ^ 2 := by ring
      _ ≤ 144 * a * c * E := mul_le_mul_of_nonneg_left hTE (by positivity)
  have hpol' := (abs_le.mp hpol).1
  unfold criticalCollaredWindowBaseConstant
  linarith

/-- **Complete Collared Critical Energy on Scale Windows `[M, LM]`.** -/
theorem criticalCollaredCompleteEnergy_ge_of_window (S : Finset ℕ) (b : ℕ → ℝ) {M L : ℕ}
    (hM : 2 ≤ M) (hL : 1 ≤ L) (hS : ScaleWindow S M L) :
    (((criticalCollarArchLogSlope * (Real.log M - criticalCollarArchLogOffset) -
        criticalCollaredWindowBaseConstant -
        2 * criticalTruncatedWindowPrimeSlope * (3 + Real.log L)) *
          ∑ n ∈ S, b n ^ 2 : ℝ) : EReal) ≤
      criticalCollaredCompleteEnergy S b := by
  set E := ∑ n ∈ S, b n ^ 2
  set X := criticalCollarArchLogSlope * (Real.log M - criticalCollarArchLogOffset) * E
  have hlev : (X : EReal) ≤ (sourceLevyEnergy (criticalCollaredSource S b) : EReal) := by
    have h1 := ofReal_le_criticalCollaredLevyEnergy S b hM fun n hn => (hS n hn).1
    have h2 := EReal.coe_ennreal_le_coe_ennreal_iff.mpr h1
    rw [EReal.coe_ennreal_ofReal] at h2
    exact le_trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)) h2
  have hgp := neg_le_criticalCollaredGammaPolar b hM fun n hn => (hS n hn).1
  have hP := (abs_le.mp (abs_criticalCollaredPrimeEnergy_le_of_window (by omega) hL hS b)).2
  have hch : -((criticalCollaredWindowBaseConstant +
      2 * criticalTruncatedWindowPrimeSlope * (3 + Real.log L)) * E) ≤
      EF.gammaBracket 0 * sourceAutocorrelation (criticalCollaredSource S b) 0 +
        2 * (criticalCollaredPolarReadout S b * criticalCollaredPolarEndpoint S b) -
        2 * criticalCollaredPrimeEnergy S b := by
    have hring : (criticalCollaredWindowBaseConstant +
        2 * criticalTruncatedWindowPrimeSlope * (3 + Real.log L)) * E =
        criticalCollaredWindowBaseConstant * E +
          2 * (criticalTruncatedWindowPrimeSlope * (3 + Real.log L) * E) := by ring
    linarith
  unfold criticalCollaredCompleteEnergy
  rw [show (criticalCollarArchLogSlope * (Real.log M - criticalCollarArchLogOffset) -
      criticalCollaredWindowBaseConstant -
      2 * criticalTruncatedWindowPrimeSlope * (3 + Real.log L)) * E =
      X + -((criticalCollaredWindowBaseConstant +
        2 * criticalTruncatedWindowPrimeSlope * (3 + Real.log L)) * E) by ring,
    EReal.coe_add]
  exact add_le_add hlev (EReal.coe_le_coe_iff.mpr hch)

/-- **Complete Collared Critical Energy on Lacunary Block Unions.** -/
theorem criticalCollaredCompleteEnergy_ge_of_lacunary {J : ℕ} {M : ℕ → ℕ} {S : ℕ → Finset ℕ}
    (h : IsLacunaryBlockFamily J M S) (b : ℕ → ℝ) :
    (((criticalCollarArchLogSlope * (Real.log (M 0) - criticalCollarArchLogOffset) -
        criticalCollaredLacunaryChannelConstant) *
          ∑ n ∈ (Finset.range J).biUnion S, b n ^ 2 : ℝ) : EReal) ≤
      criticalCollaredCompleteEnergy ((Finset.range J).biUnion S) b := by
  set T := (Finset.range J).biUnion S
  set E := ∑ n ∈ T, b n ^ 2
  have hM : 2 ≤ M 0 := by have := h.1; omega
  set X := criticalCollarArchLogSlope * (Real.log (M 0) - criticalCollarArchLogOffset) * E
  have hlev : (X : EReal) ≤ (sourceLevyEnergy (criticalCollaredSource T b) : EReal) := by
    have h1 := ofReal_le_criticalCollaredLevyEnergy T b hM fun n hn => h.lower hn
    have h2 := EReal.coe_ennreal_le_coe_ennreal_iff.mpr h1
    rw [EReal.coe_ennreal_ofReal] at h2
    exact le_trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)) h2
  have hgp := neg_le_criticalCollaredGammaPolar b hM fun n hn => h.lower hn
  have hP := (abs_le.mp (abs_criticalCollaredPrimeEnergy_le_of_lacunary h b)).2
  have hch : -(criticalCollaredLacunaryChannelConstant * E) ≤
      EF.gammaBracket 0 * sourceAutocorrelation (criticalCollaredSource T b) 0 +
        2 * (criticalCollaredPolarReadout T b * criticalCollaredPolarEndpoint T b) -
        2 * criticalCollaredPrimeEnergy T b := by
    unfold criticalCollaredLacunaryChannelConstant
    have hring : (criticalCollaredWindowBaseConstant + 2 * lacunaryPrimeConstant) * E =
        criticalCollaredWindowBaseConstant * E + 2 * (lacunaryPrimeConstant * E) := by ring
    linarith
  unfold criticalCollaredCompleteEnergy
  rw [show (criticalCollarArchLogSlope * (Real.log (M 0) - criticalCollarArchLogOffset) -
      criticalCollaredLacunaryChannelConstant) * E =
      X + -(criticalCollaredLacunaryChannelConstant * E) by ring,
    EReal.coe_add]
  exact add_le_add hlev (EReal.coe_le_coe_iff.mpr hch)

/-! ## Section 5: Simultaneous `(V, b)`-Uniform Moving-Aperture and Infinite-Head Shift Thresholds Without `C²` Regularity -/

private theorem autocorr_const_mul (c : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    autocorr (fun x => c * f x) t = c ^ 2 * autocorr f t := by
  unfold autocorr
  have hpt : (fun u => (c * f u) * (c * f (u + t))) = fun u => c ^ 2 * (f u * f (u + t)) := by
    funext u; ring
  rw [hpt, integral_const_mul]

private theorem suzukiCriticalSourcePairing_const_mul (c : ℝ) (f : ℝ → ℝ) (omega : ℝ) :
    suzukiCriticalSourcePairing (fun x => c * f x) omega =
      c ^ 2 * suzukiCriticalSourcePairing f omega := by
  unfold suzukiCriticalSourcePairing
  have hpt : (fun t => autocorr (fun x => c * f x) t *
      (Real.exp (t / 2) * (suzukiSourceHFinite omega (Real.exp t)).re)) =
      fun t => c ^ 2 * (autocorr f t *
        (Real.exp (t / 2) * (suzukiSourceHFinite omega (Real.exp t)).re)) := by
    funext t; rw [autocorr_const_mul]; ring
  rw [hpt, integral_const_mul]

private theorem realPhaseCombination_congr_scale {S : Finset ℕ} {b₁ b₂ : ℕ → ℝ} (c : ℝ)
    (h : ∀ n ∈ S, b₁ n = c * b₂ n) (v : ℝ) :
    realPhaseCombination S b₁ v = c * realPhaseCombination S b₂ v := by
  unfold realPhaseCombination
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun n hn => by rw [h n hn, mul_assoc]

private theorem criticalCollaredSource_congr_scale {S : Finset ℕ} {b₁ b₂ : ℕ → ℝ} (c : ℝ)
    (h : ∀ n ∈ S, b₁ n = c * b₂ n) :
    criticalCollaredSource S b₁ = fun x => c * criticalCollaredSource S b₂ x := by
  funext x
  rw [criticalCollaredSource_eq, criticalCollaredSource_eq,
    realPhaseCombination_congr_scale c h]
  ring

private theorem criticalTruncatedSource_congr_scale (V : ℝ) {S : Finset ℕ} {b₁ b₂ : ℕ → ℝ}
    (c : ℝ) (h : ∀ n ∈ S, b₁ n = c * b₂ n) :
    criticalTruncatedSource V S b₁ = fun x => c * criticalTruncatedSource V S b₂ x := by
  funext x
  rw [criticalTruncatedSource, criticalTruncatedSource,
    congrFun (criticalCollaredSource_congr_scale c h) x]
  ring

private def sphereS (S : Finset ℕ) : Set (S → ℝ) :=
  {u : S → ℝ | (∀ i : S, u i ∈ Icc (-1 : ℝ) 1) ∧ ∑ i : S, (u i) ^ 2 = 1}

private def extendCoeff (S : Finset ℕ) (u : S → ℝ) (n : ℕ) : ℝ :=
  if h : n ∈ S then u ⟨n, h⟩ else 0

private theorem isCompact_sphereS (S : Finset ℕ) : IsCompact (sphereS S) := by
  have heq : sphereS S =
      (Set.pi Set.univ fun _ : S => Icc (-1 : ℝ) 1) ∩ {u : S → ℝ | ∑ i : S, (u i) ^ 2 = 1} := by
    ext u; simp [sphereS]
  rw [heq]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).inter_right
    (isClosed_eq (continuous_finset_sum _ fun i _ => (continuous_apply i).pow 2) continuous_const)

private theorem sum_extendCoeff_sq (S : Finset ℕ) (u : S → ℝ) :
    ∑ n ∈ S, (extendCoeff S u n) ^ 2 = ∑ i : S, (u i) ^ 2 := by
  rw [← Finset.sum_attach S (fun n => (extendCoeff S u n) ^ 2)]
  exact Finset.sum_congr rfl fun i _ => by simp [extendCoeff, i.2]

private theorem criticalCollaredDecayConstant_le_ones (S : Finset ℕ) {b : ℕ → ℝ}
    (hb : ∀ n ∈ S, |b n| ≤ 1) :
    criticalCollaredDecayConstant S b ≤ criticalCollaredDecayConstant S (fun _ => 1) := by
  have hU0 : 0 ≤ criticalCollarMassUpper := by
    unfold criticalCollarMassUpper
    have := factorialUnitIntervalUpper_pos
    positivity
  have hsq : ∑ n ∈ S, b n ^ 2 ≤ ∑ _n ∈ S, (1 : ℝ) ^ 2 := by
    refine Finset.sum_le_sum fun n hn => ?_
    rw [← sq_abs, one_pow]
    exact pow_le_one₀ (abs_nonneg _) (hb n hn)
  have habs : ∑ n ∈ S, |b n| ≤ ∑ _n ∈ S, |(1 : ℝ)| := by
    refine Finset.sum_le_sum fun n hn => ?_
    simpa only [abs_one] using hb n hn
  have hlip : realPhaseLipschitz S b ≤ realPhaseLipschitz S (fun _ => 1) := by
    unfold realPhaseLipschitz
    refine Finset.sum_le_sum fun n hn => ?_
    have hfreq : 0 ≤ 9 / 2 * (factorialShiftedFreq (n + 1) + ((n + 1 : ℕ) : ℝ)) := by
      have := (factorialShiftedFreq_sub_self_bounds (N := n + 1) (by omega)).1
      have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have : 0 ≤ factorialShiftedFreq (n + 1) := by linarith
      positivity
    rw [abs_one]
    exact mul_le_mul_of_nonneg_right (hb n hn) hfreq
  have hprim : ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ) ≤
      ∑ n ∈ S, |(1 : ℝ)| / ((n + 1 : ℕ) : ℝ) := by
    refine Finset.sum_le_sum fun n hn => ?_
    rw [abs_one]
    exact div_le_div_of_nonneg_right (hb n hn) (by positivity)
  have hread : 0 ≤ 1 + criticalTruncatedReadoutConstant := by
    unfold criticalTruncatedReadoutConstant
    have : 0 ≤ ∫ v in Ioi 1, |deriv criticalCollarWeight v| := integral_nonneg fun _ => abs_nonneg _
    have := smoothTransitionSlope_nonneg
    have : 0 ≤ criticalCollarMass := integral_nonneg fun _ => abs_nonneg _
    positivity
  have hmass : 0 ≤ criticalCollarMass := integral_nonneg fun _ => abs_nonneg _
  unfold criticalCollaredDecayConstant
  refine max_le_max ?_ ?_
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hU0) (Real.exp_pos _).le
  · refine mul_le_mul (add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habs zero_le_two) hread)
      (mul_le_mul_of_nonneg_right hlip hmass))
      (mul_le_mul_of_nonneg_left hprim (by norm_num))
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => by positivity))
      (add_nonneg (mul_nonneg (mul_nonneg zero_le_two
        (Finset.sum_nonneg fun _ _ => abs_nonneg _)) hread)
        (mul_nonneg (realPhaseLipschitz_nonneg S _) hmass))

private def paramSource (S : Finset ℕ) (p : ℝ × (S → ℝ)) : ℝ → ℝ :=
  if p.1 ≤ 0 then criticalCollaredSource S (extendCoeff S p.2)
  else criticalTruncatedSource (1 / p.1) S (extendCoeff S p.2)

private theorem memLp_paramSource (S : Finset ℕ) (p : ℝ × (S → ℝ)) :
    MemLp (paramSource S p) 2 volume := by
  unfold paramSource
  split_ifs
  · exact memLp_criticalCollaredSource S _
  · exact memLp_criticalTruncatedSource _ S _

private theorem paramSource_sub_coeff_norm_le (S : Finset ℕ) (q : ℝ) (u v : S → ℝ) :
    ‖(memLp_paramSource S (q, u)).toLp (paramSource S (q, u)) -
      (memLp_paramSource S (q, v)).toLp (paramSource S (q, v))‖ ≤
      Real.sqrt (criticalCollarMassUpper * ∑ i : S, (u i - v i) ^ 2) := by
  rw [norm_toLp_sub_eq_sqrt_integral_sq]
  refine Real.sqrt_le_sqrt ?_
  have hdiff_phase : ∀ y, realPhaseCombination S (extendCoeff S u) y -
      realPhaseCombination S (extendCoeff S v) y =
      realPhaseCombination S (extendCoeff S (u - v)) y := fun y => by
    unfold realPhaseCombination
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [extendCoeff, dif_pos hn, Pi.sub_apply, sub_mul]
  by_cases hq : q ≤ 0
  · have hpt : ∀ x, paramSource S (q, u) x - paramSource S (q, v) x =
        criticalCollaredSource S (extendCoeff S (u - v)) x := fun x => by
      simp only [paramSource, if_pos hq, criticalCollaredSource_eq]
      rw [← hdiff_phase]; ring
    simp_rw [hpt]
    have h0 := sourceAutocorrelation_criticalCollaredSource_zero_le S (extendCoeff S (u - v))
    have hsq : sourceAutocorrelation (criticalCollaredSource S (extendCoeff S (u - v))) 0 =
        ∫ x, criticalCollaredSource S (extendCoeff S (u - v)) x ^ 2 := by
      unfold sourceAutocorrelation; simp only [sub_zero, sq]
    rw [hsq, sum_extendCoeff_sq] at h0
    exact h0
  · have hpt : ∀ x, paramSource S (q, u) x - paramSource S (q, v) x =
        criticalTruncatedSource (1 / q) S (extendCoeff S (u - v)) x := fun x => by
      simp only [paramSource, if_neg hq, criticalTruncatedSource, criticalCollaredSource_eq]
      rw [← hdiff_phase]; ring
    simp_rw [hpt]
    have h0 := sourceAutocorrelation_criticalTruncatedSource_zero_le (1 / q) S
      (extendCoeff S (u - v))
    have hsq : sourceAutocorrelation
        (criticalTruncatedSource (1 / q) S (extendCoeff S (u - v))) 0 =
        ∫ x, criticalTruncatedSource (1 / q) S (extendCoeff S (u - v)) x ^ 2 := by
      unfold sourceAutocorrelation; simp only [sub_zero, sq]
    rw [hsq, sum_extendCoeff_sq] at h0
    exact h0

private theorem continuousOn_paramSource_toLp (S : Finset ℕ) :
    ContinuousOn
      (fun p : ℝ × (S → ℝ) => (memLp_paramSource S p).toLp (paramSource S p))
      (Icc 0 (1 / criticalTruncationThreshold) ×ˢ sphereS S) := by
  have hV0_gt1 : 1 < criticalTruncationThreshold := by
    unfold criticalTruncationThreshold
    exact lt_of_lt_of_le (by linarith [factorialWindowLength_pos]) (le_max_left _ _)
  rw [Metric.continuousOn_iff]
  intro ⟨q₀, u₀⟩ hp₀ ε hε
  have hq₀_mem : q₀ ∈ Icc 0 (1 / criticalTruncationThreshold) := hp₀.1
  have hu₀_mem : u₀ ∈ sphereS S := hp₀.2
  have hU_pos : 0 < criticalCollarMassUpper + 1 := by
    unfold criticalCollarMassUpper
    have := factorialUnitIntervalUpper_pos
    positivity
  -- Step 1: Continuity in `q` at fixed `u₀` inside `[0, 1 / V₀]`.
  have hcont_q : ContinuousWithinAt
      (fun q : ℝ => (memLp_paramSource S (q, u₀)).toLp (paramSource S (q, u₀)))
      (Icc 0 (1 / criticalTruncationThreshold)) q₀ := by
    rcases hq₀_mem.1.eq_or_lt with rfl | hq₀_pos
    · rw [Metric.continuousWithinAt_iff]
      intro η hη
      refine ⟨(η / 2) ^ 2 / (criticalCollarMassUpper + 1), by positivity, fun q hq hdist => ?_⟩
      rcases hq.1.eq_or_lt with rfl | hq_pos
      · simp [hη]
      · have hq_lt1 : q ≤ 1 := hq.2.trans ((div_le_one (by linarith)).mpr hV0_gt1.le)
        have h1q : 1 ≤ 1 / q := (one_le_div hq_pos).mpr hq_lt1
        rw [dist_eq_norm]
        have hle := norm_criticalTruncatedSource_sub_collared_toLp_le h1q S (extendCoeff S u₀)
        have hsum1 : ∑ n ∈ S, (extendCoeff S u₀ n) ^ 2 = 1 := by
          rw [sum_extendCoeff_sq]; exact hu₀_mem.2
        rw [hsum1, mul_one, div_one_div] at hle
        have hparam_eq : (memLp_paramSource S (q, u₀)).toLp (paramSource S (q, u₀)) -
            (memLp_paramSource S (0, u₀)).toLp (paramSource S (0, u₀)) =
            (memLp_criticalTruncatedSource (1 / q) S (extendCoeff S u₀)).toLp
              (criticalTruncatedSource (1 / q) S (extendCoeff S u₀)) -
            (memLp_criticalCollaredSource S (extendCoeff S u₀)).toLp
              (criticalCollaredSource S (extendCoeff S u₀)) := by
          congr 1 <;> apply MemLp.toLp_congr_ae <;>
            simp [paramSource, not_le.mpr hq_pos]
        rw [hparam_eq]
        have hq_dist : q < (η / 2) ^ 2 / (criticalCollarMassUpper + 1) := by
          simpa [Real.dist_eq, abs_of_pos hq_pos] using hdist
        have hprod_lt : criticalCollarMassUpper * q < (η / 2) ^ 2 := by
          have h1 : (criticalCollarMassUpper + 1) * q < (η / 2) ^ 2 :=
            (lt_div_iff₀' hU_pos).mp hq_dist
          nlinarith [hq_pos]
        have hsqrt_le : Real.sqrt (criticalCollarMassUpper * q) ≤ η / 2 := by
          rw [← Real.sqrt_sq (by positivity : 0 ≤ η / 2)]
          exact Real.sqrt_le_sqrt hprod_lt.le
        linarith [hle.trans hsqrt_le]
    · apply ContinuousAt.continuousWithinAt
      rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
      intro qn hqn
      rw [Function.comp_def, tendsto_iff_norm_sub_tendsto_zero]
      have hpos_ev : ∀ᶠ k in atTop, 0 < qn k := hqn.eventually (Ioi_mem_nhds hq₀_pos)
      have hgc := memLp_criticalCollaredSource S (extendCoeff S u₀)
      have hint_sq : Integrable (fun x => (4 : ℝ) *
          criticalCollaredSource S (extendCoeff S u₀) x ^ 2) := hgc.integrable_sq.const_mul 4
      have hsq_zero : Tendsto (fun k => ∫ x,
          (paramSource S (qn k, u₀) x - paramSource S (q₀, u₀) x) ^ 2) atTop (𝓝 0) := by
        have hdom := tendsto_integral_of_dominated_convergence
          (fun x => (4 : ℝ) * criticalCollaredSource S (extendCoeff S u₀) x ^ 2)
          (fun k => ((memLp_paramSource S (qn k, u₀)).sub
            (memLp_paramSource S (q₀, u₀))).integrable_sq.aestronglyMeasurable)
          hint_sq
          (fun k => Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            have habs_le : ∀ r, |paramSource S (r, u₀) x| ≤
                |criticalCollaredSource S (extendCoeff S u₀) x| := fun r => by
              unfold paramSource
              split_ifs
              · exact le_rfl
              · rw [criticalTruncatedSource, abs_mul,
                  abs_of_nonneg (criticalUpperCutoff_nonneg _)]
                exact mul_le_of_le_one_left (abs_nonneg _) (criticalUpperCutoff_le_one _)
            have htri : |paramSource S (qn k, u₀) x - paramSource S (q₀, u₀) x| ≤
                2 * |criticalCollaredSource S (extendCoeff S u₀) x| :=
              (abs_sub _ _).trans (by linarith [habs_le (qn k), habs_le q₀])
            have hsq := pow_le_pow_left₀ (abs_nonneg _) htri 2
            simpa only [sq_abs, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hsq)
          (Eventually.of_forall fun x => by
            have hval : Tendsto (fun k =>
                criticalUpperCutoff (Real.exp (-x) * qn k) *
                  criticalCollaredSource S (extendCoeff S u₀) x) atTop
                (𝓝 (criticalUpperCutoff (Real.exp (-x) * q₀) *
                  criticalCollaredSource S (extendCoeff S u₀) x)) :=
              ((continuous_criticalUpperCutoff.tendsto _).comp
                (hqn.const_mul (Real.exp (-x)))).mul_const _
            have hdiff := (hval.sub tendsto_const_nhds).pow 2
            rw [sub_self, zero_pow two_ne_zero] at hdiff
            refine hdiff.congr' ?_
            filter_upwards [hpos_ev] with k hk
            simp only [paramSource, if_neg (not_le.mpr hk), if_neg (not_le.mpr hq₀_pos),
              criticalTruncatedSource, div_one_div])
        simpa only [integral_zero] using hdom
      have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq_zero
      rw [Real.sqrt_zero] at hsqrt
      exact hsqrt.congr fun k => (norm_toLp_sub_eq_sqrt_integral_sq
        (memLp_paramSource S (qn k, u₀)) (memLp_paramSource S (q₀, u₀))).symm
  rw [Metric.continuousWithinAt_iff] at hcont_q
  obtain ⟨δ₁, hδ₁, hq_close⟩ := hcont_q (ε / 2) (half_pos hε)
  set δ₂ := ε / (2 * Real.sqrt ((criticalCollarMassUpper + 1) * (S.card + 1)))
  have hδ₂ : 0 < δ₂ := by positivity
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun ⟨q, u⟩ hp hdist => ?_⟩
  have hdist_q : dist q q₀ < δ₁ :=
    (Prod.dist_eq.symm ▸ le_max_left _ _).trans_lt (hdist.trans_le (min_le_left _ _))
  have hdist_u : dist u u₀ < δ₂ :=
    (Prod.dist_eq.symm ▸ le_max_right _ _).trans_lt (hdist.trans_le (min_le_right _ _))
  have h1 : dist ((memLp_paramSource S (q, u₀)).toLp (paramSource S (q, u₀)))
      ((memLp_paramSource S (q₀, u₀)).toLp (paramSource S (q₀, u₀))) < ε / 2 :=
    hq_close hp.1 hdist_q
  have h2 : dist ((memLp_paramSource S (q, u)).toLp (paramSource S (q, u)))
      ((memLp_paramSource S (q, u₀)).toLp (paramSource S (q, u₀))) < ε / 2 := by
    rw [dist_eq_norm]
    have hle := paramSource_sub_coeff_norm_le S q u u₀
    have hsum_le : ∑ i : S, (u i - u₀ i) ^ 2 ≤ (S.card : ℝ) * δ₂ ^ 2 := by
      calc ∑ i : S, (u i - u₀ i) ^ 2
          ≤ ∑ _i : S, δ₂ ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hi : |u i - u₀ i| ≤ dist u u₀ := by
              simpa only [Real.dist_eq] using dist_le_pi_dist u u₀ i
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hi.trans hdist_u.le) 2
        _ = (S.card : ℝ) * δ₂ ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    have hU0 : 0 ≤ criticalCollarMassUpper := by
      unfold criticalCollarMassUpper
      have := factorialUnitIntervalUpper_pos
      positivity
    have hprod_lt : criticalCollarMassUpper * ∑ i : S, (u i - u₀ i) ^ 2 < (ε / 2) ^ 2 := by
      calc criticalCollarMassUpper * ∑ i : S, (u i - u₀ i) ^ 2
          ≤ criticalCollarMassUpper * ((S.card : ℝ) * δ₂ ^ 2) :=
            mul_le_mul_of_nonneg_left hsum_le hU0
        _ < (criticalCollarMassUpper + 1) * ((S.card + 1 : ℝ) * δ₂ ^ 2) := by
            have hd2_pos : 0 < δ₂ ^ 2 := sq_pos_of_pos hδ₂
            have hcard0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
            nlinarith
        _ = (ε / 2) ^ 2 := by
            unfold δ₂
            rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
            field_simp
    have hsqrt_lt : Real.sqrt (criticalCollarMassUpper * ∑ i : S, (u i - u₀ i) ^ 2) < ε / 2 := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ ε / 2)]
      exact Real.sqrt_lt_sqrt (mul_nonneg hU0 (Finset.sum_nonneg fun _ _ => sq_nonneg _)) hprod_lt
    exact hle.trans_lt hsqrt_lt
  calc dist ((memLp_paramSource S (q, u)).toLp (paramSource S (q, u)))
        ((memLp_paramSource S (q₀, u₀)).toLp (paramSource S (q₀, u₀)))
      ≤ dist ((memLp_paramSource S (q, u)).toLp (paramSource S (q, u)))
          ((memLp_paramSource S (q, u₀)).toLp (paramSource S (q, u₀))) +
        dist ((memLp_paramSource S (q, u₀)).toLp (paramSource S (q, u₀)))
          ((memLp_paramSource S (q₀, u₀)).toLp (paramSource S (q₀, u₀))) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add h2 h1
    _ = ε := add_halves ε

/-- **Simultaneous `(V, b)`-Uniform Moving-Aperture and Infinite-Head Shift Theorem.**
Whenever a finite index set `S` admits a positive energy floor `γ > 0` across both
`criticalCollaredCompleteEnergy S b` and `criticalTruncatedCompleteEnergy V S b`
(`∀ V ≥ criticalTruncationThreshold`), sequential compactness of the compactified parameter space
`[0, 1 / V₀] × S(S)` combined with `V`- and `b`-uniform `O(e^{-3t/2})` correlation decay and
2-homogeneity produces a **single shift threshold `ω₀ > 0` independent of both `V` and `b`**
governing all `V ≥ criticalTruncationThreshold` and the untruncated collared source simultaneously,
without `C²` smoothness. -/
theorem exists_suzukiCriticalUniformShift_of_collared_family {S : Finset ℕ} {γ : ℝ}
    (hγ : 0 < γ)
    (hcol : ∀ b : ℕ → ℝ,
      (((γ * ∑ n ∈ S, b n ^ 2) : ℝ) : EReal) ≤ criticalCollaredCompleteEnergy S b)
    (htrunc : ∀ V : ℝ, criticalTruncationThreshold ≤ V → ∀ b : ℕ → ℝ,
      (((γ * ∑ n ∈ S, b n ^ 2) : ℝ) : EReal) ≤ criticalTruncatedCompleteEnergy V S b) :
    ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ ω : ℝ, 0 < ω → ω < ω₀ → ∀ b : ℕ → ℝ,
      ((ω * (γ / 2)) * ∑ n ∈ S, b n ^ 2 ≤
        autocorr (criticalCollaredSource S b) 0 -
          suzukiCriticalSourcePairing (criticalCollaredSource S b) ω ∧
      ((∃ n ∈ S, b n ≠ 0) →
        (ω * (γ / 2)) * ∑ n ∈ S, b n ^ 2 <
          autocorr (criticalCollaredSource S b) 0 -
            suzukiCriticalSourcePairing (criticalCollaredSource S b) ω)) ∧
      (∀ V : ℝ, criticalTruncationThreshold ≤ V →
        (ω * (γ / 2)) * ∑ n ∈ S, b n ^ 2 ≤
          autocorr (criticalTruncatedSource V S b) 0 -
            suzukiCriticalSourcePairing (criticalTruncatedSource V S b) ω ∧
        ((∃ n ∈ S, b n ≠ 0) →
          (ω * (γ / 2)) * ∑ n ∈ S, b n ^ 2 <
            autocorr (criticalTruncatedSource V S b) 0 -
              suzukiCriticalSourcePairing (criticalTruncatedSource V S b) ω)) := by
  have hV0_pos : 0 < criticalTruncationThreshold := by
    unfold criticalTruncationThreshold
    exact lt_of_lt_of_le (by linarith [factorialWindowLength_pos]) (le_max_left _ _)
  by_cases hS_empty : S = ∅
  · subst hS_empty
    refine ⟨1, one_pos, fun ω _ _ b => ?_⟩
    have hph : ∀ v, realPhaseCombination ∅ b v = 0 := fun _ => by simp [realPhaseCombination]
    have hgc : criticalCollaredSource ∅ b = fun _ => 0 := by
      funext x; simp [criticalCollaredSource_eq, hph]
    have hgt : ∀ V, criticalTruncatedSource V ∅ b = fun _ => 0 := fun V => by
      funext x; simp [criticalTruncatedSource, hgc]
    have hac0 : autocorr (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
      funext t; unfold autocorr; simp
    have hpair0 : suzukiCriticalSourcePairing (fun _ : ℝ => (0 : ℝ)) ω = 0 := by
      unfold suzukiCriticalSourcePairing; simp [hac0]
    simp [hgc, hgt, hac0, hpair0]
  -- Nonempty `S`: first prove a uniform threshold `ω₀ > 0` over the compact product `K`.
  set K := Icc (0 : ℝ) (1 / criticalTruncationThreshold) ×ˢ sphereS S
  have hK_cpt : IsCompact K := isCompact_Icc.prod (isCompact_sphereS S)
  have hunit_unif : ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ ω : ℝ, 0 < ω → ω < ω₀ → ∀ p ∈ K,
      ω * (γ / 2) < autocorr (paramSource S p) 0 - suzukiCriticalSourcePairing (paramSource S p) ω := by
    by_contra! hbad
    have hseq : ∀ k : ℕ, ∃ ω : ℝ, 0 < ω ∧ ω < 1 / ((k : ℝ) + 1) ∧ ∃ p ∈ K,
        autocorr (paramSource S p) 0 - suzukiCriticalSourcePairing (paramSource S p) ω ≤
          ω * (γ / 2) := fun k => hbad (1 / ((k : ℝ) + 1)) (by positivity)
    choose w hw_pos hw_lt p hp_mem hle using hseq
    obtain ⟨p₀, hp₀_mem, φ, hφ_mono, hφ_lim⟩ := hK_cpt.isSeqCompact hp_mem
    have hw_nhds : Tendsto (w ∘ φ) atTop (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall fun k => hw_pos (φ k)⟩
      refine squeeze_zero (fun k => (hw_pos (φ k)).le) (fun k => (hw_lt (φ k)).le) ?_
      have h1 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      exact h1.comp hφ_mono.tendsto_atTop
    have htoLp_lim : Tendsto
        (fun k => (memLp_paramSource S (p (φ k))).toLp (paramSource S (p (φ k))))
        atTop (𝓝 ((memLp_paramSource S p₀).toLp (paramSource S p₀))) :=
      Filter.Tendsto.comp (continuousOn_paramSource_toLp S p₀ hp₀_mem)
        (tendsto_nhdsWithin_iff.mpr ⟨hφ_lim, Eventually.of_forall fun k => hp_mem (φ k)⟩)
    have hdec_unif : ∀ k t, 0 ≤ t →
        |autocorr (paramSource S (p (φ k))) t| ≤
          criticalCollaredDecayConstant S (fun _ => 1) * Real.exp (-(3 / 2 : ℝ) * t) := by
      intro k t ht
      have hu_le : ∀ n ∈ S, |extendCoeff S (p (φ k)).2 n| ≤ 1 := fun n hn => by
        simp only [extendCoeff, dif_pos hn]
        exact abs_le.mpr ((hp_mem (φ k)).2.1 ⟨n, hn⟩)
      have hK_le := criticalCollaredDecayConstant_le_ones S hu_le
      unfold paramSource
      split_ifs with hq
      · exact (abs_autocorr_criticalCollaredSource_le S _ ht).trans
          (mul_le_mul_of_nonneg_right hK_le (Real.exp_pos _).le)
      · have hq_pos : 0 < 1 / (p (φ k)).1 := one_div_pos.mpr (not_le.mp hq)
        exact (abs_autocorr_criticalTruncatedSource_le hq_pos S _ ht).trans
          (mul_le_mul_of_nonneg_right hK_le (Real.exp_pos _).le)
    have hweil_p₀ : ((γ : ℝ) : EReal) ≤
        suzukiCriticalExtendedWeilEnergy (paramSource S p₀) := by
      have hsum1 : ∑ n ∈ S, (extendCoeff S p₀.2 n) ^ 2 = 1 := by
        rw [sum_extendCoeff_sq]; exact hp₀_mem.2.2
      unfold paramSource
      rcases hp₀_mem.1.1.eq_or_lt with hq0 | hq_pos
      · rw [if_pos (by linarith), suzukiCriticalExtendedWeilEnergy_criticalCollaredSource]
        have h := hcol (extendCoeff S p₀.2)
        rwa [hsum1, mul_one] at h
      · rw [if_neg (not_le.mpr hq_pos),
          suzukiCriticalExtendedWeilEnergy_criticalTruncatedSource (one_div_pos.mpr hq_pos)]
        have hV_ge : criticalTruncationThreshold ≤ 1 / p₀.1 := by
          have := (le_div_iff₀ hV0_pos).mp hp₀_mem.1.2
          rw [le_div_iff₀ hq_pos, mul_comm]
          exact this
        have h := htrunc (1 / p₀.1) hV_ge (extendCoeff S p₀.2)
        rwa [hsum1, mul_one] at h
    have hev := eventually_suzukiCriticalDeficit_of_exp_decay_tendsto
      (f := fun k => paramSource S (p (φ k))) (g := paramSource S p₀) (w := w ∘ φ)
      (fun k => memLp_paramSource S (p (φ k))) (memLp_paramSource S p₀)
      htoLp_lim hw_nhds (by norm_num : (1 / 2 : ℝ) < 3 / 2) hdec_unif hweil_p₀ (half_pos hγ)
    obtain ⟨k, hk⟩ := hev.exists
    have hsub : γ - γ / 2 = γ / 2 := by ring
    rw [hsub] at hk
    linarith [hle (φ k)]
  obtain ⟨ω₀, hω₀, hunif⟩ := hunit_unif
  refine ⟨ω₀, hω₀, fun ω hω0 hω_lt b => ?_⟩
  set E := ∑ n ∈ S, b n ^ 2
  have hE_nn : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rcases hE_nn.eq_or_lt with hE0 | hE_pos
  · have hb0 : ∀ n ∈ S, b n = 0 := fun n hn => by
      have hsq0 : b n ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hE0.symm n hn
      exact sq_eq_zero_iff.mp hsq0
    have hph : ∀ v, realPhaseCombination S b v = 0 := fun v =>
      Finset.sum_eq_zero fun n hn => by simp [hb0 n hn]
    have hgc : criticalCollaredSource S b = fun _ => 0 := by
      funext x; simp [criticalCollaredSource_eq, hph]
    have hgt : ∀ V, criticalTruncatedSource V S b = fun _ => 0 := fun V => by
      funext x; simp [criticalTruncatedSource, hgc]
    have hac0 : autocorr (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
      funext t; unfold autocorr; simp
    have hpair0 : suzukiCriticalSourcePairing (fun _ : ℝ => (0 : ℝ)) ω = 0 := by
      unfold suzukiCriticalSourcePairing; simp [hac0]
    have hno_nz : ¬∃ n ∈ S, b n ≠ 0 := by rintro ⟨n, hn, hne⟩; exact hne (hb0 n hn)
    simp [← hE0, hgc, hgt, hac0, hpair0, hno_nz]
  · set c := Real.sqrt E
    have hc_pos : 0 < c := Real.sqrt_pos.mpr hE_pos
    have hc_sq : c ^ 2 = E := Real.sq_sqrt hE_pos.le
    set u : S → ℝ := fun i => b i.1 / c
    have hu_sum : ∑ i : S, (u i) ^ 2 = 1 := by
      have hsum_eq : ∑ i : S, (b i.1 / c) ^ 2 = (∑ n ∈ S, b n ^ 2) / c ^ 2 := by
        simp_rw [div_pow, ← Finset.sum_div]
        congr 1
        exact Finset.sum_attach S (fun n => b n ^ 2)
      dsimp only [u]
      rw [hsum_eq, hc_sq, div_self hE_pos.ne']
    have hu_mem : u ∈ sphereS S := by
      refine ⟨fun i => ?_, hu_sum⟩
      have hsq_le1 : (u i) ^ 2 ≤ 1 := by
        rw [← hu_sum]
        exact Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
      exact abs_le.mp (abs_le_one_iff_mul_self_le_one.mpr (by simpa only [sq] using hsq_le1))
    have hb_scale : ∀ n ∈ S, b n = c * extendCoeff S u n := fun n hn => by
      simp only [extendCoeff, dif_pos hn, u]
      exact (mul_div_cancel₀ (b n) hc_pos.ne').symm
    -- Collared branch (`q = 0`):
    have hcol_strict : (ω * (γ / 2)) * E <
        autocorr (criticalCollaredSource S b) 0 -
          suzukiCriticalSourcePairing (criticalCollaredSource S b) ω := by
      have hp0_mem : ((0 : ℝ), u) ∈ K := ⟨⟨le_rfl, by positivity⟩, hu_mem⟩
      have hu0 := hunif ω hω0 hω_lt (0, u) hp0_mem
      simp only [paramSource, if_pos le_rfl] at hu0
      rw [criticalCollaredSource_congr_scale c hb_scale, autocorr_const_mul,
        suzukiCriticalSourcePairing_const_mul, hc_sq, ← mul_sub]
      nlinarith [mul_lt_mul_of_pos_left hu0 hE_pos]
    refine ⟨⟨hcol_strict.le, fun _ => hcol_strict⟩, fun V hV => ?_⟩
    -- Truncated branch (`q = 1 / V > 0`):
    have hV_pos : 0 < V := lt_of_lt_of_le hV0_pos hV
    have hq_mem : ((1 / V : ℝ), u) ∈ K :=
      ⟨⟨by positivity, one_div_le_one_div_of_le hV0_pos hV⟩, hu_mem⟩
    have huV := hunif ω hω0 hω_lt (1 / V, u) hq_mem
    have hq_not_le : ¬(1 / V ≤ 0) := not_le.mpr (by positivity)
    simp only [paramSource, if_neg hq_not_le, one_div_one_div] at huV
    have htrunc_strict : (ω * (γ / 2)) * E <
        autocorr (criticalTruncatedSource V S b) 0 -
          suzukiCriticalSourcePairing (criticalTruncatedSource V S b) ω := by
      rw [criticalTruncatedSource_congr_scale V c hb_scale, autocorr_const_mul,
        suzukiCriticalSourcePairing_const_mul, hc_sq, ← mul_sub]
      nlinarith [mul_lt_mul_of_pos_left huV hE_pos]
    exact ⟨htrunc_strict.le, fun _ => htrunc_strict⟩

/-- **Unconditional Simultaneous Moving-Aperture and Infinite-Head Suzuki Deficit on High Dyadic
Blocks.**
Above an absolute scale `M₀`, every dyadic block `DyadicScaleBlock S M` (`M ≥ M₀`) admits a single
shift threshold `ω₀ > 0` independent of `V` and `b` governing all `V ≥ criticalTruncationThreshold`
and `criticalCollaredSource S b` simultaneously. -/
theorem exists_dyadic_uniform_movingAperture_suzukiDeficit :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ S : Finset ℕ, DyadicScaleBlock S M →
      let s := min criticalTruncatedArchLogSlope criticalCollarArchLogSlope
      0 < s / 4 * Real.log M ∧
      ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ ω : ℝ, 0 < ω → ω < ω₀ → ∀ b : ℕ → ℝ, (∃ n ∈ S, b n ≠ 0) →
        (ω * (s / 8 * Real.log M)) * ∑ n ∈ S, b n ^ 2 <
          autocorr (criticalCollaredSource S b) 0 -
            suzukiCriticalSourcePairing (criticalCollaredSource S b) ω ∧
        ∀ V : ℝ, criticalTruncationThreshold ≤ V →
          (ω * (s / 8 * Real.log M)) * ∑ n ∈ S, b n ^ 2 <
            autocorr (criticalTruncatedSource V S b) 0 -
              suzukiCriticalSourcePairing (criticalTruncatedSource V S b) ω := by
  set s := min criticalTruncatedArchLogSlope criticalCollarArchLogSlope
  have hs : 0 < s := lt_min criticalTruncatedArchLogSlope_pos criticalCollarArchLogSlope_pos
  set Kt := criticalTruncatedArchLogSlope * criticalTruncatedArchLogOffset +
    criticalTruncatedChannelConstant
  set Kc := criticalCollarArchLogSlope * criticalCollarArchLogOffset +
    criticalCollaredChannelConstant
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp ((hlog.eventually_gt_atTop
    (max (4 * Kt / criticalTruncatedArchLogSlope)
      (4 * Kc / criticalCollarArchLogSlope))).and (eventually_ge_atTop 2))
  refine ⟨M₀, fun M hM S hS => ?_⟩
  dsimp only
  obtain ⟨hlogM, hM2⟩ := hM₀ M hM
  have hlogM_pos : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  set γ := s / 4 * Real.log M
  have hγ : 0 < γ := by positivity
  have hcol : ∀ b : ℕ → ℝ,
      (((γ * ∑ n ∈ S, b n ^ 2) : ℝ) : EReal) ≤ criticalCollaredCompleteEnergy S b := fun b => by
    have hE : 0 ≤ ∑ n ∈ S, b n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hs_le : s ≤ criticalCollarArchLogSlope := min_le_right _ _
    have hKc_lt : Kc < criticalCollarArchLogSlope / 4 * Real.log M := by
      have := (div_lt_iff₀ criticalCollarArchLogSlope_pos).mp
        ((le_max_right _ _).trans_lt hlogM)
      linarith
    have hgap : γ ≤ criticalCollarArchLogSlope * (Real.log M - criticalCollarArchLogOffset) -
        criticalCollaredChannelConstant := by
      unfold γ Kc at *; nlinarith
    exact (EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_right hgap hE)).trans
      (criticalCollaredCompleteEnergy_ge S b hM2 hS)
  have htrunc : ∀ V : ℝ, criticalTruncationThreshold ≤ V → ∀ b : ℕ → ℝ,
      (((γ * ∑ n ∈ S, b n ^ 2) : ℝ) : EReal) ≤ criticalTruncatedCompleteEnergy V S b :=
    fun V hV b => by
      have hE : 0 ≤ ∑ n ∈ S, b n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hs_le : s ≤ criticalTruncatedArchLogSlope := min_le_left _ _
      have hKt_lt : Kt < criticalTruncatedArchLogSlope / 4 * Real.log M := by
        have := (div_lt_iff₀ criticalTruncatedArchLogSlope_pos).mp
          ((le_max_left _ _).trans_lt hlogM)
        linarith
      have hgap : γ ≤ criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) -
          criticalTruncatedChannelConstant := by
        unfold γ Kt at *; nlinarith
      exact (EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_right hgap hE)).trans
        (criticalTruncatedCompleteEnergy_ge S b hM2 hS hV)
  obtain ⟨ω₀, hω₀, hshift⟩ := exists_suzukiCriticalUniformShift_of_collared_family hγ hcol htrunc
  refine ⟨hγ, ω₀, hω₀, fun ω hω0 hω_lt b hb => ?_⟩
  obtain ⟨⟨_, hc_lt⟩, ht_all⟩ := hshift ω hω0 hω_lt b
  have hhalf : γ / 2 = s / 8 * Real.log M := by unfold γ; ring
  rw [hhalf] at hc_lt
  refine ⟨hc_lt hb, fun V hV => ?_⟩
  have ht_lt := (ht_all V hV).2 hb
  rwa [hhalf] at ht_lt

/-- **Unconditional Simultaneous Moving-Aperture and Infinite-Head Suzuki Deficit on Polynomial
Scale Windows `[M, LM]`.** -/
theorem exists_polynomial_window_uniform_movingAperture_suzukiDeficit :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L : ℕ, 1 ≤ L → (L : ℝ) ≤ (M : ℝ) ^ δ →
      ∀ S : Finset ℕ, ScaleWindow S M L →
        let s := min criticalTruncatedArchLogSlope criticalCollarArchLogSlope
        0 < s / 4 * Real.log M ∧
        ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ ω : ℝ, 0 < ω → ω < ω₀ → ∀ b : ℕ → ℝ, (∃ n ∈ S, b n ≠ 0) →
          (ω * (s / 8 * Real.log M)) * ∑ n ∈ S, b n ^ 2 <
            autocorr (criticalCollaredSource S b) 0 -
              suzukiCriticalSourcePairing (criticalCollaredSource S b) ω ∧
          ∀ V : ℝ, criticalTruncationThreshold ≤ V →
            (ω * (s / 8 * Real.log M)) * ∑ n ∈ S, b n ^ 2 <
              autocorr (criticalTruncatedSource V S b) 0 -
                suzukiCriticalSourcePairing (criticalTruncatedSource V S b) ω := by
  set s := min criticalTruncatedArchLogSlope criticalCollarArchLogSlope
  have hs : 0 < s := lt_min criticalTruncatedArchLogSlope_pos criticalCollarArchLogSlope_pos
  set W := criticalTruncatedWindowPrimeSlope
  have hW : 0 ≤ W := criticalTruncatedWindowPrimeSlope_nonneg
  set δ := s / (4 * (W + 1))
  have hδ : 0 < δ := by positivity
  set Kt := criticalTruncatedArchLogSlope * criticalTruncatedArchLogOffset +
    criticalTruncatedWindowBaseConstant + 6 * W
  set Kc := criticalCollarArchLogSlope * criticalCollarArchLogOffset +
    criticalCollaredWindowBaseConstant + 6 * W
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp ((hlog.eventually_gt_atTop
    (max (4 * Kt / criticalTruncatedArchLogSlope)
      (4 * Kc / criticalCollarArchLogSlope))).and (eventually_ge_atTop 2))
  refine ⟨δ, hδ, M₀, fun M hM L hL hLM S hS => ?_⟩
  dsimp only
  obtain ⟨hlogM, hM2⟩ := hM₀ M hM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hlogL : Real.log L ≤ δ * Real.log M := by
    have := Real.log_le_log hL0 hLM
    rwa [Real.log_rpow hMpos] at this
  have hlogM_pos : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hWlogL : 2 * W * Real.log L ≤ s / 2 * Real.log M := by
    calc 2 * W * Real.log L ≤ 2 * W * (δ * Real.log M) := by gcongr
      _ = s / 2 * Real.log M * (W / (W + 1)) := by unfold δ; field_simp; ring
      _ ≤ s / 2 * Real.log M * 1 := by gcongr; rw [div_le_one (by linarith)]; linarith
      _ = s / 2 * Real.log M := by ring
  set γ := s / 4 * Real.log M
  have hγ : 0 < γ := by positivity
  have hcol : ∀ b : ℕ → ℝ,
      (((γ * ∑ n ∈ S, b n ^ 2) : ℝ) : EReal) ≤ criticalCollaredCompleteEnergy S b := fun b => by
    have hE : 0 ≤ ∑ n ∈ S, b n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hs_le : s ≤ criticalCollarArchLogSlope := min_le_right _ _
    have hKc_lt : Kc < criticalCollarArchLogSlope / 4 * Real.log M := by
      have := (div_lt_iff₀ criticalCollarArchLogSlope_pos).mp
        ((le_max_right _ _).trans_lt hlogM)
      linarith
    have hgap : γ ≤ criticalCollarArchLogSlope * (Real.log M - criticalCollarArchLogOffset) -
        criticalCollaredWindowBaseConstant - 2 * W * (3 + Real.log L) := by
      unfold γ Kc at *; nlinarith
    exact (EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_right hgap hE)).trans
      (criticalCollaredCompleteEnergy_ge_of_window S b hM2 hL hS)
  have htrunc : ∀ V : ℝ, criticalTruncationThreshold ≤ V → ∀ b : ℕ → ℝ,
      (((γ * ∑ n ∈ S, b n ^ 2) : ℝ) : EReal) ≤ criticalTruncatedCompleteEnergy V S b :=
    fun V hV b => by
      have hE : 0 ≤ ∑ n ∈ S, b n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hs_le : s ≤ criticalTruncatedArchLogSlope := min_le_left _ _
      have hKt_lt : Kt < criticalTruncatedArchLogSlope / 4 * Real.log M := by
        have := (div_lt_iff₀ criticalTruncatedArchLogSlope_pos).mp
          ((le_max_left _ _).trans_lt hlogM)
        linarith
      have hgap : γ ≤ criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) -
          criticalTruncatedWindowBaseConstant - 2 * W * (3 + Real.log L) := by
        unfold γ Kt at *; nlinarith
      exact (EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_right hgap hE)).trans
        (criticalTruncatedCompleteEnergy_ge_of_window S b hM2 hL hS hV)
  obtain ⟨ω₀, hω₀, hshift⟩ := exists_suzukiCriticalUniformShift_of_collared_family hγ hcol htrunc
  refine ⟨hγ, ω₀, hω₀, fun ω hω0 hω_lt b hb => ?_⟩
  obtain ⟨⟨_, hc_lt⟩, ht_all⟩ := hshift ω hω0 hω_lt b
  have hhalf : γ / 2 = s / 8 * Real.log M := by unfold γ; ring
  rw [hhalf] at hc_lt
  refine ⟨hc_lt hb, fun V hV => ?_⟩
  have ht_lt := (ht_all V hV).2 hb
  rwa [hhalf] at ht_lt

/-- **Unconditional Simultaneous Moving-Aperture and Infinite-Head Suzuki Deficit Across
Arbitrary-Depth Lacunary Block Unions.** -/
theorem exists_lacunary_uniform_movingAperture_suzukiDeficit :
    ∃ M₀ : ℕ, ∀ (J : ℕ) (M : ℕ → ℕ) (S : ℕ → Finset ℕ), IsLacunaryBlockFamily J M S →
      M₀ ≤ M 0 →
        let s := min criticalTruncatedArchLogSlope criticalCollarArchLogSlope
        0 < s / 4 * Real.log (M 0) ∧
        ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ ω : ℝ, 0 < ω → ω < ω₀ → ∀ b : ℕ → ℝ,
          (∃ n ∈ (Finset.range J).biUnion S, b n ≠ 0) →
            (ω * (s / 8 * Real.log (M 0))) * ∑ n ∈ (Finset.range J).biUnion S, b n ^ 2 <
              autocorr (criticalCollaredSource ((Finset.range J).biUnion S) b) 0 -
                suzukiCriticalSourcePairing
                  (criticalCollaredSource ((Finset.range J).biUnion S) b) ω ∧
            ∀ V : ℝ, criticalTruncationThreshold ≤ V →
              (ω * (s / 8 * Real.log (M 0))) * ∑ n ∈ (Finset.range J).biUnion S, b n ^ 2 <
                autocorr (criticalTruncatedSource V ((Finset.range J).biUnion S) b) 0 -
                  suzukiCriticalSourcePairing
                    (criticalTruncatedSource V ((Finset.range J).biUnion S) b) ω := by
  set s := min criticalTruncatedArchLogSlope criticalCollarArchLogSlope
  have hs : 0 < s := lt_min criticalTruncatedArchLogSlope_pos criticalCollarArchLogSlope_pos
  set Kt := criticalTruncatedArchLogSlope * criticalTruncatedArchLogOffset +
    lacunaryChannelConstant
  set Kc := criticalCollarArchLogSlope * criticalCollarArchLogOffset +
    criticalCollaredLacunaryChannelConstant
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp (hlog.eventually_gt_atTop
    (max (4 * Kt / criticalTruncatedArchLogSlope) (4 * Kc / criticalCollarArchLogSlope)))
  refine ⟨M₀, fun J M S h hM => ?_⟩
  dsimp only
  set T := (Finset.range J).biUnion S
  have hlogM := hM₀ (M 0) hM
  have hM3 : 3 ≤ M 0 := h.1
  have hlogM_pos : 0 < Real.log (M 0) := Real.log_pos (by exact_mod_cast (show 1 < M 0 by omega))
  set γ := s / 4 * Real.log (M 0)
  have hγ : 0 < γ := by positivity
  have hcol : ∀ b : ℕ → ℝ,
      (((γ * ∑ n ∈ T, b n ^ 2) : ℝ) : EReal) ≤ criticalCollaredCompleteEnergy T b := fun b => by
    have hE : 0 ≤ ∑ n ∈ T, b n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hs_le : s ≤ criticalCollarArchLogSlope := min_le_right _ _
    have hKc_lt : Kc < criticalCollarArchLogSlope / 4 * Real.log (M 0) := by
      have := (div_lt_iff₀ criticalCollarArchLogSlope_pos).mp
        ((le_max_right _ _).trans_lt hlogM)
      linarith
    have hgap : γ ≤ criticalCollarArchLogSlope * (Real.log (M 0) - criticalCollarArchLogOffset) -
        criticalCollaredLacunaryChannelConstant := by
      unfold γ Kc at *; nlinarith
    exact (EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_right hgap hE)).trans
      (criticalCollaredCompleteEnergy_ge_of_lacunary h b)
  have htrunc : ∀ V : ℝ, criticalTruncationThreshold ≤ V → ∀ b : ℕ → ℝ,
      (((γ * ∑ n ∈ T, b n ^ 2) : ℝ) : EReal) ≤ criticalTruncatedCompleteEnergy V T b :=
    fun V hV b => by
      have hE : 0 ≤ ∑ n ∈ T, b n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hs_le : s ≤ criticalTruncatedArchLogSlope := min_le_left _ _
      have hKt_lt : Kt < criticalTruncatedArchLogSlope / 4 * Real.log (M 0) := by
        have := (div_lt_iff₀ criticalTruncatedArchLogSlope_pos).mp
          ((le_max_left _ _).trans_lt hlogM)
        linarith
      have hgap : γ ≤
          criticalTruncatedArchLogSlope * (Real.log (M 0) - criticalTruncatedArchLogOffset) -
            lacunaryChannelConstant := by
        unfold γ Kt at *; nlinarith
      exact (EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_right hgap hE)).trans
        (criticalTruncatedCompleteEnergy_ge_of_lacunary h b hV)
  obtain ⟨ω₀, hω₀, hshift⟩ := exists_suzukiCriticalUniformShift_of_collared_family hγ hcol htrunc
  refine ⟨hγ, ω₀, hω₀, fun ω hω0 hω_lt b hb => ?_⟩
  obtain ⟨⟨_, hc_lt⟩, ht_all⟩ := hshift ω hω0 hω_lt b
  have hhalf : γ / 2 = s / 8 * Real.log (M 0) := by unfold γ; ring
  rw [hhalf] at hc_lt
  refine ⟨hc_lt hb, fun V hV => ?_⟩
  have ht_lt := (ht_all V hV).2 hb
  rwa [hhalf] at ht_lt

end
end RHTower
