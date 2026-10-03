import GaloisForLFunctions.RHTower.RoutePNativeCriticalSquareEnergy
import GaloisForLFunctions.RHTower.RoutePCoprimeSquareNative
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The complete native coprime history carries infinite negative work

The admitted damped balance contains both the endpoint square and every
coprime cross term. A finite negative-part budget would admit each damped
square and bound every undamped partial square energy, contradicting the
literal native energy escape. No separate square admission is assumed.
This is a zero-damping obstruction, not a positive-damping payment law.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace RHTower

/-- Complete native coprime cross work in the critical logarithmic measure. -/
def routePNativeCriticalCoprimeWork (t : ℝ) : ℝ :=
  Real.exp (-t) * logarithmicCoprimeCross routePCoprimeNativeProfile t

/-- The negative part retains every native coprime pair before taking its sign. -/
def routePNativeNegativeCoprimeWork (t : ℝ) : ℝ :=
  max (-routePNativeCriticalCoprimeWork t) 0

private def nativeCombined (t : ℝ) : ℝ :=
  Real.exp (-t) * (routePCoprimeSquareSource (Real.exp (-t))).re

private theorem balance_eq {t : ℝ} (ht : 0 ≤ t) :
    nativeCombined t = routePNativeCriticalProfile t ^ 2 +
      routePNativeCriticalCoprimeWork t := by
  rw [nativeCombined, routePCoprimeSquareSource_eq_nativeSquare_add_cross ht,
    Complex.ofReal_re, routePNativeCriticalProfile, routePNativeCriticalCoprimeWork]
  ring

private theorem negative_nonneg (t : ℝ) : 0 ≤ routePNativeNegativeCoprimeWork t :=
  le_max_right _ _

private theorem native_measurable : Measurable routePNativeCriticalProfile :=
  (Real.measurable_exp.comp measurable_id.neg).mul
    (measurable_mobiusDivisorFullHead.comp Real.measurable_exp)

private theorem source_zero {y : ℝ} (hy : 1 ≤ y) : routePCoprimeSquareSource y = 0 := by
  unfold routePCoprimeSquareSource pmWeightedDilationSource
  have hz (n : ℕ) : ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
      (routePCoprimeSquareWeight ((n : ℝ) * y) : ℂ) = 0 := by
    by_cases hn : n = 0
    · simp [hn]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hny : 1 ≤ (n : ℝ) * y :=
        hy.trans (by simpa using mul_le_mul_of_nonneg_right hn1 (by linarith : 0 ≤ y))
      simp [routePCoprimeSquareWeight_eq_zero_of_one_le hny]
  simp only [hz, tsum_zero]

private theorem integrand_re (ε y : ℝ) (hy : 0 < y) :
    ((y : ℂ) ^ ((1 + (ε : ℂ)) - 1) • routePCoprimeSquareSource y).re =
      y ^ ε * (routePCoprimeSquareSource y).re := by
  rw [show (1 + (ε : ℂ)) - 1 = (ε : ℂ) by ring, smul_eq_mul,
    ← Complex.ofReal_cpow hy.le]
  simp

private theorem real_mellin {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun y : ℝ => y ^ ε * (routePCoprimeSquareSource y).re) (Ioi 0) ∧
    (∫ y in Ioi (0 : ℝ), y ^ ε * (routePCoprimeSquareSource y).re) =
      (mellin routePCoprimeSquareSource (1 + (ε : ℂ))).re := by
  have hs : 1 < ((1 : ℂ) + (ε : ℂ)).re := by simpa using hε
  have hm := (routePCoprimeSquareSource_hasMellin hs).1
  constructor
  · apply hm.re.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    simpa only [RCLike.re_eq_complex_re] using integrand_re ε y hy
  · have h := integral_re hm
    simp only [RCLike.re_eq_complex_re] at h
    unfold mellin
    rw [← h]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (integrand_re ε y hy).symm

private theorem combined_admission_and_budget {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => Real.exp (-ε * t) * nativeCombined t) (Ioi 0) ∧
    (∫ t in Ioi (0 : ℝ), Real.exp (-ε * t) * nativeCombined t) =
      (mellin routePCoprimeSquareSource (1 + (ε : ℂ))).re := by
  let f : ℝ → ℝ := fun y => y ^ ε * (routePCoprimeSquareSource y).re
  have himg : (fun t : ℝ => Real.exp (-t)) '' Ioi 0 = Ioo 0 1 := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht : 0 < t := ht
      exact ⟨Real.exp_pos _, by simpa using Real.exp_lt_exp.mpr (show -t < 0 by linarith)⟩
    · rintro ⟨hy0, hy1⟩
      exact ⟨-Real.log y, neg_pos.mpr (Real.log_neg hy0 hy1), by simp [Real.exp_log hy0]⟩
  have hd (t : ℝ) (_ : t ∈ Ioi (0 : ℝ)) :
      HasDerivWithinAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) (Ioi 0) t := by
    simpa using ((hasDerivAt_id t).neg.exp).hasDerivWithinAt
  have hinj : InjOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) :=
    fun _ _ _ _ h => neg_injective (Real.exp_injective h)
  have hw (t : ℝ) : Real.exp (-t) * f (Real.exp (-t)) =
      Real.exp (-ε * t) * nativeCombined t := by
    have he : Real.exp (-t) ^ ε = Real.exp (-ε * t) := by
      rw [← Real.exp_mul]
      congr 1
      ring
    dsimp only [f, nativeCombined]
    rw [he]
    ring
  have hr := real_mellin hε
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi hd hinj f
  rw [himg] at hi
  have hj := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj f
  rw [himg] at hj
  have hcut : (∫ y in Ioi (0 : ℝ), f y) = ∫ y in Ioo (0 : ℝ) 1, f y := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioo_subset_Ioi_self
    intro y hy
    have hy1 : 1 ≤ y := le_of_not_gt (fun h => hy.2 ⟨hy.1, h⟩)
    simp [f, source_zero hy1]
  refine ⟨?_, ?_⟩
  · simpa only [abs_neg, abs_of_pos (Real.exp_pos _), smul_eq_mul, hw] using
      hi.mp (hr.1.mono_set Ioo_subset_Ioi_self)
  · have hj' : (∫ y in Ioo (0 : ℝ) 1, f y) =
        ∫ t in Ioi (0 : ℝ), Real.exp (-ε * t) * nativeCombined t := by
      simpa only [abs_neg, abs_of_pos (Real.exp_pos _), smul_eq_mul, hw] using hj
    exact hj'.symm.trans (hcut.symm.trans hr.2)

private theorem damped_square_budget
    (hN : IntegrableOn routePNativeNegativeCoprimeWork (Ioi 0))
    {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t => Real.exp (-ε * t) * routePNativeCriticalProfile t ^ 2) (Ioi 0) ∧
    (∫ t in Ioi (0 : ℝ), Real.exp (-ε * t) * routePNativeCriticalProfile t ^ 2) ≤
      (mellin routePCoprimeSquareSource (1 + (ε : ℂ))).re +
        ∫ t in Ioi (0 : ℝ), routePNativeNegativeCoprimeWork t := by
  have hA := combined_admission_and_budget hε
  have hupper (t : ℝ) (ht : 0 < t) :
      Real.exp (-ε * t) * routePNativeCriticalProfile t ^ 2 ≤
        Real.exp (-ε * t) * nativeCombined t + routePNativeNegativeCoprimeWork t := by
    have he : Real.exp (-ε * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hn : -routePNativeCriticalCoprimeWork t ≤ routePNativeNegativeCoprimeWork t :=
      le_max_left _ _
    have h1 := mul_le_mul_of_nonneg_left hn (Real.exp_pos (-ε * t)).le
    have h2 := mul_le_mul_of_nonneg_right he (negative_nonneg t)
    rw [balance_eq ht.le]
    nlinarith
  have hm : AEStronglyMeasurable
      (fun t => Real.exp (-ε * t) * routePNativeCriticalProfile t ^ 2)
      (volume.restrict (Ioi 0)) :=
    ((by fun_prop : Continuous (fun t : ℝ => Real.exp (-ε * t))).measurable.mul
      (native_measurable.pow_const 2)).aestronglyMeasurable
  have hi : IntegrableOn
      (fun t => Real.exp (-ε * t) * routePNativeCriticalProfile t ^ 2) (Ioi 0) := by
    apply (hA.1.add hN).mono' hm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    exact hupper t ht
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ),
        Real.exp (-ε * t) * nativeCombined t + routePNativeNegativeCoprimeWork t := by
      apply integral_mono_ae hi (hA.1.add hN)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hupper t ht
    _ = _ := by rw [integral_add hA.1 hN, hA.2]

private theorem partial_square_limit (U : ℝ) :
    Tendsto (fun ε : ℝ => ∫ t in Ioc (0 : ℝ) U,
      Real.exp (-ε * t) * routePNativeCriticalProfile t ^ 2)
      (𝓝[>] 0) (𝓝 (∫ t in Ioc (0 : ℝ) U, routePNativeCriticalProfile t ^ 2)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun t => routePNativeCriticalProfile t ^ 2)
  · exact Eventually.of_forall fun ε =>
      ((by fun_prop : Continuous (fun t : ℝ => Real.exp (-ε * t))).measurable.mul
        (native_measurable.pow_const 2)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have he : Real.exp (-ε * t) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have hε : 0 < ε := hε
      nlinarith [ht.1])
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    simpa using mul_le_mul_of_nonneg_right he (sq_nonneg (routePNativeCriticalProfile t))
  · exact integrableOn_routePNativeCriticalProfile_sq_Ioc U
  · filter_upwards with t
    have hε : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have he := (Real.continuous_exp.continuousAt.tendsto.comp (hε.neg.mul_const t)).mul_const
      (routePNativeCriticalProfile t ^ 2)
    simpa using he

/-- The literal native coprime work has infinite negative mass at zero damping. -/
theorem not_integrableOn_routePNativeNegativeCoprimeWork :
    ¬ IntegrableOn routePNativeNegativeCoprimeWork (Ioi 0) := by
  intro hN
  let N : ℝ := ∫ t in Ioi (0 : ℝ), routePNativeNegativeCoprimeWork t
  obtain ⟨U, hU, hbig⟩ := routePNativeCritical_square_energy_cofinally_unbounded N 0
  have hlimit := (Complex.continuous_re.tendsto (0 : ℂ)).comp
    mellin_routePCoprimeSquareSource_tendsto_zero
  simp only [Function.comp_def, Complex.zero_re] at hlimit
  have hbound : (∫ t in Ioc (0 : ℝ) U, routePNativeCriticalProfile t ^ 2) ≤ N := by
    apply le_of_tendsto_of_tendsto (partial_square_limit U)
      (by simpa using hlimit.add_const N)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε : 0 < ε := hε
    have hbudget := damped_square_budget hN hε
    apply le_trans (setIntegral_mono_set hbudget.1 ?_ ?_) hbudget.2
    · exact Eventually.of_forall fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
    · exact Eventually.of_forall fun t ht => ht.1
  rw [intervalIntegral.integral_of_le hU] at hbig
  exact (not_lt_of_ge hbound) hbig

private theorem negative_interval_integrable (U : ℝ) :
    IntegrableOn routePNativeNegativeCoprimeWork (Ioc 0 U) := by
  have hB1 := (combined_admission_and_budget (by norm_num : (0 : ℝ) < 1)).1
  have he : AEStronglyMeasurable Real.exp (volume.restrict (Ioc (0 : ℝ) U)) :=
    Real.continuous_exp.aestronglyMeasurable
  have hBmul := (hB1.mono_set Ioc_subset_Ioi_self).bdd_mul he (c := Real.exp U) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr ht.2)
  have hB : IntegrableOn nativeCombined (Ioc 0 U) := by
    apply hBmul.congr
    filter_upwards with t
    rw [← mul_assoc, ← Real.exp_add]
    simp
  have hC : IntegrableOn routePNativeCriticalCoprimeWork (Ioc 0 U) := by
    apply (hB.sub (integrableOn_routePNativeCriticalProfile_sq_Ioc U)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    change nativeCombined t - routePNativeCriticalProfile t ^ 2 = _
    rw [balance_eq ht.1.le]
    ring
  apply ((hC.norm.sub hC).div_const 2).congr
  filter_upwards with t
  change (‖routePNativeCriticalCoprimeWork t‖ - routePNativeCriticalCoprimeWork t) / 2 = _
  rw [Real.norm_eq_abs, routePNativeNegativeCoprimeWork]
  by_cases ht : 0 ≤ routePNativeCriticalCoprimeWork t
  · rw [abs_of_nonneg ht, max_eq_right (neg_nonpos.mpr ht)]
    ring
  · have ht' := (lt_of_not_ge ht).le
    rw [abs_of_nonpos ht', max_eq_left (neg_nonneg.mpr ht')]
    ring

/-- Positive survivor: complete native negative work exceeds every finite budget. -/
theorem routePNativeNegativeCoprimeWork_cofinally_unbounded (B T : ℝ) :
    ∃ U : ℝ, T ≤ U ∧ B < ∫ t in (0 : ℝ)..U, routePNativeNegativeCoprimeWork t := by
  by_contra hn
  push Not at hn
  apply not_integrableOn_routePNativeNegativeCoprimeWork
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded B 0
    negative_interval_integrable tendsto_id
  filter_upwards [eventually_ge_atTop T] with U hU
  simpa only [Real.norm_eq_abs, abs_of_nonneg (negative_nonneg _)] using hn U hU

/-- Actual coprime cross terms remain negative arbitrarily late. -/
theorem routePNativeCoprimeCross_negative_beyond (T : ℝ) :
    ∃ t : ℝ, T < t ∧ logarithmicCoprimeCross routePCoprimeNativeProfile t < 0 := by
  by_contra hn
  push Not at hn
  apply not_integrableOn_routePNativeNegativeCoprimeWork
  apply (negative_interval_integrable (max T 0)).of_ae_sdiff_eq_zero
    measurableSet_Ioi.nullMeasurableSet
  filter_upwards with t ht
  have htU : max T 0 < t := lt_of_not_ge (fun h => ht.2 ⟨ht.1, h⟩)
  have hC : 0 ≤ routePNativeCriticalCoprimeWork t :=
    mul_nonneg (Real.exp_pos _).le (hn t ((le_max_left T 0).trans_lt htU))
  exact max_eq_right (neg_nonpos.mpr hC)

end RHTower
