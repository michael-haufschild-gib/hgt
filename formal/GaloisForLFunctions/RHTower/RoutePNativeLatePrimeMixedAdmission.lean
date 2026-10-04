import GaloisForLFunctions.RHTower.RoutePNativeCriticalL1Nonintegrability
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalMovingHeadAsymptotic
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalCorrelationRegularity
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Absolute admission of the complete late-prime mixed work

The actual late-prime increment has a nonzero inverse-square tail. Its
mixed work therefore has exactly the same absolute-admission class at
infinity as the native profile with weight `exp((1/2-ε)t)/t²`.
For `ε < 1/2` this is unconditionally nonintegrable, including positive
damping. Separate absolute payment of this mixed term cannot close RP.
The joint signed square remains the open obligation.
-/

noncomputable section
open MeasureTheory Set Filter Topology Asymptotics

namespace RHTower

/-- Complete prime increment with the literal moving cutoff. -/
def routePLatePrimeIncrement (t : ℝ) : ℝ :=
  ∑ p ∈ criticalLogLatePrimes t, criticalAbelLogProfile (t - Real.log p) / p

/-- Native parent/late-prime mixed work in the square-energy measure. -/
def routePNativeLatePrimeMixedWork (ε t : ℝ) : ℝ :=
  Real.exp ((1 - ε) * t) * criticalAbelLogProfile t * routePLatePrimeIncrement t

theorem measurable_routePLatePrimeIncrement : Measurable routePLatePrimeIncrement := by
  classical
  let F : ℝ × ℕ → ℝ := fun z => ∑ p ∈ Nat.primesLE z.2,
    if z.1 / 2 < Real.log p then criticalAbelLogProfile (z.1 - Real.log p) / p else 0
  have hm : Measurable F := by
    apply measurable_from_prod_countable_left
    intro n
    dsimp only [F]
    apply Finset.measurable_sum
    intro p _
    exact Measurable.ite
      (measurableSet_lt (measurable_id.div_const 2) measurable_const)
      ((measurable_criticalAbelLogProfile.comp
        (measurable_id.sub_const (Real.log p))).div_const (p : ℝ)) measurable_const
  have heq : routePLatePrimeIncrement = fun t => F (t, ⌊Real.exp t⌋₊) := by
    funext t
    simp only [routePLatePrimeIncrement, criticalLogLatePrimes, Finset.sum_filter, F]
  rw [heq]
  exact hm.comp (measurable_id.prodMk Real.measurable_exp.nat_floor)

/-- The nonzero signed coefficient is inherited from the actual source moment. -/
theorem tendsto_routePLatePrimeIncrement_scaled :
    Tendsto (fun t : ℝ => t ^ 2 * routePLatePrimeIncrement t) atTop
      (𝓝 (-(divisorHarmonicBoundary / 3))) := by
  have h := tendsto_criticalMovingPrimeHead_log_scaled.sub
    tendsto_criticalAbelLogProfile_quadratic_zero
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [criticalMovingPrimeHead_exp_eq_log_late_sum ht]
  dsimp only [routePLatePrimeIncrement]
  ring

theorem routePNativeCriticalProfile_eq_exp_mul_logProfile (t : ℝ) :
    routePNativeCriticalProfile t = Real.exp (t / 2) * criticalAbelLogProfile t := by
  unfold routePNativeCriticalProfile criticalAbelLogProfile
  rw [mobiusDivisorFullHead_eq_criticalContinuousAbel, ← mul_assoc, ← Real.exp_add,
    show t / 2 + -(3 / 2 : ℝ) * t = -t by ring]

theorem continuous_routePNativeCriticalProfile : Continuous routePNativeCriticalProfile := by
  have heq : routePNativeCriticalProfile =
      fun t => Real.exp (t / 2) * criticalAbelLogProfile t :=
    funext routePNativeCriticalProfile_eq_exp_mul_logProfile
  rw [heq]
  exact (Real.continuous_exp.comp (continuous_id.div_const 2)).mul
    continuous_criticalAbelLogProfile

private theorem native_mixed_weight (ε t : ℝ) :
    Real.exp ((1 - ε) * t) * criticalAbelLogProfile t =
      Real.exp ((1 / 2 - ε) * t) * routePNativeCriticalProfile t := by
  rw [routePNativeCriticalProfile_eq_exp_mul_logProfile, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Exact asymptotic absolute-size classification, retaining the native profile. -/
theorem routePNativeLatePrimeMixedWork_isTheta (ε : ℝ) :
    routePNativeLatePrimeMixedWork ε =Θ[atTop]
      (fun t => Real.exp ((1 / 2 - ε) * t) * routePNativeCriticalProfile t / t ^ 2) := by
  have hratio : Tendsto (fun t : ℝ => routePLatePrimeIncrement t / (1 / t ^ 2))
      atTop (𝓝 (-(divisorHarmonicBoundary / 3))) := by
    simpa only [div_div_eq_mul_div, div_one, mul_comm] using tendsto_routePLatePrimeIncrement_scaled
  have hJ := isTheta_of_div_tendsto_nhds_ne_zero hratio
    (neg_ne_zero.mpr (div_ne_zero divisorHarmonicBoundary_pos.ne' (by norm_num)))
  have hm := (isTheta_refl
    (fun t => Real.exp ((1 - ε) * t) * criticalAbelLogProfile t) atTop).mul hJ.symm
  change routePNativeLatePrimeMixedWork ε =Θ[atTop]
    (fun t => (Real.exp ((1 - ε) * t) * criticalAbelLogProfile t) * (1 / t ^ 2)) at hm
  apply hm.trans_eventuallyEq
  exact Eventually.of_forall fun t => by
    dsimp only
    rw [native_mixed_weight]
    ring

/-- Positive survivor: exact equivalence of absolute admission at infinity. -/
theorem routePNativeLatePrimeMixedWork_integrableAtFilter_iff (ε : ℝ) :
    IntegrableAtFilter (routePNativeLatePrimeMixedWork ε) atTop volume ↔
      IntegrableAtFilter
        (fun t => Real.exp ((1 / 2 - ε) * t) * routePNativeCriticalProfile t / t ^ 2)
        atTop volume := by
  have hm : Measurable (routePNativeLatePrimeMixedWork ε) :=
    (((measurable_const.mul measurable_id).exp).mul
      measurable_criticalAbelLogProfile).mul measurable_routePLatePrimeIncrement
  have hw : Measurable
      (fun t => Real.exp ((1 / 2 - ε) * t) * routePNativeCriticalProfile t / t ^ 2) :=
    ((((measurable_const.mul measurable_id).exp).mul
      continuous_routePNativeCriticalProfile.measurable).div (measurable_id.pow_const 2))
  have h := routePNativeLatePrimeMixedWork_isTheta ε
  exact ⟨fun hi => h.2.integrableAtFilter hw.aestronglyMeasurable.stronglyMeasurableAtFilter hi,
    fun hi => h.1.integrableAtFilter hm.aestronglyMeasurable.stronglyMeasurableAtFilter hi⟩

private theorem native_isBigO_mixed {ε : ℝ} (hε : ε < 1 / 2) :
    routePNativeCriticalProfile =O[atTop] routePNativeLatePrimeMixedWork ε := by
  have hpow := (isLittleO_pow_exp_pos_mul_atTop 2 (b := 1 / 2 - ε)
    (by linarith)).bound (by norm_num : (0 : ℝ) < 1)
  have ho : routePNativeCriticalProfile =O[atTop]
      (fun t => Real.exp ((1 / 2 - ε) * t) * routePNativeCriticalProfile t / t ^ 2) := by
    apply IsBigO.of_bound 1
    filter_upwards [hpow, eventually_gt_atTop (0 : ℝ)] with t ht ht0
    simp only [Real.norm_eq_abs, abs_pow, sq_abs, abs_of_pos (Real.exp_pos _), one_mul] at ht
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_pow, sq_abs, le_div_iff₀ (sq_pos_of_pos ht0)]
    exact mul_le_mul_of_nonneg_left ht (abs_nonneg _) |>.trans_eq (mul_comm _ _)
  exact ho.trans (routePNativeLatePrimeMixedWork_isTheta ε).2

/-- Even on a sufficiently late tail the literal mixed term is not absolutely
integrable below the half-damping threshold. -/
theorem not_integrableAtFilter_routePNativeLatePrimeMixedWork {ε : ℝ} (hε : ε < 1 / 2) :
    ¬ IntegrableAtFilter (routePNativeLatePrimeMixedWork ε) atTop volume := by
  intro hi
  apply not_integrableOn_routePNativeCriticalProfile
  have hlocal := continuous_routePNativeCriticalProfile.locallyIntegrable.locallyIntegrableOn
    (Ici (0 : ℝ)) (μ := volume)
  exact (hlocal.integrableOn_of_isBigO_atTop (native_isBigO_mixed hε) hi).mono_set
    Ioi_subset_Ici_self

/-- Separate absolute payment fails for every positive damping below `1/2`. -/
theorem not_integrableOn_routePNativeLatePrimeMixedWork {ε : ℝ} (hε : ε < 1 / 2) :
    ¬ IntegrableOn (routePNativeLatePrimeMixedWork ε) (Ioi 0) := by
  intro hi
  exact not_integrableAtFilter_routePNativeLatePrimeMixedWork hε ⟨Ioi 0, Ioi_mem_atTop 0, hi⟩

end RHTower
