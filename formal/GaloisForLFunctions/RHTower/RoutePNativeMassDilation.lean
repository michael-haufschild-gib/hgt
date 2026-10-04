import GaloisForLFunctions.RHTower.RoutePNativeMassPrefixMoments
import GaloisForLFunctions.RHTower.RoutePCoprimeSquareNative
import GaloisForLFunctions.RHTower.LogarithmicDilationPrimitiveQuadrature
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The complete dilation source after native mass compensation

The full arithmetic cutoff becomes a normalized floor kernel in `[0,1]`.
Its exact limit exposes the nonzero mass introduced by compensation.
Every force admission below is proved for the literal native profile.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

def routePNativeMassCoprimeProfile (lam t : ℝ) : ℝ :=
  Real.exp t * routePNativeMassCompensatedLogProfile lam t

def routePNativeMassDilation (lam T : ℝ) : ℝ :=
  logarithmicDilationSum (routePNativeMassCoprimeProfile lam) T

/-- The carrier in the coprime form is the same profile as in the audited
finite-window compensation identity, with its half-density restored. -/
theorem routePNativeMassCoprimeProfile_eq_compensated (lam t : ℝ) :
    routePNativeMassCoprimeProfile lam t =
      Real.exp (t / 2) * routePNativeMassCompensatedProfile (1 - lam) t := by
  unfold routePNativeMassCoprimeProfile routePNativeMassCompensatedLogProfile
    routePNativeMassCompensatedProfile
  rw [show (1 : ℝ) - (1 - lam) = lam by ring, ← mul_assoc, ← Real.exp_add]
  rw [show t / 2 + t / 2 = t by ring]

/-- Zero compensation is exactly the existing native coprime carrier. -/
theorem routePNativeMassCoprimeProfile_zero :
    routePNativeMassCoprimeProfile 0 = routePCoprimeNativeProfile := by
  funext t
  simp only [routePNativeMassCoprimeProfile, routePNativeMassCompensatedLogProfile,
    zero_mul, add_zero, routePCoprimeNativeProfile]
  rw [← Real.exp_half, mobiusDivisorFullHead_eq_criticalContinuousAbel]
  unfold criticalAbelLogProfile
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

private def weightedForce (lam t : ℝ) : ℝ :=
  (1 + lam) * criticalAbelLogProfile t + criticalAbelLogVelocity t +
    lam * routePNativeMassPrefix t

private def force (lam t : ℝ) : ℝ := Real.exp t * weightedForce lam t

private theorem force_admission_mass (lam : ℝ) :
    IntegrableOn (weightedForce lam) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), weightedForce lam t) =
        lam * (divisorHarmonicBoundary / 3) := by
  have ha := (integrable_criticalAbelLogProfile.integrableOn (s := Ioi (0 : ℝ))).const_mul
    (1 + lam)
  have hv := integrableOn_criticalAbelLogVelocity
  have hm := integrableOn_routePNativeMassPrefix.const_mul lam
  have hav : IntegrableOn (fun t =>
      (1 + lam) * criticalAbelLogProfile t + criticalAbelLogVelocity t) (Ioi 0) := ha.add hv
  refine ⟨(ha.add hv).add hm, ?_⟩
  change (∫ t in Ioi (0 : ℝ),
    ((1 + lam) * criticalAbelLogProfile t + criticalAbelLogVelocity t) +
      lam * routePNativeMassPrefix t) = _
  rw [integral_add hav hm, integral_add ha hv, integral_const_mul,
    integral_const_mul, criticalAbelLogProfile_mass_zero, criticalAbelLogVelocity_mass_zero,
    integral_routePNativeMassPrefix]
  ring

private theorem force_measurable (lam : ℝ) : Measurable (weightedForce lam) := by
  have hv : Measurable criticalAbelLogVelocity :=
    (measurable_criticalAbelLogDefect.div_const 2).sub
      (measurable_const.mul measurable_criticalAbelLogProfile)
  exact ((measurable_const.mul measurable_criticalAbelLogProfile).add hv).add
    (measurable_const.mul continuous_routePNativeMassPrefix.measurable)

private theorem profile_continuous (lam : ℝ) :
    Continuous (routePNativeMassCoprimeProfile lam) :=
  Real.continuous_exp.mul
    (continuous_criticalAbelLogProfile.add (continuous_const.mul continuous_routePNativeMassPrefix))

private theorem profile_deriv (lam : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (routePNativeMassCoprimeProfile lam) (force lam t) (Ioi t) t := by
  have hm : HasDerivAt routePNativeMassPrefix (criticalAbelLogProfile t) t :=
    intervalIntegral.integral_hasDerivAt_right
      (continuous_criticalAbelLogProfile.intervalIntegrable _ _)
      continuous_criticalAbelLogProfile.aestronglyMeasurable.stronglyMeasurableAtFilter
      continuous_criticalAbelLogProfile.continuousAt
  have h := (Real.hasDerivAt_exp t).hasDerivWithinAt.mul
    ((criticalAbelLogProfile_hasDeriv_right ht).add (hm.hasDerivWithinAt.const_mul lam))
  have hraw : HasDerivWithinAt (routePNativeMassCoprimeProfile lam)
      (Real.exp t * (criticalAbelLogProfile t + lam * routePNativeMassPrefix t) +
        Real.exp t * (criticalAbelLogVelocity t + lam * criticalAbelLogProfile t)) (Ioi t) t := by
    change HasDerivWithinAt
      (fun u => Real.exp u * (criticalAbelLogProfile u + lam * routePNativeMassPrefix u)) _ _ _
    simpa only [Pi.mul_def, Pi.add_def] using h
  apply hraw.congr_deriv
  unfold force weightedForce
  ring

private theorem force_local (lam : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (force lam) volume 0 T := by
  have hi : IntervalIntegrable (weightedForce lam) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
      ((force_admission_mass lam).1.mono_set Ioc_subset_Ioi_self)
  change IntervalIntegrable (fun t => Real.exp t * weightedForce lam t) volume 0 T
  simpa only [Pi.mul_def, mul_comm] using hi.mul_continuousOn Real.continuous_exp.continuousOn

private theorem profile_primitive (lam : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, force lam t) = routePNativeMassCoprimeProfile lam T := by
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT
    (profile_continuous lam).continuousOn
    (fun t ht => profile_deriv lam ht.1.le) (force_local lam hT)
  have hz : routePNativeMassCoprimeProfile lam 0 = 0 := by
    simp [routePNativeMassCoprimeProfile, routePNativeMassCompensatedLogProfile,
      routePNativeMassPrefix, criticalAbelLogProfile_zero_of_nonpos le_rfl]
  simpa only [hz, sub_zero] using h

private def floorKernel (t : ℝ) : ℝ := Real.exp (-t) * (⌊Real.exp t⌋₊ : ℝ)

private theorem kernel_bounds (t : ℝ) : 0 ≤ floorKernel t ∧ floorKernel t ≤ 1 := by
  refine ⟨by unfold floorKernel; positivity, ?_⟩
  calc
    floorKernel t ≤ Real.exp (-t) * Real.exp t :=
      mul_le_mul_of_nonneg_left (Nat.floor_le (Real.exp_pos t).le) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

private theorem kernel_zero {t : ℝ} (ht : t < 0) : floorKernel t = 0 := by
  have he : Real.exp t < 1 := by simpa using Real.exp_lt_exp.mpr ht
  simp [floorKernel, Nat.floor_eq_zero.mpr he]

private theorem kernel_measurable : Measurable floorKernel :=
  measurable_id.neg.exp.mul
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp Real.measurable_exp.nat_floor)

private theorem kernel_limit : Tendsto floorKernel atTop (𝓝 1) := by
  change Tendsto (fun t => Real.exp (-t) * (⌊Real.exp t⌋₊ : ℝ)) atTop (𝓝 1)
  simpa only [Function.comp_def, Real.exp_neg, div_eq_mul_inv, mul_comm] using
    tendsto_nat_floor_div_atTop.comp Real.tendsto_exp_atTop

private theorem kernel_pair_bound (lam T t : ℝ) :
    ‖weightedForce lam t * floorKernel (T - t)‖ ≤ |weightedForce lam t| := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kernel_bounds _).1]
  exact mul_le_of_le_one_right (abs_nonneg _) (kernel_bounds _).2

private theorem kernel_pair_admission (lam T : ℝ) :
    IntegrableOn (fun t => weightedForce lam t * floorKernel (T - t)) (Ioi 0) := by
  apply (force_admission_mass lam).1.norm.mono'
    ((force_measurable lam).mul
      (kernel_measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable.restrict
  filter_upwards with t
  change ‖weightedForce lam t * floorKernel (T - t)‖ ≤ ‖weightedForce lam t‖
  simpa only [Real.norm_eq_abs] using kernel_pair_bound lam T t

private theorem dilation_floor_integral (lam : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    routePNativeMassDilation lam T =
      ∫ s in (0 : ℝ)..T, force lam (T - s) * (⌊Real.exp s⌋₊ : ℝ) := by
  have heq : routePNativeMassDilation lam T =
      logarithmicDilationSum (fun u => ∫ t in (0 : ℝ)..u, force lam t) T := by
    unfold routePNativeMassDilation logarithmicDilationSum logarithmicWeightedDilation
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hlog : Real.log n ≤ T := (Real.log_le_iff_le_exp hnpos).mpr
      ((Nat.le_floor_iff (Real.exp_pos T).le).mp (Finset.mem_Icc.mp hn).2)
    simp only [one_mul]
    exact (profile_primitive lam (sub_nonneg.mpr hlog)).symm
  rw [heq]
  exact logarithmicDilationSum_primitive_eq_floor_integral _ (force_local lam hT) hT

private theorem normalized_dilation_integral (lam : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    Real.exp (-T) * routePNativeMassDilation lam T =
      ∫ t in Ioi (0 : ℝ), weightedForce lam t * floorKernel (T - t) := by
  rw [dilation_floor_integral lam hT, ← intervalIntegral.integral_const_mul]
  have hpoint (s : ℝ) :
      Real.exp (-T) * (force lam (T - s) * (⌊Real.exp s⌋₊ : ℝ)) =
        weightedForce lam (T - s) * floorKernel s := by
    unfold force floorKernel
    rw [show Real.exp (-T) * (Real.exp (T - s) * weightedForce lam (T - s) *
        (⌊Real.exp s⌋₊ : ℝ)) =
        (Real.exp (-T) * Real.exp (T - s)) * weightedForce lam (T - s) *
          (⌊Real.exp s⌋₊ : ℝ) by ring, ← Real.exp_add]
    rw [show -T + (T - s) = -s by ring]
    ring
  simp_rw [hpoint]
  have hrev := intervalIntegral.integral_comp_sub_left
    (fun t => weightedForce lam t * floorKernel (T - t)) (a := 0) (b := T) T
  simp only [sub_sub_cancel, sub_self, sub_zero] at hrev
  rw [hrev]
  have hi := kernel_pair_admission lam T
  have h := intervalIntegral.integral_interval_add_Ioi hi (hi.mono_set (Ioi_subset_Ioi hT))
  have hz : (∫ t in Ioi T, weightedForce lam t * floorKernel (T - t)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change weightedForce lam t * floorKernel (T - t) = 0
    rw [kernel_zero (sub_neg.mpr ht), mul_zero]
  simpa only [hz, add_zero] using h

/-- Complete native dilation source, with the exponential coefficient fixed
by the actual first signed moment. -/
theorem routePNativeMassDilation_asymptotic (lam : ℝ) :
    Tendsto (fun T : ℝ => Real.exp (-T) * routePNativeMassDilation lam T)
      atTop (𝓝 (lam * (divisorHarmonicBoundary / 3))) := by
  have hs (t : ℝ) : Tendsto (fun T : ℝ => T - t) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b + t)] with T hT
    linarith
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ))) (fun t => |weightedForce lam t|)
    (Eventually.of_forall (fun T => (kernel_pair_admission lam T).aestronglyMeasurable))
    (Eventually.of_forall (fun T => Eventually.of_forall (kernel_pair_bound lam T)))
    (force_admission_mass lam).1.norm
    (Eventually.of_forall (fun t => by
      simpa only [Function.comp_def, mul_one] using
        (kernel_limit.comp (hs t)).const_mul (weightedForce lam t)))
  rw [(force_admission_mass lam).2] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact (normalized_dilation_integral lam hT).symm

/-- A single absolute bound controls every normalized physical dilation
cutoff; it comes from the admitted literal force, not from native L2. -/
theorem routePNativeMassDilation_normalized_bound (lam : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, |Real.exp (-T) * routePNativeMassDilation lam T| ≤ C := by
  refine ⟨∫ t in Ioi (0 : ℝ), |weightedForce lam t|,
    integral_nonneg (fun _ => abs_nonneg _), ?_⟩
  intro T
  by_cases hT : 0 ≤ T
  · rw [normalized_dilation_integral lam hT]
    have hn := norm_integral_le_integral_norm
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (fun t => weightedForce lam t * floorKernel (T - t))
    apply (show |∫ t in Ioi (0 : ℝ), weightedForce lam t * floorKernel (T - t)| ≤
      ∫ t in Ioi (0 : ℝ), ‖weightedForce lam t * floorKernel (T - t)‖ from
      by simpa only [Real.norm_eq_abs] using hn).trans
    exact integral_mono_ae (kernel_pair_admission lam T).norm
      (force_admission_mass lam).1.norm (Eventually.of_forall (kernel_pair_bound lam T))
  · have he : Real.exp T < 1 := by
      simpa using Real.exp_lt_exp.mpr (lt_of_not_ge hT)
    simp only [routePNativeMassDilation, logarithmicDilationSum, logarithmicWeightedDilation,
      Nat.floor_eq_zero.mpr he, Finset.Icc_eq_empty_of_lt (by decide : (0 : ℕ) < 1),
      Finset.sum_empty, mul_zero, abs_zero]
    exact integral_nonneg (fun _ => abs_nonneg _)

end RHTower
