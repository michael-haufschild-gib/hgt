import GaloisForLFunctions.HTGeometry.DiskMultiplierOuterFactor
import GaloisForLFunctions.HTGeometry.DiskMultiplierAlgebra
import GaloisForLFunctions.HTGeometry.SmirnovBoundaryQuotient

/-!
# Cyclicity of canonical Szegő outer factors

The reciprocal of the outer factor for the lower-truncated weight is bounded.  Multiplying it by
the original outer factor gives contractive analytic functions whose values at the origin tend to
one.  Their Hardy vectors therefore tend strongly to the constant vector, proving dense range of
multiplication by the original outer factor.
-/

open Complex MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Positive lower truncation of the canonical boundary weight. -/
def diskMultiplierOuterTruncatedWeight
    (phi : DiskMultiplier) (n : ℕ) (theta : ℝ) : ℝ :=
  max (diskMultiplierOuterWeight phi theta) (Real.exp (-(n : ℝ)))

theorem diskMultiplierOuterTruncatedWeight_pos
    (phi : DiskMultiplier) (n : ℕ) (theta : ℝ) :
    0 < diskMultiplierOuterTruncatedWeight phi n theta :=
  lt_of_lt_of_le (diskMultiplierOuterWeight_pos phi theta) (le_max_left _ _)

theorem diskMultiplierOuterTruncatedWeight_lower
    (phi : DiskMultiplier) (n : ℕ) (theta : ℝ) :
    Real.exp (-(n : ℝ)) ≤ diskMultiplierOuterTruncatedWeight phi n theta :=
  le_max_right _ _

theorem diskMultiplierOuterTruncatedWeight_le
    (phi : DiskMultiplier) (n : ℕ) (theta : ℝ) :
    diskMultiplierOuterTruncatedWeight phi n theta ≤ (max 1 phi.bd) ^ 2 := by
  apply max_le
  · exact diskMultiplierOuterWeight_le phi theta
  · have hn : 0 ≤ (n : ℝ) := by positivity
    have hexp : Real.exp (-(n : ℝ)) ≤ 1 := by
      simpa using Real.exp_le_one_iff.mpr (by linarith)
    exact hexp.trans (by nlinarith [le_max_left (1 : ℝ) phi.bd])

theorem diskMultiplierOuterTruncatedWeight_periodic
    (phi : DiskMultiplier) (n : ℕ) :
    Function.Periodic (diskMultiplierOuterTruncatedWeight phi n)
      (2 * Real.pi) := by
  intro theta
  rw [diskMultiplierOuterTruncatedWeight, diskMultiplierOuterTruncatedWeight,
    diskMultiplierOuterWeight_periodic phi theta]

theorem log_diskMultiplierOuterTruncatedWeight
    (phi : DiskMultiplier) (n : ℕ) (theta : ℝ) :
    Real.log (diskMultiplierOuterTruncatedWeight phi n theta) =
      max (Real.log (diskMultiplierOuterWeight phi theta)) (-(n : ℝ)) := by
  rw [diskMultiplierOuterTruncatedWeight]
  by_cases h : diskMultiplierOuterWeight phi theta ≤ Real.exp (-(n : ℝ))
  · rw [max_eq_right h, Real.log_exp]
    have hlog : Real.log (diskMultiplierOuterWeight phi theta) ≤ -(n : ℝ) := by
      rw [← Real.exp_le_exp]
      simpa [Real.exp_log (diskMultiplierOuterWeight_pos phi theta)] using h
    exact (max_eq_right hlog).symm
  · have h' : Real.exp (-(n : ℝ)) ≤ diskMultiplierOuterWeight phi theta := le_of_not_ge h
    rw [max_eq_left h']
    have hlog : -(n : ℝ) ≤ Real.log (diskMultiplierOuterWeight phi theta) := by
      rw [← Real.exp_le_exp]
      simpa [Real.exp_log (diskMultiplierOuterWeight_pos phi theta)] using h'
    exact (max_eq_left hlog).symm

theorem abs_log_diskMultiplierOuterTruncatedWeight_le
    (phi : DiskMultiplier) (n : ℕ) (theta : ℝ) :
    |Real.log (diskMultiplierOuterTruncatedWeight phi n theta)| ≤
      |Real.log (diskMultiplierOuterWeight phi theta)| := by
  rw [log_diskMultiplierOuterTruncatedWeight]
  have hn : 0 ≤ (n : ℝ) := by positivity
  by_cases h : Real.log (diskMultiplierOuterWeight phi theta) ≤ -(n : ℝ)
  · rw [max_eq_right h]
    have hlog : Real.log (diskMultiplierOuterWeight phi theta) ≤ 0 := h.trans (neg_nonpos.mpr hn)
    rw [abs_of_nonpos (neg_nonpos.mpr hn), abs_of_nonpos hlog]
    linarith
  · rw [max_eq_left (le_of_not_ge h)]

theorem intervalIntegrable_log_diskMultiplierOuterTruncatedWeight
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0)
    (n : ℕ) :
    IntervalIntegrable
      (fun theta => Real.log (diskMultiplierOuterTruncatedWeight phi n theta))
      volume 0 (2 * Real.pi) := by
  let f : ℝ → ℝ := fun theta => Real.log (diskMultiplierOuterWeight phi theta)
  let F : ℝ → ℝ := fun theta =>
    Real.log (diskMultiplierOuterTruncatedWeight phi n theta)
  have hf := intervalIntegrable_log_diskMultiplierOuterWeight phi hphi
  have hang : Measurable angularCircle := by
    apply Continuous.measurable
    unfold angularCircle
    fun_prop
  have hw : Measurable (diskMultiplierOuterWeight phi) := by
    exact (((measurable_diskMultiplierBoundarySafe phi).comp hang).norm.pow_const 2)
  have hFm : AEStronglyMeasurable F volume := by
    exact (Real.measurable_log.comp (hw.max measurable_const)).aestronglyMeasurable
  constructor
  · exact hf.1.norm.mono' hFm.restrict
      (Filter.Eventually.of_forall fun theta => by
        simpa [F, f, Real.norm_eq_abs] using
          abs_log_diskMultiplierOuterTruncatedWeight_le phi n theta)
  · exact hf.2.norm.mono' hFm.restrict
      (Filter.Eventually.of_forall fun theta => by
        simpa [F, f, Real.norm_eq_abs] using
          abs_log_diskMultiplierOuterTruncatedWeight_le phi n theta)

theorem normSq_szegoOuter_mono_of_log_le
    {u v : ℝ → ℝ}
    (hlogu : IntervalIntegrable (fun theta => Real.log (u theta)) volume
      0 (2 * Real.pi))
    (hlogv : IntervalIntegrable (fun theta => Real.log (v theta)) volume
      0 (2 * Real.pi))
    (huv : ∀ theta, Real.log (u theta) ≤ Real.log (v theta))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (varphi : ℝ) :
    ‖szegoOuter u (circleMap 0 r varphi)‖ ^ 2 ≤
      ‖szegoOuter v (circleMap 0 r varphi)‖ ^ 2 := by
  rw [normSq_szegoOuter_circleMap hlogu hr0 hr1 varphi,
    normSq_szegoOuter_circleMap hlogv hr0 hr1 varphi]
  apply Real.exp_le_exp.mpr
  gcongr
  have habs : |r| < 1 := by rw [abs_of_nonneg hr0]; exact hr1
  have hcont : Continuous (fun theta => poissonKer r (theta - varphi)) :=
    (poissonKer_continuous habs).comp (continuous_id.sub continuous_const)
  apply intervalIntegral.integral_mono_on (by positivity)
    (hlogu.continuousOn_mul hcont.continuousOn)
    (hlogv.continuousOn_mul hcont.continuousOn)
  intro theta _
  exact mul_le_mul_of_nonneg_left (huv theta)
    (poissonKer_nonneg hr0 hr1 (theta - varphi))

/-- Bounded analytic reciprocal of the lower-truncated outer factor. -/
noncomputable def diskMultiplierOuterTruncatedInverse
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0)
    (n : ℕ) : DiskMultiplier where
  fn := fun z => (szegoOuter (diskMultiplierOuterTruncatedWeight phi n) z)⁻¹
  diff := (analyticOnNhd_inv_szegoOuter
    (intervalIntegrable_log_diskMultiplierOuterTruncatedWeight phi hphi n)).differentiableOn
  bd := Real.exp (n : ℝ)
  bd_nonneg := (Real.exp_pos _).le
  bd_le := by
    intro z hz
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    have hz1 : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    have hsq := normSq_inv_szegoOuter_le_from_weight_lower
      (Real.exp_pos (-(n : ℝ)))
      (intervalIntegrable_log_diskMultiplierOuterTruncatedWeight phi hphi n)
      (diskMultiplierOuterTruncatedWeight_lower phi n)
      hz0 hz1 z.arg
    rw [circleMap_norm_arg, Real.exp_neg, inv_inv] at hsq
    have hexpone : 1 ≤ Real.exp (n : ℝ) :=
      Real.one_le_exp (by positivity)
    nlinarith [norm_nonneg
      ((szegoOuter (diskMultiplierOuterTruncatedWeight phi n) z)⁻¹)]

/-- Contractive quotient of the original outer factor by its lower-truncated outer factor. -/
noncomputable def diskMultiplierOuterCyclicApprox
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0)
    (n : ℕ) : DiskMultiplier where
  fn := fun z => szegoOuter (diskMultiplierOuterWeight phi) z *
    (szegoOuter (diskMultiplierOuterTruncatedWeight phi n) z)⁻¹
  diff := (analyticOnNhd_szegoOuter
    (intervalIntegrable_log_diskMultiplierOuterWeight phi hphi)).differentiableOn.mul
      (analyticOnNhd_inv_szegoOuter
        (intervalIntegrable_log_diskMultiplierOuterTruncatedWeight phi hphi n)).differentiableOn
  bd := 1
  bd_nonneg := zero_le_one
  bd_le := by
    intro z hz
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    have hz1 : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    have hsq := normSq_szegoOuter_mono_of_log_le
      (intervalIntegrable_log_diskMultiplierOuterWeight phi hphi)
      (intervalIntegrable_log_diskMultiplierOuterTruncatedWeight phi hphi n)
      (fun theta => by
        rw [log_diskMultiplierOuterTruncatedWeight]
        exact le_max_left _ _)
      hz0 hz1 z.arg
    rw [circleMap_norm_arg] at hsq
    rw [norm_mul, norm_inv]
    have hnorm := (sq_le_sq₀
      (norm_nonneg (szegoOuter (diskMultiplierOuterWeight phi) z))
      (norm_nonneg (szegoOuter (diskMultiplierOuterTruncatedWeight phi n) z))).mp hsq
    rw [← div_eq_mul_inv]
    exact (div_le_one (norm_pos_iff.mpr (szegoOuter_ne_zero _ _))).mpr hnorm

theorem tendsto_log_diskMultiplierOuterTruncatedWeight
    (phi : DiskMultiplier) (theta : ℝ) :
    Tendsto
      (fun n : ℕ => Real.log (diskMultiplierOuterTruncatedWeight phi n theta))
      atTop (𝓝 (Real.log (diskMultiplierOuterWeight phi theta))) := by
  apply tendsto_const_nhds.congr'
  obtain ⟨N, hN⟩ := exists_nat_ge
    (-Real.log (diskMultiplierOuterWeight phi theta))
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [log_diskMultiplierOuterTruncatedWeight]
  have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
  exact (max_eq_left (by linarith)).symm

theorem tendsto_integral_log_diskMultiplierOuterTruncatedWeight
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    Tendsto
      (fun n : ℕ => ∫ theta in (0 : ℝ)..(2 * Real.pi),
        Real.log (diskMultiplierOuterTruncatedWeight phi n theta))
      atTop
      (𝓝 (∫ theta in (0 : ℝ)..(2 * Real.pi),
        Real.log (diskMultiplierOuterWeight phi theta))) := by
  let f : ℝ → ℝ := fun theta => Real.log (diskMultiplierOuterWeight phi theta)
  let F : ℕ → ℝ → ℝ := fun n theta =>
    Real.log (diskMultiplierOuterTruncatedWeight phi n theta)
  have hang : Measurable angularCircle := by
    apply Continuous.measurable
    unfold angularCircle
    fun_prop
  have hw : Measurable (diskMultiplierOuterWeight phi) :=
    (((measurable_diskMultiplierBoundarySafe phi).comp hang).norm.pow_const 2)
  have hFm : ∀ n, AEStronglyMeasurable (F n)
      (volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))) := by
    intro n
    exact (Real.measurable_log.comp (hw.max measurable_const)).aestronglyMeasurable.restrict
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun theta => |f theta|)
  · exact Filter.Eventually.of_forall hFm
  · exact Filter.Eventually.of_forall fun n =>
      Filter.Eventually.of_forall fun theta _ => by
        simpa [F, f, Real.norm_eq_abs] using
          abs_log_diskMultiplierOuterTruncatedWeight_le phi n theta
  · exact (intervalIntegrable_log_diskMultiplierOuterWeight phi hphi).norm
  · exact Filter.Eventually.of_forall fun theta _ =>
      tendsto_log_diskMultiplierOuterTruncatedWeight phi theta

theorem szegoOuter_zero_eq_real_exp (w : ℝ → ℝ) :
    szegoOuter w 0 =
      ((Real.exp ((1 / (4 * Real.pi)) *
        ∫ theta in (0 : ℝ)..(2 * Real.pi), Real.log (w theta)) : ℝ) : ℂ) := by
  have hint :
      (∫ theta in (0 : ℝ)..(2 * Real.pi),
        -herglotzRieszKernel 0 (circleMap 0 1 theta) 0 *
          (Real.log (w theta) : ℂ)) =
        ((∫ theta in (0 : ℝ)..(2 * Real.pi), Real.log (w theta) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro theta _
    change -herglotzRieszKernel 0 (circleMap 0 1 theta) 0 *
      (Real.log (w theta) : ℂ) = (Real.log (w theta) : ℂ)
    rw [neg_herglotz_zero, one_mul]
  rw [szegoOuter, hint]
  congr 1
  push_cast
  ring

theorem tendsto_szegoOuter_truncated_zero
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    Tendsto
      (fun n : ℕ => szegoOuter (diskMultiplierOuterTruncatedWeight phi n) 0)
      atTop
      (𝓝 (szegoOuter (diskMultiplierOuterWeight phi) 0)) := by
  have hint := tendsto_integral_log_diskMultiplierOuterTruncatedWeight phi hphi
  have hscaled := hint.const_mul (1 / (4 * Real.pi))
  have hexp := (Real.continuous_exp.tendsto _).comp hscaled
  have hcomplex := (Complex.continuous_ofReal.tendsto _).comp hexp
  change Tendsto
    (fun n : ℕ => ((Real.exp ((1 / (4 * Real.pi)) *
      ∫ theta in (0 : ℝ)..(2 * Real.pi),
        Real.log (diskMultiplierOuterTruncatedWeight phi n theta)) : ℝ) : ℂ))
    atTop
    (𝓝 (((Real.exp ((1 / (4 * Real.pi)) *
      ∫ theta in (0 : ℝ)..(2 * Real.pi),
        Real.log (diskMultiplierOuterWeight phi theta)) : ℝ) : ℂ))) at hcomplex
  simpa only [szegoOuter_zero_eq_real_exp] using hcomplex

theorem tendsto_diskMultiplierOuterCyclicApprox_zero
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    Tendsto (fun n => (diskMultiplierOuterCyclicApprox phi hphi n).fn 0)
      atTop (𝓝 (1 : ℂ)) := by
  have hden := tendsto_szegoOuter_truncated_zero phi hphi
  have hnum : Tendsto
      (fun _n : ℕ => szegoOuter (diskMultiplierOuterWeight phi) 0)
      atTop (𝓝 (szegoOuter (diskMultiplierOuterWeight phi) 0)) :=
    tendsto_const_nhds
  have hquot := hnum.div hden
    (szegoOuter_ne_zero (diskMultiplierOuterWeight phi) 0)
  change Tendsto
    (fun n => szegoOuter (diskMultiplierOuterWeight phi) 0 /
      szegoOuter (diskMultiplierOuterTruncatedWeight phi n) 0)
    atTop
    (𝓝 (szegoOuter (diskMultiplierOuterWeight phi) 0 /
      szegoOuter (diskMultiplierOuterWeight phi) 0)) at hquot
  rw [div_self (szegoOuter_ne_zero (diskMultiplierOuterWeight phi) 0)] at hquot
  simpa only [diskMultiplierOuterCyclicApprox, div_eq_mul_inv] using hquot

theorem norm_hardyOne_eq_one : ‖hardyOne‖ = 1 := by
  rw [hardyOne, lp.norm_single (by norm_num)]
  norm_num

theorem tendsto_hardyOf_of_bound_one_of_tendsto_zero
    (u : ℕ → DiskMultiplier)
    (hubd : ∀ n, (u n).bd = 1)
    (hu0 : Tendsto (fun n => (u n).fn 0) atTop (𝓝 (1 : ℂ))) :
    Tendsto (fun n => hardyOf (u n)) atTop (𝓝 hardyOne) := by
  have hnormSq (n : ℕ) : ‖hardyOf (u n)‖ ^ 2 ≤ 1 := by
    have h := (hardyMulCoeff_bound (u n) hardyOne).2
    change ‖hardyOf (u n)‖ ^ 2 ≤ 1
    rw [hardyOf, hardyDisk_norm_sq]
    change (∑' k, ‖hardyMulCoeff (u n) hardyOne k‖ ^ 2) ≤ 1
    rw [hubd n, norm_hardyOne_eq_one] at h
    norm_num at h
    exact h
  have hinner (n : ℕ) : inner ℂ hardyOne (hardyOf (u n)) = (u n).fn 0 := by
    have hzero : hardyFun (hardyOf (u n)) 0 = (u n).fn 0 :=
      hardyFun_hardyOf (u n) (by norm_num)
    calc
      inner ℂ hardyOne (hardyOf (u n)) =
          inner ℂ (hardyKernel (by norm_num : ‖(0 : ℂ)‖ < 1))
            (hardyOf (u n)) := by rw [hardyKernel_zero_eq_hardyOne]
      _ = hardyFun (hardyOf (u n)) 0 :=
        inner_hardyKernel (by norm_num) (hardyOf (u n))
      _ = (hardyOf (u n)) 0 := hardyFun_zero _
      _ = (u n).fn 0 := (hardyFun_zero _).symm.trans hzero
  have hdistSq (n : ℕ) :
      ‖hardyOf (u n) - hardyOne‖ ^ 2 ≤
        2 - 2 * ((u n).fn 0).re := by
    have hnormSub := norm_sub_sq (𝕜 := ℂ) hardyOne (hardyOf (u n))
    rw [norm_sub_rev] at hnormSub
    rw [norm_hardyOne_eq_one, hinner] at hnormSub
    change ‖hardyOf (u n) - hardyOne‖ ^ 2 =
      1 ^ 2 - 2 * ((u n).fn 0).re + ‖hardyOf (u n)‖ ^ 2 at hnormSub
    nlinarith [hnormSq n]
  have hupper : Tendsto (fun n => 2 - 2 * ((u n).fn 0).re)
      atTop (𝓝 0) := by
    have hre : Tendsto (fun n => ((u n).fn 0).re) atTop (𝓝 (1 : ℝ)) := by
      have h := (Complex.continuous_re.tendsto (1 : ℂ)).comp hu0
      change Tendsto (fun n => ((u n).fn 0).re) atTop (𝓝 (1 : ℝ)) at h
      exact h
    have hconst : Tendsto (fun _n : ℕ => (2 : ℝ)) atTop (𝓝 2) :=
      tendsto_const_nhds
    simpa using hconst.sub (hre.const_mul 2)
  have hsq : Tendsto (fun n => ‖hardyOf (u n) - hardyOne‖ ^ 2)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper
      (Filter.Eventually.of_forall fun n => sq_nonneg _)
      (Filter.Eventually.of_forall hdistSq)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  change Tendsto
    (fun n => Real.sqrt (‖hardyOf (u n) - hardyOne‖ ^ 2))
    atTop (𝓝 (Real.sqrt 0)) at hsqrt
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hsqrt

theorem tendsto_hardyOf_diskMultiplierOuterCyclicApprox
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    Tendsto (fun n => hardyOf (diskMultiplierOuterCyclicApprox phi hphi n))
      atTop (𝓝 hardyOne) :=
  tendsto_hardyOf_of_bound_one_of_tendsto_zero
    (diskMultiplierOuterCyclicApprox phi hphi)
    (fun _ => rfl)
    (tendsto_diskMultiplierOuterCyclicApprox_zero phi hphi)

theorem hardyOf_diskMultiplierOuterCyclicApprox_mem_range
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0)
    (n : ℕ) :
    hardyOf (diskMultiplierOuterCyclicApprox phi hphi n) ∈
      Set.range (hardyMul (diskMultiplierOuterFactor phi hphi)) := by
  let outer := diskMultiplierOuterFactor phi hphi
  let invn := diskMultiplierOuterTruncatedInverse phi hphi n
  have hcongr : hardyOf (diskMultiplierOuterCyclicApprox phi hphi n) =
      hardyOf (outer.mul invn) := by
    apply hardyOf_congr
    intro z _
    rfl
  refine ⟨hardyOf invn, ?_⟩
  rw [hcongr, hardyOf, hardyOf]
  exact hardyMul_mul outer invn hardyOne

theorem isOuterDiskMultiplier_diskMultiplierOuterFactor
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    IsOuterDiskMultiplier (diskMultiplierOuterFactor phi hphi) := by
  let outer := diskMultiplierOuterFactor phi hphi
  let R : Submodule ℂ HardyDisk :=
    LinearMap.range ((hardyMul outer : HardyDisk →L[ℂ] HardyDisk) :
      HardyDisk →ₗ[ℂ] HardyDisk)
  let V : Submodule ℂ HardyDisk := R.topologicalClosure
  have hone : hardyOne ∈ V := by
    change hardyOne ∈ closure (R : Set HardyDisk)
    apply mem_closure_of_tendsto
      (tendsto_hardyOf_diskMultiplierOuterCyclicApprox phi hphi)
    exact Filter.Eventually.of_forall fun n => by
      change hardyOf (diskMultiplierOuterCyclicApprox phi hphi n) ∈ R
      exact hardyOf_diskMultiplierOuterCyclicApprox_mem_range phi hphi n
  have hshift : ∀ {x : HardyDisk}, x ∈ V → hardyMul diskShift x ∈ V := by
    intro x hx
    have hclosed : IsClosed
        ((hardyMul diskShift : HardyDisk → HardyDisk) ⁻¹' (V : Set HardyDisk)) :=
      (Submodule.isClosed_topologicalClosure R).preimage (hardyMul diskShift).continuous
    have hrange : (R : Set HardyDisk) ⊆
        (hardyMul diskShift : HardyDisk → HardyDisk) ⁻¹' (V : Set HardyDisk) := by
      intro y hy
      obtain ⟨q, rfl⟩ := hy
      change hardyMul diskShift (hardyMul outer q) ∈ V
      rw [hardyMul_comm]
      exact Submodule.le_topologicalClosure R
        (show hardyMul outer (hardyMul diskShift q) ∈ R from
          ⟨hardyMul diskShift q, rfl⟩)
    change x ∈ closure (R : Set HardyDisk) at hx
    exact closure_minimal hrange hclosed hx
  have hpowers : ∀ n : ℕ, ((hardyMul diskShift) ^ n) hardyOne ∈ V := by
    intro n
    induction n with
    | zero => simpa using hone
    | succ n ih =>
        rw [pow_succ']
        exact hshift ih
  have hpoly : polyMultiples hardyOne ≤ V := by
    rw [polyMultiples]
    apply Submodule.span_le.mpr
    rintro y ⟨n, rfl⟩
    exact hpowers n
  have hcyclic : cyclicSubspace hardyOne ≤ V := by
    rw [cyclicSubspace]
    exact (polyMultiples hardyOne).topologicalClosure_minimal hpoly
      (Submodule.isClosed_topologicalClosure R)
  have hVtop : V = ⊤ := by
    apply top_unique
    rw [← cyclicSubspace_hardyOne]
    exact hcyclic
  rw [isOuterDiskMultiplier_iff_denseRange, denseRange_iff_closure_range]
  have hrange : (R : Set HardyDisk) =
      Set.range (hardyMul outer : HardyDisk → HardyDisk) := by
    ext y
    constructor <;> rintro ⟨x, rfl⟩ <;> exact ⟨x, rfl⟩
  have hsets := congrArg (fun W : Submodule ℂ HardyDisk => (W : Set HardyDisk)) hVtop
  simp only [V, Submodule.topologicalClosure_coe, Submodule.top_coe] at hsets
  rw [hrange] at hsets
  simpa [outer] using hsets

end

end GaloisForLFunctions.HTGeometry
