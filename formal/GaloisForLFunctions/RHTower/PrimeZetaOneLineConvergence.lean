import GaloisForLFunctions.RHTower.OscillatoryLogIntegral
import GaloisForLFunctions.RHTower.Sieve.ChebyshevThetaBigO

/-!
# Convergence of the prime zeta series on the one-line
-/

namespace RHTower

open Filter MeasureTheory Finset
open scoped Topology BigOperators

/-- The prime-log coefficient field. -/
noncomputable def primeLogCoeff (k : ℕ) : ℂ := if k.Prime then ((Real.log k : ℝ) : ℂ) else 0

theorem primeLogCoeff_zero : primeLogCoeff 0 = 0 := by
  simp [primeLogCoeff, Nat.not_prime_zero]

theorem primeLogCoeff_one : primeLogCoeff 1 = 0 := by
  simp [primeLogCoeff, Nat.not_prime_one]

theorem sum_primeLogCoeff_eq_theta (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 n, primeLogCoeff k = ((Chebyshev.theta (n : ℝ) : ℝ) : ℂ) := by
  classical
  have hfloor : ⌊(n : ℝ)⌋₊ = n := Nat.floor_natCast n
  rw [Chebyshev.theta, hfloor, Finset.sum_filter]
  push_cast
  have hsplit : Finset.Icc 0 n = insert 0 (Finset.Ioc 0 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [hsplit, Finset.sum_insert (by simp)]
  simp only [primeLogCoeff, Nat.not_prime_zero, if_false, zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k.Prime <;> simp [hk]

/-! ## The derivative of the oscillatory kernel -/

/-- The derivative of the oscillatory logarithmic kernel. -/
noncomputable def oscLogKernelDeriv (lam : ℝ) (t : ℝ) : ℂ :=
  logPhase lam t * (((t : ℂ)) ^ 2)⁻¹ *
    ((-1 - (lam : ℂ) * Complex.I) * invLogC t - (invLogC t) ^ 2)

theorem hasDerivAt_oscLogKernel {lam : ℝ} {t : ℝ} (ht : 1 < t) :
    HasDerivAt (oscLogKernel lam) (oscLogKernelDeriv lam t) t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have htC : ((t : ℝ) : ℂ) ≠ 0 := by
    simpa using ht0.ne'
  have hlogpos : 0 < Real.log t := Real.log_pos ht
  have hlogC : ((Real.log t : ℝ) : ℂ) ≠ 0 := by
    simpa using hlogpos.ne'
  have h1 := hasDerivAt_invLogC ht
  have h2 := hasDerivAt_logPhase (lam := lam) ht0
  have h3 : HasDerivAt (fun x : ℝ => ((x⁻¹ : ℝ) : ℂ)) (-(((t : ℝ) : ℂ) ^ 2)⁻¹) t := by
    have hbase : HasDerivAt (fun x : ℝ => ((x : ℝ) : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have hinv := hbase.inv htC
    have heq : ((fun x : ℝ => ((x : ℝ) : ℂ))⁻¹) = fun x : ℝ => ((x⁻¹ : ℝ) : ℂ) := by
      funext x
      simp only [Pi.inv_apply]
      push_cast
      ring
    rw [heq] at hinv
    refine hinv.congr_deriv ?_
    field_simp
  have h4 := h2.mul h3
  have h5 := h1.mul h4
  refine h5.congr_deriv ?_
  simp only [Pi.mul_apply, oscLogKernelDeriv, invLogC]
  push_cast
  field_simp
  ring

theorem deriv_oscLogKernel {lam : ℝ} {t : ℝ} (ht : 1 < t) :
    deriv (oscLogKernel lam) t = oscLogKernelDeriv lam t :=
  (hasDerivAt_oscLogKernel ht).deriv

/-! ## Abel summation for the prime phase sum -/

/-- The prime phase partial sum `∑_{p ≤ b} p^{-1-iλ}`. -/
noncomputable def primePhaseSum (lam : ℝ) (b : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 0 ⌊b⌋₊, oscLogKernel lam (k : ℝ) * primeLogCoeff k

theorem theta_natFloor (t : ℝ) : Chebyshev.theta ((⌊t⌋₊ : ℕ) : ℝ) = Chebyshev.theta t := by
  rw [Chebyshev.theta, Chebyshev.theta, Nat.floor_natCast]

theorem continuousAt_oscLogKernelDeriv (lam : ℝ) {x : ℝ} (hx2 : 1 < x) :
    ContinuousAt (oscLogKernelDeriv lam) x := by
  have hlog : 0 < Real.log x := Real.log_pos hx2
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < x := by linarith
    simpa using this.ne'
  have hlogne : ((Real.log x : ℝ) : ℂ) ≠ 0 := by simpa using hlog.ne'
  have hphase := continuousAt_logPhase lam (by linarith : x ≠ 0)
  have hsq : ContinuousAt (fun y : ℝ => (((y : ℝ) : ℂ)) ^ 2)⁻¹ x := by
    refine ContinuousAt.inv₀ ?_ (by simpa using pow_ne_zero 2 hxne)
    exact (Complex.continuous_ofReal.continuousAt).pow 2
  have hinvlog : ContinuousAt invLogC x := by
    refine ContinuousAt.inv₀ ?_ hlogne
    exact Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log (by linarith))
  exact ((hphase.mul hsq).mul
    (((continuousAt_const.mul hinvlog)).sub (hinvlog.pow 2)))

theorem continuousOn_oscLogKernelDeriv (lam : ℝ) {b : ℝ} :
    ContinuousOn (oscLogKernelDeriv lam) (Set.Icc 2 b) := fun x hx =>
  (continuousAt_oscLogKernelDeriv lam (by linarith [hx.1])).continuousWithinAt

theorem primePhaseSum_abel (lam : ℝ) (b : ℝ) :
    primePhaseSum lam b
      = oscLogKernel lam b * ((Chebyshev.theta b : ℝ) : ℂ)
        - ∫ t in Set.Ioc 2 b, oscLogKernelDeriv lam t * ((Chebyshev.theta t : ℝ) : ℂ) := by
  classical
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) b, DifferentiableAt ℝ (oscLogKernel lam) t := by
    intro t ht
    exact (hasDerivAt_oscLogKernel (by linarith [ht.1])).differentiableAt
  have hderivEq : Set.EqOn (deriv (oscLogKernel lam)) (oscLogKernelDeriv lam) (Set.Icc 2 b) := by
    intro t ht
    exact deriv_oscLogKernel (by linarith [ht.1])
  have hint : IntegrableOn (deriv (oscLogKernel lam)) (Set.Icc 2 b) := by
    refine (MeasureTheory.IntegrableOn.congr_fun ?_ hderivEq.symm measurableSet_Icc)
    exact (continuousOn_oscLogKernelDeriv lam).integrableOn_compact isCompact_Icc
  have habel := sum_mul_eq_sub_integral_mul₁ (c := primeLogCoeff) (f := oscLogKernel lam)
    primeLogCoeff_zero primeLogCoeff_one b hdiff hint
  rw [primePhaseSum, habel]
  congr 1
  · rw [sum_primeLogCoeff_eq_theta, theta_natFloor]
  · refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht2 : (2 : ℝ) < t := ht.1
    rw [deriv_oscLogKernel (by linarith), sum_primeLogCoeff_eq_theta, theta_natFloor]

/-! ## The main-term decomposition -/

/-- The absolutely convergent part of the main term. -/
noncomputable def oscLogTail (lam : ℝ) (t : ℝ) : ℂ :=
  logPhase lam t * (((t : ℝ) : ℂ))⁻¹ * (invLogC t) ^ 2

theorem oscLogKernelDeriv_mul_self {lam : ℝ} {t : ℝ} (ht : 1 < t) :
    oscLogKernelDeriv lam t * ((t : ℝ) : ℂ)
      = (-1 - (lam : ℂ) * Complex.I) * oscLogKernel lam t - oscLogTail lam t := by
  have htC : ((t : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < t := by linarith
    simpa using this.ne'
  rw [oscLogKernelDeriv, oscLogKernel, oscLogTail]
  push_cast
  field_simp

theorem norm_oscLogTail (lam : ℝ) {t : ℝ} (ht : 1 < t) :
    ‖oscLogTail lam t‖ = (t * (Real.log t) ^ 2)⁻¹ := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog : 0 < Real.log t := Real.log_pos ht
  rw [oscLogTail, norm_mul, norm_mul, norm_logPhase, one_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ht0, invLogC, norm_pow, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hlog]
  field_simp

theorem integrableOn_oscLogTail (lam : ℝ) :
    IntegrableOn (oscLogTail lam) (Set.Ioi 2) := by
  have hmeas : AEStronglyMeasurable (oscLogTail lam) (volume.restrict (Set.Ioi 2)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro x hx
    have hx2 : (2 : ℝ) < x := hx
    have hlog : 0 < Real.log x := Real.log_pos (by linarith)
    have hxne : ((x : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < x := by linarith
      simpa using this.ne'
    have hlogne : ((Real.log x : ℝ) : ℂ) ≠ 0 := by simpa using hlog.ne'
    refine ContinuousAt.continuousWithinAt ?_
    have hinvlog : ContinuousAt invLogC x := by
      refine ContinuousAt.inv₀ ?_ hlogne
      exact Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log (by linarith))
    exact ((continuousAt_logPhase lam (by linarith)).mul
      (Complex.continuous_ofReal.continuousAt.inv₀ hxne)).mul (hinvlog.pow 2)
  refine Integrable.mono integrableOn_logTailWeight hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx2 : (2 : ℝ) < x := hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  rw [norm_oscLogTail lam (by linarith), Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (x * Real.log x ^ 2)⁻¹)]

/-! ## The boundary term and the error integral -/

theorem norm_oscLogKernel (lam : ℝ) {t : ℝ} (ht : 1 < t) :
    ‖oscLogKernel lam t‖ = (t * Real.log t)⁻¹ := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog : 0 < Real.log t := Real.log_pos ht
  rw [oscLogKernel, norm_mul, norm_mul, norm_logPhase, one_mul, invLogC, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < t⁻¹)]
  field_simp

theorem exists_theta_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ b : ℝ in atTop, |Chebyshev.theta b| ≤ K * b := by
  obtain ⟨c, hc0, hO⟩ := RHTower.Sieve.chebyshevTheta_sub_id_isBigO
  rw [Asymptotics.isBigO_iff] at hO
  obtain ⟨C, hC⟩ := hO
  refine ⟨|C| + 1, by positivity, ?_⟩
  filter_upwards [hC, Filter.eventually_ge_atTop (1 : ℝ)] with b hb hb1
  have hbpos : (0 : ℝ) < b := by linarith
  have hexp : Real.exp (-c * Real.sqrt (Real.log b)) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have hs : 0 ≤ Real.sqrt (Real.log b) := Real.sqrt_nonneg _
    nlinarith
  have hnormb : ‖b * Real.exp (-c * Real.sqrt (Real.log b))‖
      = b * Real.exp (-c * Real.sqrt (Real.log b)) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [Pi.sub_apply, id_eq, Real.norm_eq_abs, hnormb] at hb
  have hstep : |Chebyshev.theta b - b| ≤ |C| * b := by
    refine hb.trans ?_
    calc C * (b * Real.exp (-c * Real.sqrt (Real.log b)))
        ≤ |C| * (b * Real.exp (-c * Real.sqrt (Real.log b))) := by
          exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * (b * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg C)
          exact mul_le_mul_of_nonneg_left hexp hbpos.le
      _ = |C| * b := by ring
  have habs : |Chebyshev.theta b| ≤ |Chebyshev.theta b - b| + |b| := by
    calc |Chebyshev.theta b| = |(Chebyshev.theta b - b) + b| := by ring_nf
      _ ≤ |Chebyshev.theta b - b| + |b| := abs_add_le _ _
  rw [abs_of_pos hbpos] at habs
  nlinarith

theorem tendsto_oscLogKernel_mul_theta (lam : ℝ) :
    Tendsto (fun b : ℝ => oscLogKernel lam b * ((Chebyshev.theta b : ℝ) : ℂ))
      atTop (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := exists_theta_le
  have hbound : ∀ᶠ b : ℝ in atTop,
      ‖oscLogKernel lam b * ((Chebyshev.theta b : ℝ) : ℂ)‖ ≤ K * (Real.log b)⁻¹ := by
    filter_upwards [hK, Filter.eventually_gt_atTop (1 : ℝ)] with b hb hb1
    have hbpos : (0 : ℝ) < b := by linarith
    have hlog : 0 < Real.log b := Real.log_pos hb1
    rw [norm_mul, norm_oscLogKernel lam hb1, Complex.norm_real, Real.norm_eq_abs]
    rw [inv_mul_eq_div, div_le_iff₀ (by positivity)]
    calc |Chebyshev.theta b| ≤ K * b := hb
      _ = K * (Real.log b)⁻¹ * (b * Real.log b) := by field_simp
  have hlim : Tendsto (fun b : ℝ => K * (Real.log b)⁻¹) atTop (𝓝 0) := by
    have := Real.tendsto_log_atTop.inv_tendsto_atTop
    simpa using this.const_mul K
  refine squeeze_zero_norm' hbound hlim

theorem norm_oscLogKernelDeriv_le (lam : ℝ) {t : ℝ} (ht : 2 ≤ t) :
    ‖oscLogKernelDeriv lam t‖
      ≤ ((1 + |lam|) * (Real.log 2)⁻¹ + ((Real.log 2)⁻¹) ^ 2) * (t ^ 2)⁻¹ := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hlogpos : 0 < Real.log t := by linarith
  have hinv : ‖invLogC t‖ = (Real.log t)⁻¹ := by
    rw [invLogC, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogpos]
  have hinvle : (Real.log t)⁻¹ ≤ (Real.log 2)⁻¹ := by
    exact (inv_le_inv₀ hlogpos hlog2).mpr hlogt
  have hcoeff : ‖(-1 - (lam : ℂ) * Complex.I)‖ ≤ 1 + |lam| := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_neg, norm_one, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs]
  have hbody : ‖(-1 - (lam : ℂ) * Complex.I) * invLogC t - (invLogC t) ^ 2‖
      ≤ (1 + |lam|) * (Real.log 2)⁻¹ + ((Real.log 2)⁻¹) ^ 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_mul, hinv, norm_pow, hinv]
    have h1 : ‖(-1 - (lam : ℂ) * Complex.I)‖ * (Real.log t)⁻¹ ≤ (1 + |lam|) * (Real.log 2)⁻¹ :=
      mul_le_mul hcoeff hinvle (by positivity) (by positivity)
    have h2 : ((Real.log t)⁻¹) ^ 2 ≤ ((Real.log 2)⁻¹) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hinvle 2
    linarith
  rw [oscLogKernelDeriv, norm_mul, norm_mul, norm_logPhase, one_mul, norm_inv, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right hbody (by positivity)

theorem integrableOn_oscLogKernelDeriv_mul_thetaError (lam : ℝ) :
    IntegrableOn (fun t : ℝ => oscLogKernelDeriv lam t * (((Chebyshev.theta t - t : ℝ)) : ℂ))
      (Set.Ioi 2) := by
  classical
  obtain ⟨c, hc0, hO⟩ := RHTower.Sieve.chebyshevTheta_sub_id_isBigO
  have hKcont : ContinuousOn (oscLogKernelDeriv lam) (Set.Ici 2) := by
    intro x hx
    have hx2 : (2 : ℝ) ≤ x := hx
    exact (continuousAt_oscLogKernelDeriv lam (by linarith)).continuousWithinAt
  have hKloc : LocallyIntegrableOn (oscLogKernelDeriv lam) (Set.Ici 2) :=
    hKcont.locallyIntegrableOn measurableSet_Ici
  have hloc1 : LocallyIntegrableOn (fun t : ℝ => oscLogKernelDeriv lam t *
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogCoeff k) (Set.Ici 2) :=
    locallyIntegrableOn_mul_sum_Icc (c := primeLogCoeff) (m := 0) (by norm_num) hKloc
  have hloc2 : LocallyIntegrableOn
      (fun t : ℝ => oscLogKernelDeriv lam t * ((t : ℝ) : ℂ)) (Set.Ici 2) := by
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ici
    exact hKcont.mul (Complex.continuous_ofReal.continuousOn)
  have hfun : (fun t : ℝ => oscLogKernelDeriv lam t * (((Chebyshev.theta t - t : ℝ)) : ℂ))
      = (fun t : ℝ => oscLogKernelDeriv lam t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogCoeff k) -
        (fun t : ℝ => oscLogKernelDeriv lam t * ((t : ℝ) : ℂ)) := by
    funext t
    simp only [Pi.sub_apply]
    rw [sum_primeLogCoeff_eq_theta, theta_natFloor]
    push_cast
    ring
  have hloc : LocallyIntegrableOn
      (fun t : ℝ => oscLogKernelDeriv lam t * (((Chebyshev.theta t - t : ℝ)) : ℂ))
      (Set.Ici 2) := by
    rw [hfun]
    exact hloc1.sub hloc2
  set Cb : ℝ := (1 + |lam|) * (Real.log 2)⁻¹ + ((Real.log 2)⁻¹) ^ 2 with hCb
  have hCb0 : 0 ≤ Cb := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [hCb]
    positivity
  have hbigO : (fun t : ℝ => oscLogKernelDeriv lam t * (((Chebyshev.theta t - t : ℝ)) : ℂ))
      =O[atTop] fun t : ℝ => Real.exp (-c * Real.sqrt (Real.log t)) / t := by
    rw [Asymptotics.isBigO_iff] at hO ⊢
    obtain ⟨C', hC'⟩ := hO
    refine ⟨Cb * |C'|, ?_⟩
    filter_upwards [hC', Filter.eventually_ge_atTop (2 : ℝ)] with t ht ht2
    have ht0 : (0 : ℝ) < t := by linarith
    have hexp : (0 : ℝ) < Real.exp (-c * Real.sqrt (Real.log t)) := Real.exp_pos _
    have hnormRHS : ‖Real.exp (-c * Real.sqrt (Real.log t)) / t‖
        = Real.exp (-c * Real.sqrt (Real.log t)) / t := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hthetaBound : |Chebyshev.theta t - t|
        ≤ |C'| * (t * Real.exp (-c * Real.sqrt (Real.log t))) := by
      have hn : ‖t * Real.exp (-c * Real.sqrt (Real.log t))‖
          = t * Real.exp (-c * Real.sqrt (Real.log t)) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [Pi.sub_apply, id_eq, Real.norm_eq_abs, hn] at ht
      refine ht.trans ?_
      exact mul_le_mul_of_nonneg_right (le_abs_self C') (by positivity)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormRHS]
    calc ‖oscLogKernelDeriv lam t‖ * |Chebyshev.theta t - t|
        ≤ (Cb * (t ^ 2)⁻¹) * (|C'| * (t * Real.exp (-c * Real.sqrt (Real.log t)))) := by
          refine mul_le_mul (norm_oscLogKernelDeriv_le lam ht2) hthetaBound (abs_nonneg _) ?_
          positivity
      _ = Cb * |C'| * (Real.exp (-c * Real.sqrt (Real.log t)) / t) := by
          field_simp
  have hIAF : MeasureTheory.IntegrableAtFilter
      (fun t : ℝ => Real.exp (-c * Real.sqrt (Real.log t)) / t) atTop :=
    ⟨Set.Ioi 2, Ioi_mem_atTop 2, integrableOn_pntErrorWeight hc0⟩
  exact (hloc.integrableOn_of_isBigO_atTop hbigO hIAF).mono_set Set.Ioi_subset_Ici_self

/-! ## Convergence of the prime phase sum -/

theorem intervalIntegrable_oscLogKernel (lam : ℝ) {b : ℝ} (hb : 2 ≤ b) :
    IntervalIntegrable (oscLogKernel lam) volume 2 b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hb]
  intro x hx
  have hx2 : (2 : ℝ) ≤ x := hx.1
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogne : ((Real.log x : ℝ) : ℂ) ≠ 0 := by simpa using hlog.ne'
  refine ContinuousAt.continuousWithinAt ?_
  have hinvlog : ContinuousAt invLogC x := by
    refine ContinuousAt.inv₀ ?_ hlogne
    exact Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log (by linarith))
  refine hinvlog.mul ((continuousAt_logPhase lam (by linarith)).mul ?_)
  exact Complex.continuous_ofReal.continuousAt.comp (continuousAt_inv₀ (by linarith))

theorem intervalIntegrable_oscLogTail (lam : ℝ) {b : ℝ} (hb : 2 ≤ b) :
    IntervalIntegrable (oscLogTail lam) volume 2 b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hb]
  intro x hx
  have hx2 : (2 : ℝ) ≤ x := hx.1
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < x := by linarith
    simpa using this.ne'
  have hlogne : ((Real.log x : ℝ) : ℂ) ≠ 0 := by simpa using hlog.ne'
  refine ContinuousAt.continuousWithinAt ?_
  have hinvlog : ContinuousAt invLogC x := by
    refine ContinuousAt.inv₀ ?_ hlogne
    exact Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log (by linarith))
  exact ((continuousAt_logPhase lam (by linarith)).mul
    (Complex.continuous_ofReal.continuousAt.inv₀ hxne)).mul (hinvlog.pow 2)

/-- **The prime-ordered series `∑_p p^{-1-iλ}` converges for every nonzero height.** -/
theorem exists_tendsto_primePhaseSum {lam : ℝ} (hlam : lam ≠ 0) :
    ∃ L : ℂ, Tendsto (fun b : ℝ => primePhaseSum lam b) atTop (𝓝 L) := by
  obtain ⟨L₁, hL₁⟩ := exists_tendsto_integral_oscLogKernel hlam
  have hTail : Tendsto (fun b : ℝ => ∫ t in (2 : ℝ)..b, oscLogTail lam t) atTop
      (𝓝 (∫ t in Set.Ioi (2 : ℝ), oscLogTail lam t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi (2 : ℝ)
      (integrableOn_oscLogTail lam) Filter.tendsto_id
  have hErr : Tendsto (fun b : ℝ => ∫ t in (2 : ℝ)..b,
      oscLogKernelDeriv lam t * (((Chebyshev.theta t - t : ℝ)) : ℂ)) atTop
      (𝓝 (∫ t in Set.Ioi (2 : ℝ),
        oscLogKernelDeriv lam t * (((Chebyshev.theta t - t : ℝ)) : ℂ))) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi (2 : ℝ)
      (integrableOn_oscLogKernelDeriv_mul_thetaError lam) Filter.tendsto_id
  refine ⟨0 - ((-1 - (lam : ℂ) * Complex.I) * L₁ -
    (∫ t in Set.Ioi (2 : ℝ), oscLogTail lam t) +
    ∫ t in Set.Ioi (2 : ℝ),
      oscLogKernelDeriv lam t * (((Chebyshev.theta t - t : ℝ)) : ℂ)), ?_⟩
  have hcomb := (tendsto_oscLogKernel_mul_theta lam).sub
    (((hL₁.const_mul (-1 - (lam : ℂ) * Complex.I)).sub hTail).add hErr)
  refine hcomb.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with b hb
  have habel := primePhaseSum_abel lam b
  have hIocEq : ∫ t in Set.Ioc (2 : ℝ) b,
      oscLogKernelDeriv lam t * ((Chebyshev.theta t : ℝ) : ℂ)
      = ∫ t in (2 : ℝ)..b, oscLogKernelDeriv lam t * ((Chebyshev.theta t : ℝ) : ℂ) :=
    (intervalIntegral.integral_of_le hb).symm
  have hsplitFun : ∀ t : ℝ, 1 < t →
      oscLogKernelDeriv lam t * ((Chebyshev.theta t : ℝ) : ℂ)
        = ((-1 - (lam : ℂ) * Complex.I) * oscLogKernel lam t - oscLogTail lam t)
          + oscLogKernelDeriv lam t * (((Chebyshev.theta t - t : ℝ)) : ℂ) := by
    intro t ht
    rw [← oscLogKernelDeriv_mul_self ht]
    push_cast
    ring
  have hIntKernel := intervalIntegrable_oscLogKernel lam hb
  have hIntTail := intervalIntegrable_oscLogTail lam hb
  have hIntErr : IntervalIntegrable
      (fun t : ℝ => oscLogKernelDeriv lam t * (((Chebyshev.theta t - t : ℝ)) : ℂ))
      volume 2 b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb]
    exact (integrableOn_oscLogKernelDeriv_mul_thetaError lam).mono_set Set.Ioc_subset_Ioi_self
  have hsplit : ∫ t in (2 : ℝ)..b, oscLogKernelDeriv lam t * ((Chebyshev.theta t : ℝ) : ℂ)
      = ((-1 - (lam : ℂ) * Complex.I) * (∫ t in (2 : ℝ)..b, oscLogKernel lam t)
          - ∫ t in (2 : ℝ)..b, oscLogTail lam t)
        + ∫ t in (2 : ℝ)..b, oscLogKernelDeriv lam t * (((Chebyshev.theta t - t : ℝ)) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (hIntKernel.const_mul _) hIntTail,
      ← intervalIntegral.integral_add ((hIntKernel.const_mul _).sub hIntTail) hIntErr]
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le hb] at ht
    exact hsplitFun t (by linarith [ht.1])
  rw [habel, hIocEq, hsplit]

theorem natCast_cpow_neg_one_sub (lam : ℝ) {k : ℕ} (hk : 0 < k) :
    ((k : ℂ)) ^ (-1 - (lam : ℂ) * Complex.I) = ((k⁻¹ : ℝ) : ℂ) * logPhase lam (k : ℝ) := by
  have hne : ((k : ℂ)) ≠ 0 := by exact_mod_cast hk.ne'
  have hkR : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hsplit : (-1 - (lam : ℂ) * Complex.I)
      = (((-1 : ℝ)) : ℂ) + (-(lam : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hsplit, Complex.cpow_add _ _ hne]
  congr 1
  · rw [show ((k : ℕ) : ℂ) = ((((k : ℕ) : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hkR, Real.rpow_neg_one]
  · rw [logPhase, Complex.cpow_def_of_ne_zero hne, ← Complex.natCast_log]
    congr 1
    push_cast
    ring

theorem primePhaseSum_eq_cpow_sum (lam : ℝ) (b : ℝ) :
    primePhaseSum lam b
      = ∑ k ∈ Finset.Icc 0 ⌊b⌋₊ with k.Prime,
          ((k : ℂ)) ^ (-1 - (lam : ℂ) * Complex.I) := by
  classical
  rw [primePhaseSum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k.Prime
  · have hk2 : 2 ≤ k := hk.two_le
    have hkR : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk.one_lt
    have hlog : 0 < Real.log ((k : ℕ) : ℝ) := Real.log_pos hkR
    have hlogne : ((Real.log ((k : ℕ) : ℝ) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hlog.ne'
    rw [if_pos hk, primeLogCoeff, if_pos hk, oscLogKernel, invLogC,
      natCast_cpow_neg_one_sub lam hk.pos]
    field_simp
  · rw [if_neg hk, primeLogCoeff, if_neg hk, mul_zero]

/-- **Convergence of the prime zeta series on the one-line, off the pole.**  For every nonzero
height the prime-ordered partial sums of `p^{-1-iλ}` converge. -/
theorem exists_tendsto_primeCpowSum {lam : ℝ} (hlam : lam ≠ 0) :
    ∃ L : ℂ, Tendsto (fun b : ℝ =>
      ∑ k ∈ Finset.Icc 0 ⌊b⌋₊ with k.Prime,
        ((k : ℂ)) ^ (-1 - (lam : ℂ) * Complex.I)) atTop (nhds L) := by
  obtain ⟨L, hL⟩ := exists_tendsto_primePhaseSum hlam
  exact ⟨L, hL.congr fun b => primePhaseSum_eq_cpow_sum lam b⟩

end RHTower
