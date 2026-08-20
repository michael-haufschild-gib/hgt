import GaloisForLFunctions.RHTower.PrimeRpowAbelSummation
import GaloisForLFunctions.RHTower.PrimeRpowLogSumAsymptotic
import GaloisForLFunctions.RHTower.Sieve.ChebyshevThetaBigO
import GaloisForLFunctions.RHTower.OscillatoryLogIntegral
import Mathlib

/-!
# The higher-order Mertens theorem

For every `k ≥ 1` the prime logarithmic-power sum has a convergent normalized limit

`∑_{p ≤ x} (log p)^k / p - (log x)^k / k → C_k`.

The proof is Abel summation of the corpus prime-log weight against the Chebyshev function `θ`,
splitting `θ(t) = t (1 + thetaError t)`.  The elementary part integrates exactly, with primitive
`(log t)^m - (log t)^{m+1}/(m+1)`, and the remaining error integrand `t f_m'(t) thetaError t` is
absolutely integrable on `(2, ∞)` because the de la Vallée Poussin error beats every logarithmic
power: the device `exp (-c √u) ≤ (2m)! / (c^{2m} u^m)` gives
`(log t)^m exp (-c √log t) / t ∈ L¹(2, ∞)`.

Both devices are reusable, and the resulting constants `C_k` are the higher-order Mertens
constants appearing as the endpoint jet coefficients of the prime boundary layer.
-/

open Filter Topology Set MeasureTheory Asymptotics

namespace RHTower

noncomputable section

/-! ## Logarithmic powers against the de la Vallée Poussin weight -/

/-- Every power of the argument is dominated by the square-root exponential. -/
theorem exp_neg_sqrt_le_pow {c : ℝ} (hc : 0 < c) (m : ℕ) {u : ℝ} (hu : 0 < u) :
    Real.exp (-c * Real.sqrt u) ≤ (((2 * m).factorial : ℕ) : ℝ) / (c ^ (2 * m) * u ^ m) := by
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hcs : 0 < c * Real.sqrt u := by positivity
  have hbound := Real.sum_le_exp_of_nonneg hcs.le (2 * m + 1)
  have hsingle : (c * Real.sqrt u) ^ (2 * m) / (((2 * m).factorial : ℕ) : ℝ)
      ≤ ∑ i ∈ Finset.range (2 * m + 1), (c * Real.sqrt u) ^ i / ((i.factorial : ℕ) : ℝ) := by
    refine Finset.single_le_sum
      (f := fun i => (c * Real.sqrt u) ^ i / ((i.factorial : ℕ) : ℝ))
      (fun i _ => by positivity) (Finset.self_mem_range_succ (2 * m))
  have hterm : (c * Real.sqrt u) ^ (2 * m) / (((2 * m).factorial : ℕ) : ℝ)
      ≤ Real.exp (c * Real.sqrt u) := le_trans hsingle hbound
  have hsu : (Real.sqrt u) ^ (2 * m) = u ^ m := by
    rw [pow_mul, Real.sq_sqrt hu.le]
  have hpow : (c * Real.sqrt u) ^ (2 * m) = c ^ (2 * m) * u ^ m := by
    rw [mul_pow, hsu]
  have hfac : (0 : ℝ) < (((2 * m).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 * m)
  rw [hpow] at hterm
  have hA : (0 : ℝ) < c ^ (2 * m) * u ^ m / (((2 * m).factorial : ℕ) : ℝ) := by positivity
  rw [neg_mul, Real.exp_neg]
  calc (Real.exp (c * Real.sqrt u))⁻¹
      ≤ (c ^ (2 * m) * u ^ m / (((2 * m).factorial : ℕ) : ℝ))⁻¹ := by gcongr
    _ = (((2 * m).factorial : ℕ) : ℝ) / (c ^ (2 * m) * u ^ m) := by rw [inv_div]

/-- Any logarithmic power against the prime-number-theorem error weight is integrable. -/
theorem integrableOn_logPow_pntErrorWeight {c : ℝ} (hc : 0 < c) (m : ℕ) :
    IntegrableOn
      (fun t : ℝ => (Real.log t) ^ m * Real.exp (-c * Real.sqrt (Real.log t)) / t) (Ioi 2) := by
  set K : ℝ := (((2 * (m + 2)).factorial : ℕ) : ℝ) / c ^ (2 * (m + 2)) with hK
  have hKpos : 0 < K := by
    have : (0 : ℝ) < (((2 * (m + 2)).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    positivity
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (Real.log t) ^ m * Real.exp (-c * Real.sqrt (Real.log t)) / t)
      (volume.restrict (Ioi 2)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro x hx
    have hx2 : (2 : ℝ) < x := hx
    have hx0 : x ≠ 0 := by intro h; rw [h] at hx2; linarith
    have h1 : ContinuousAt (fun t : ℝ => Real.log t) x := Real.continuousAt_log hx0
    have h2 : ContinuousAt (fun t : ℝ => Real.sqrt (Real.log t)) x :=
      Real.continuous_sqrt.continuousAt.comp h1
    refine ContinuousAt.continuousWithinAt ?_
    exact ((h1.pow m).mul
      (Real.continuous_exp.continuousAt.comp (h2.const_mul (-c)))).div continuousAt_id hx0
  refine Integrable.mono (integrableOn_logTailWeight.const_mul K) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx2 : (2 : ℝ) < x := hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hEle : Real.exp (-c * Real.sqrt (Real.log x)) ≤ K / (Real.log x) ^ (m + 2) := by
    have h := exp_neg_sqrt_le_pow hc (m + 2) hlog
    rwa [hK, div_div]
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.log x) ^ m *
      Real.exp (-c * Real.sqrt (Real.log x)) / x),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ K * (x * Real.log x ^ 2)⁻¹)]
  have hstep : (Real.log x) ^ m * Real.exp (-c * Real.sqrt (Real.log x)) / x
      ≤ (Real.log x) ^ m * (K / (Real.log x) ^ (m + 2)) / x := by
    gcongr
  refine hstep.trans_eq ?_
  field_simp
  ring

/-! ## The Abel weight `(log t)^m / t` -/

/-- The Abel weight `f_m(t) = (log t)^m / t`. -/
def logPowDivId (m : ℕ) (t : ℝ) : ℝ := (Real.log t) ^ m / t

/-- Its derivative. -/
def derivLogPowDivId (m : ℕ) (t : ℝ) : ℝ :=
  ((m : ℝ) * (Real.log t) ^ (m - 1) - (Real.log t) ^ m) / t ^ 2

theorem hasDerivAt_logPowDivId (m : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (logPowDivId m) (derivLogPowDivId m t) t := by
  have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht.ne'
  have hpow : HasDerivAt (fun s : ℝ => (Real.log s) ^ m)
      ((m : ℝ) * (Real.log t) ^ (m - 1) * t⁻¹) t := hlog.pow m
  have hinv : HasDerivAt (fun s : ℝ => s⁻¹) (-(t ^ 2)⁻¹) t := hasDerivAt_inv ht.ne'
  have hmul := hpow.mul hinv
  have hfun : ((fun s : ℝ => (Real.log s) ^ m) * fun s : ℝ => s⁻¹) = logPowDivId m := by
    funext s
    simp only [Pi.mul_apply]
    rw [logPowDivId, div_eq_mul_inv]
  rw [hfun] at hmul
  refine hmul.congr_deriv ?_
  rw [derivLogPowDivId]
  field_simp
  ring

/-- The primitive of `t ↦ t · f_m'(t)`. -/
def logPowIdPrimitive (m : ℕ) (t : ℝ) : ℝ :=
  (Real.log t) ^ m - (Real.log t) ^ (m + 1) / ((m : ℝ) + 1)

theorem hasDerivAt_logPowIdPrimitive (m : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (logPowIdPrimitive m) (t * derivLogPowDivId m t) t := by
  have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht.ne'
  have h1 : HasDerivAt (fun s : ℝ => (Real.log s) ^ m)
      ((m : ℝ) * (Real.log t) ^ (m - 1) * t⁻¹) t := hlog.pow m
  have h2 : HasDerivAt (fun s : ℝ => (Real.log s) ^ (m + 1))
      (((m + 1 : ℕ) : ℝ) * (Real.log t) ^ (m + 1 - 1) * t⁻¹) t := hlog.pow (m + 1)
  have h3 := h1.sub (h2.div_const ((m : ℝ) + 1))
  have hfun : ((fun s : ℝ => (Real.log s) ^ m)
      - fun s : ℝ => (Real.log s) ^ (m + 1) / ((m : ℝ) + 1)) = logPowIdPrimitive m := by
    funext s
    simp only [Pi.sub_apply]
    rw [logPowIdPrimitive]
  rw [hfun] at h3
  refine h3.congr_deriv ?_
  rw [derivLogPowDivId]
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp

theorem continuousOn_derivLogPowDivId (m : ℕ) {x : ℝ} :
    ContinuousOn (derivLogPowDivId m) (Icc 2 x) := by
  intro t ht
  have ht0 : t ≠ 0 := by
    have := ht.1
    intro h
    rw [h] at this
    linarith
  refine ContinuousAt.continuousWithinAt ?_
  have hlog : ContinuousAt Real.log t := Real.continuousAt_log ht0
  refine ContinuousAt.div (((hlog.pow (m - 1)).const_mul (m : ℝ)).sub (hlog.pow m)) ?_ ?_
  · exact continuousAt_id.pow 2
  · positivity

theorem integrableOn_deriv_logPowDivId (m : ℕ) {x : ℝ} :
    IntegrableOn (deriv (logPowDivId m)) (Icc 2 x) := by
  refine (continuousOn_derivLogPowDivId (m := m) (x := x)).integrableOn_Icc.congr_fun
    (fun t ht => ?_) measurableSet_Icc
  have ht0 : (0 : ℝ) < t := by
    have := ht.1
    linarith
  exact ((hasDerivAt_logPowDivId m ht0).deriv).symm

/-! ## Abel summation of the prime logarithmic-power sum -/

/-- `(log p)^k / p`, supported on primes. -/
def primeLogPowWeight (k n : ℕ) : ℝ := if n.Prime then (Real.log n) ^ k / n else 0

/-- `∑_{2 < p ≤ x} (log p)^k / p`. -/
def primeLogPowSumIoc (k : ℕ) (x : ℝ) : ℝ := ∑ n ∈ Finset.Ioc 2 ⌊x⌋₊, primeLogPowWeight k n

/-- `∑_{p ≤ x} (log p)^k / p`. -/
def primeLogPowSum (k : ℕ) (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeLogPowWeight k n

theorem logPowDivId_mul_primeLogWeight (m n : ℕ) :
    logPowDivId m n * primeLogWeight n = primeLogPowWeight (m + 1) n := by
  rw [logPowDivId, primeLogWeight, primeLogPowWeight]
  by_cases hp : n.Prime
  · rw [if_pos hp, if_pos hp, pow_succ]
    ring
  · rw [if_neg hp, if_neg hp, mul_zero]

theorem primeLogPowSumIoc_eq (m : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    primeLogPowSumIoc (m + 1) x
      = logPowDivId m x * Chebyshev.theta x - logPowDivId m 2 * Chebyshev.theta 2
        - ∫ t in Ioc (2 : ℝ) x, derivLogPowDivId m t * Chebyshev.theta t := by
  have habel := sum_mul_eq_sub_sub_integral_mul (𝕜 := ℝ) primeLogWeight
    (f := logPowDivId m) (a := (2 : ℝ)) (b := x) (by norm_num) hx
    (fun t ht => (hasDerivAt_logPowDivId m (by have := ht.1; linarith)).differentiableAt)
    (integrableOn_deriv_logPowDivId m)
  simp only [sum_primeLogWeight_eq_theta] at habel
  rw [show (⌊(2 : ℝ)⌋₊) = 2 from by norm_num] at habel
  have hint : (∫ t in Ioc (2 : ℝ) x, deriv (logPowDivId m) t * Chebyshev.theta t)
      = ∫ t in Ioc (2 : ℝ) x, derivLogPowDivId m t * Chebyshev.theta t := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    rw [(hasDerivAt_logPowDivId m (by have := ht.1; linarith)).deriv]
  rw [primeLogPowSumIoc, ← hint, ← habel]
  exact Finset.sum_congr rfl fun n _ => (logPowDivId_mul_primeLogWeight m n).symm

/-! ## The error integrand -/

/-- The Abel error integrand `t f_m'(t) (θ(t)/t - 1)`. -/
def logPowThetaErrorIntegrand (m : ℕ) (t : ℝ) : ℝ :=
  derivLogPowDivId m t * t * thetaError t

theorem measurable_derivLogPowDivId (m : ℕ) : Measurable (derivLogPowDivId m) := by
  refine Measurable.div ?_ ?_
  · exact ((Real.measurable_log.pow_const (m - 1)).const_mul (m : ℝ)).sub
      (Real.measurable_log.pow_const m)
  · exact measurable_id.pow_const 2

theorem measurable_logPowThetaErrorIntegrand (m : ℕ) :
    Measurable (logPowThetaErrorIntegrand m) :=
  ((measurable_derivLogPowDivId m).mul measurable_id).mul measurable_thetaError

theorem integrableOn_logPowThetaErrorIntegrand_Icc (m : ℕ) (x : ℝ) :
    IntegrableOn (logPowThetaErrorIntegrand m) (Icc 2 x) := by
  have hcont : ContinuousOn (fun t : ℝ => derivLogPowDivId m t * t) (Icc 2 x) :=
    (continuousOn_derivLogPowDivId m).mul continuousOn_id
  have h := ((integrableOn_thetaError x).mul_continuousOn hcont isCompact_Icc)
  refine h.congr_fun (fun t _ => ?_) measurableSet_Icc
  rw [logPowThetaErrorIntegrand]
  ring

/-- The Abel error integrand is integrable on the whole ray. -/
theorem integrableOn_logPowThetaErrorIntegrand (m : ℕ) :
    IntegrableOn (logPowThetaErrorIntegrand m) (Ioi (2 : ℝ)) := by
  obtain ⟨c, hc0, hO⟩ := Sieve.chebyshevTheta_sub_id_isBigO
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hO
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (hC.and (Filter.eventually_ge_atTop (2 : ℝ)))
  have hT2 : (2 : ℝ) ≤ T := (hT T le_rfl).2
  have hsplit : Ioc (2 : ℝ) T ∪ Ioi T = Ioi (2 : ℝ) := Ioc_union_Ioi_eq_Ioi hT2
  rw [← hsplit]
  refine IntegrableOn.union ?_ ?_
  · exact (integrableOn_logPowThetaErrorIntegrand_Icc m T).mono_set Ioc_subset_Icc_self
  · set g : ℝ → ℝ := fun t : ℝ =>
      |C| * ((m : ℝ) * ((Real.log t) ^ (m - 1) *
          Real.exp (-c * Real.sqrt (Real.log t)) / t))
        + |C| * ((Real.log t) ^ m * Real.exp (-c * Real.sqrt (Real.log t)) / t) with hg
    have hgint : IntegrableOn g (Ioi (2 : ℝ)) := by
      refine Integrable.add ?_ ?_
      · exact ((integrableOn_logPow_pntErrorWeight hc0 (m - 1)).const_mul (m : ℝ)).const_mul |C|
      · exact (integrableOn_logPow_pntErrorWeight hc0 m).const_mul |C|
    refine Integrable.mono (hgint.mono_set (Ioi_subset_Ioi hT2))
      ((measurable_logPowThetaErrorIntegrand m).aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htT : T ≤ t := le_of_lt ht
    have ht2 : (2 : ℝ) < t := lt_of_le_of_lt hT2 ht
    have htpos : (0 : ℝ) < t := by linarith
    have hlog : 0 < Real.log t := Real.log_pos (by linarith)
    have hbound := (hT t htT).1
    have herr : |thetaError t| ≤ |C| * Real.exp (-c * Real.sqrt (Real.log t)) := by
      have h1 : ‖(Chebyshev.theta - id : ℝ → ℝ) t‖
          ≤ C * ‖t * Real.exp (-c * Real.sqrt (Real.log t))‖ := hbound
      have h2 : ‖t * Real.exp (-c * Real.sqrt (Real.log t))‖
          = t * Real.exp (-c * Real.sqrt (Real.log t)) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h3 : ‖(Chebyshev.theta - id : ℝ → ℝ) t‖ = |Chebyshev.theta t - t| := by
        simp [Real.norm_eq_abs]
      rw [h2, h3] at h1
      have hnum : |Chebyshev.theta t - t|
          ≤ |C| * (t * Real.exp (-c * Real.sqrt (Real.log t))) :=
        h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
      have hdiv : thetaError t = (Chebyshev.theta t - t) / t := by
        rw [thetaError]
        field_simp
      rw [hdiv, abs_div, abs_of_pos htpos, div_le_iff₀ htpos]
      calc |Chebyshev.theta t - t|
          ≤ |C| * (t * Real.exp (-c * Real.sqrt (Real.log t))) := hnum
        _ = |C| * Real.exp (-c * Real.sqrt (Real.log t)) * t := by ring
    have hA : (0 : ℝ) ≤ (m : ℝ) * (Real.log t) ^ (m - 1) := by
      exact mul_nonneg (Nat.cast_nonneg m) (pow_nonneg hlog.le _)
    have hB : (0 : ℝ) ≤ (Real.log t) ^ m := pow_nonneg hlog.le _
    have hfac : |derivLogPowDivId m t * t|
        ≤ ((m : ℝ) * (Real.log t) ^ (m - 1) + (Real.log t) ^ m) / t := by
      have hval : derivLogPowDivId m t * t
          = ((m : ℝ) * (Real.log t) ^ (m - 1) - (Real.log t) ^ m) / t := by
        rw [derivLogPowDivId]
        field_simp
      rw [hval, abs_div, abs_of_pos htpos]
      have hnum : |(m : ℝ) * (Real.log t) ^ (m - 1) - (Real.log t) ^ m|
          ≤ (m : ℝ) * (Real.log t) ^ (m - 1) + (Real.log t) ^ m := by
        rw [abs_le]
        constructor <;> linarith
      exact div_le_div_of_nonneg_right hnum htpos.le
    have he : (0 : ℝ) < Real.exp (-c * Real.sqrt (Real.log t)) := Real.exp_pos _
    have hgnn : 0 ≤ g t := by
      have t1 : (0 : ℝ) ≤ (m : ℝ) *
          ((Real.log t) ^ (m - 1) * Real.exp (-c * Real.sqrt (Real.log t)) / t) :=
        mul_nonneg (Nat.cast_nonneg m)
          (div_nonneg (mul_nonneg (pow_nonneg hlog.le _) he.le) htpos.le)
      have t2 : (0 : ℝ) ≤ (Real.log t) ^ m *
          Real.exp (-c * Real.sqrt (Real.log t)) / t :=
        div_nonneg (mul_nonneg hB he.le) htpos.le
      rw [hg]
      exact add_nonneg (mul_nonneg (abs_nonneg C) t1) (mul_nonneg (abs_nonneg C) t2)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hgnn, logPowThetaErrorIntegrand,
      abs_mul]
    calc |derivLogPowDivId m t * t| * |thetaError t|
        ≤ (((m : ℝ) * (Real.log t) ^ (m - 1) + (Real.log t) ^ m) / t)
            * (|C| * Real.exp (-c * Real.sqrt (Real.log t))) :=
          mul_le_mul hfac herr (abs_nonneg _) (by positivity)
      _ = g t := by
          rw [hg]
          field_simp

/-! ## The higher-order Mertens theorem -/

theorem integral_derivLogPowDivId_mul_theta_eq (m : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    (∫ t in Ioc (2 : ℝ) x, derivLogPowDivId m t * Chebyshev.theta t)
      = (logPowIdPrimitive m x - logPowIdPrimitive m 2)
        + ∫ t in Ioc (2 : ℝ) x, logPowThetaErrorIntegrand m t := by
  have hpt : ∀ t ∈ Ioc (2 : ℝ) x, derivLogPowDivId m t * Chebyshev.theta t
      = (t * derivLogPowDivId m t) + logPowThetaErrorIntegrand m t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := by have := ht.1; linarith
    rw [theta_eq_mul_thetaError ht0, logPowThetaErrorIntegrand]
    ring
  have hI1 : IntegrableOn (fun t : ℝ => t * derivLogPowDivId m t) (Ioc (2 : ℝ) x) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    exact continuousOn_id.mul (continuousOn_derivLogPowDivId m)
  have hI2 : IntegrableOn (logPowThetaErrorIntegrand m) (Ioc (2 : ℝ) x) :=
    (integrableOn_logPowThetaErrorIntegrand_Icc m x).mono_set Ioc_subset_Icc_self
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_add hI1 hI2]
  congr 1
  have hftc : (∫ t in (2 : ℝ)..x, t * derivLogPowDivId m t)
      = logPowIdPrimitive m x - logPowIdPrimitive m 2 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_) ?_
    · rw [uIcc_of_le hx] at ht
      exact hasDerivAt_logPowIdPrimitive m (by have := ht.1; linarith)
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
      exact hI1
  rw [← hftc, intervalIntegral.integral_of_le hx]

theorem primeLogPowSumIoc_sub_eq (m : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    primeLogPowSumIoc (m + 1) x - (Real.log x) ^ (m + 1) / ((m : ℝ) + 1)
      = logPowDivId m x * (Chebyshev.theta x - x)
        - logPowDivId m 2 * Chebyshev.theta 2 + logPowIdPrimitive m 2
        - ∫ t in Ioc (2 : ℝ) x, logPowThetaErrorIntegrand m t := by
  have hx0 : (0 : ℝ) < x := by linarith
  rw [primeLogPowSumIoc_eq m hx, integral_derivLogPowDivId_mul_theta_eq m hx]
  have hfx : logPowDivId m x * x = (Real.log x) ^ m := by
    rw [logPowDivId]
    field_simp
  have hsplit : logPowDivId m x * Chebyshev.theta x
      = logPowDivId m x * (Chebyshev.theta x - x) + (Real.log x) ^ m := by
    rw [← hfx]
    ring
  rw [hsplit, logPowIdPrimitive]
  ring

/-- The higher-order Mertens constant `C_{m+1}` of `∑_{2 < p ≤ x} (log p)^{m+1}/p`. -/
def mertensLogPowConstant (m : ℕ) : ℝ :=
  logPowIdPrimitive m 2 - logPowDivId m 2 * Chebyshev.theta 2
    - ∫ t in Ioi (2 : ℝ), logPowThetaErrorIntegrand m t

theorem tendsto_logPowDivId_mul_thetaSub (m : ℕ) :
    Tendsto (fun x : ℝ => logPowDivId m x * (Chebyshev.theta x - x)) atTop (𝓝 0) := by
  obtain ⟨c, hc0, hO⟩ := Sieve.chebyshevTheta_sub_id_isBigO
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hO
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (hC.and (Filter.eventually_ge_atTop (2 : ℝ)))
  set K : ℝ := (((2 * (m + 1)).factorial : ℕ) : ℝ) / c ^ (2 * (m + 1)) with hK
  refine squeeze_zero_norm' (a := fun x : ℝ => |C| * (K / Real.log x)) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop T, Filter.eventually_ge_atTop (2 : ℝ)]
      with x hxT hx2
    have hxpos : (0 : ℝ) < x := by linarith
    have hlog : 0 < Real.log x := Real.log_pos (by linarith)
    have hbound := (hT x hxT).1
    have h2 : ‖x * Real.exp (-c * Real.sqrt (Real.log x))‖
        = x * Real.exp (-c * Real.sqrt (Real.log x)) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h3 : ‖(Chebyshev.theta - id : ℝ → ℝ) x‖ = |Chebyshev.theta x - x| := by
      simp [Real.norm_eq_abs]
    rw [h2, h3] at hbound
    have hnum : |Chebyshev.theta x - x|
        ≤ |C| * (x * Real.exp (-c * Real.sqrt (Real.log x))) :=
      hbound.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    have hexp : Real.exp (-c * Real.sqrt (Real.log x)) ≤ K / (Real.log x) ^ (m + 1) := by
      have h := exp_neg_sqrt_le_pow hc0 (m + 1) hlog
      rwa [hK, div_div]
    rw [Real.norm_eq_abs, logPowDivId, abs_mul, abs_div,
      abs_of_nonneg (pow_nonneg hlog.le m), abs_of_pos hxpos]
    have hstep : (Real.log x) ^ m / x * |Chebyshev.theta x - x|
        ≤ (Real.log x) ^ m / x * (|C| * (x * Real.exp (-c * Real.sqrt (Real.log x)))) := by
      gcongr
    refine hstep.trans ?_
    have hrw : (Real.log x) ^ m / x * (|C| * (x * Real.exp (-c * Real.sqrt (Real.log x))))
        = |C| * ((Real.log x) ^ m * Real.exp (-c * Real.sqrt (Real.log x))) := by
      field_simp
    rw [hrw]
    have hfin : (Real.log x) ^ m * Real.exp (-c * Real.sqrt (Real.log x)) ≤ K / Real.log x := by
      have hstep2 : (Real.log x) ^ m * Real.exp (-c * Real.sqrt (Real.log x))
          ≤ (Real.log x) ^ m * (K / (Real.log x) ^ (m + 1)) := by
        gcongr
      refine hstep2.trans_eq ?_
      field_simp
      ring
    exact mul_le_mul_of_nonneg_left hfin (abs_nonneg C)
  · have hlogTop : Tendsto (fun x : ℝ => Real.log x) atTop atTop := Real.tendsto_log_atTop
    have hdiv : Tendsto (fun x : ℝ => K / Real.log x) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds hlogTop
    have := hdiv.const_mul |C|
    rwa [mul_zero] at this

/-- **The higher-order Mertens theorem.**  For every `k ≥ 1` the difference between the prime
logarithmic-power sum and its main term converges. -/
theorem tendsto_primeLogPowSumIoc_sub (m : ℕ) :
    Tendsto (fun x : ℝ => primeLogPowSumIoc (m + 1) x - (Real.log x) ^ (m + 1) / ((m : ℝ) + 1))
      atTop (𝓝 (mertensLogPowConstant m)) := by
  have htail : Tendsto (fun x : ℝ => ∫ t in Ioc (2 : ℝ) x, logPowThetaErrorIntegrand m t)
      atTop (𝓝 (∫ t in Ioi (2 : ℝ), logPowThetaErrorIntegrand m t)) := by
    have h := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (2 : ℝ)
      (integrableOn_logPowThetaErrorIntegrand m) (tendsto_id (α := ℝ) (x := atTop))
    refine h.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
    exact intervalIntegral.integral_of_le hx
  have hmain := ((tendsto_logPowDivId_mul_thetaSub m).sub_const
    (logPowDivId m 2 * Chebyshev.theta 2 - logPowIdPrimitive m 2)).sub htail
  have hval : (0 : ℝ) - (logPowDivId m 2 * Chebyshev.theta 2 - logPowIdPrimitive m 2)
      - ∫ t in Ioi (2 : ℝ), logPowThetaErrorIntegrand m t = mertensLogPowConstant m := by
    rw [mertensLogPowConstant]
    ring
  rw [hval] at hmain
  refine hmain.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
  rw [primeLogPowSumIoc_sub_eq m hx]
  ring

/-! ## The full prime sum and the boundary defect -/

theorem primeLogPowSum_eq_add (k : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    primeLogPowSum k x = primeLogPowSumIoc k x + (Real.log 2) ^ k / 2 := by
  have hfloor : 2 ≤ ⌊x⌋₊ := by
    have := Nat.le_floor (α := ℝ) (n := 2) (by exact_mod_cast hx)
    exact this
  have hunion : Finset.Icc 0 2 ∪ Finset.Ioc 2 ⌊x⌋₊ = Finset.Icc 0 ⌊x⌋₊ := by
    ext a
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 0 2) (Finset.Ioc 2 ⌊x⌋₊) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    have h1 : a ≤ 2 := (Finset.mem_Icc.mp ha).2
    have h2 : 2 < a := (Finset.mem_Ioc.mp ha').1
    omega
  rw [primeLogPowSum, ← hunion, Finset.sum_union hdisj, primeLogPowSumIoc, add_comm]
  congr 1
  rw [show Finset.Icc 0 2 = {0, 1, 2} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [primeLogPowWeight, primeLogPowWeight, primeLogPowWeight,
    if_neg (by decide : ¬ Nat.Prime 0), if_neg (by decide : ¬ Nat.Prime 1),
    if_pos (by decide : Nat.Prime 2)]
  norm_num

/-- The higher-order Mertens constant of the complete prime sum. -/
def mertensLogPowConstantFull (m : ℕ) : ℝ :=
  mertensLogPowConstant m + (Real.log 2) ^ (m + 1) / 2

/-- **The higher-order Mertens theorem, complete sum.**  `∑_{p ≤ x} (log p)^{k}/p
- (log x)^{k}/k` converges for every `k ≥ 1`. -/
theorem tendsto_primeLogPowSum_sub (m : ℕ) :
    Tendsto (fun x : ℝ => primeLogPowSum (m + 1) x - (Real.log x) ^ (m + 1) / ((m : ℝ) + 1))
      atTop (𝓝 (mertensLogPowConstantFull m)) := by
  have h := (tendsto_primeLogPowSumIoc_sub m).add_const ((Real.log 2) ^ (m + 1) / 2)
  rw [← mertensLogPowConstantFull] at h
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
  rw [primeLogPowSum_eq_add (m + 1) hx]
  ring

/-- **The endpoint jet at a monomial test function.**  This is the card's `D_N(u^k)` identity:
the normalized prime-harmonic defect at `h(u) = u^k` is exactly `C_k / (log x)^k` up to `o(1)`. -/
theorem tendsto_logPow_mul_primeLevyDefect_pow (m : ℕ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ (m + 1) *
        ((∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
            (if n.Prime then ((Real.log n / Real.log x) ^ (m + 1)) / n else 0))
          - 1 / ((m : ℝ) + 1)))
      atTop (𝓝 (mertensLogPowConstantFull m)) := by
  refine (tendsto_primeLogPowSum_sub m).congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (2 : ℝ)] with x hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogpow : ((Real.log x) ^ (m + 1)) ≠ 0 := by positivity
  have key : ∀ n ∈ Finset.Icc 0 ⌊x⌋₊,
      (Real.log x) ^ (m + 1) *
          (if n.Prime then ((Real.log n / Real.log x) ^ (m + 1)) / n else 0)
        = primeLogPowWeight (m + 1) n := by
    intro n _
    rw [primeLogPowWeight]
    by_cases hp : n.Prime
    · rw [if_pos hp, if_pos hp, div_pow]
      field_simp
    · rw [if_neg hp, if_neg hp, mul_zero]
  symm
  rw [mul_sub, Finset.mul_sum, primeLogPowSum, Finset.sum_congr rfl key]
  congr 1
  field_simp

end

end RHTower
