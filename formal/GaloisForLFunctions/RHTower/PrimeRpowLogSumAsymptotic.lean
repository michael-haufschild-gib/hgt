import GaloisForLFunctions.RHTower.PrimeRpowAbelSummation
import GaloisForLFunctions.RHTower.Sieve.ChebyshevThetaBigO
import GaloisForLFunctions.HTGeometry.RpowKernelRemainder

/-!
# The prime power–logarithm sum

For every positive exponent `a`,

```text
∑_{2 < p ≤ x} p^(a-1) log p = (x^a/a)(1 + o(1)).
```

Abel summation against the Chebyshev function turns the sum into the boundary term
`x^(a-1) θ(x)`, the elementary power integral `(a-1)(x^a - 2^a)/a`, and a remainder weighted by
the relative error `θ(t)/t - 1`, which the prime number theorem sends to zero.  Since
`1 - (a-1)/a = 1/a`, the normalized limit is `1/a`.
-/

open Filter Topology Set MeasureTheory intervalIntegral Asymptotics

namespace RHTower

noncomputable section

/-! ## The relative error of the Chebyshev function -/

/-- Relative error in the prime number theorem for `θ`. -/
def thetaError (t : ℝ) : ℝ := Chebyshev.theta t / t - 1

theorem theta_eq_mul_thetaError {t : ℝ} (ht : 0 < t) :
    Chebyshev.theta t = t * (1 + thetaError t) := by
  rw [thetaError]
  field_simp
  ring

/-- The prime number theorem in relative form. -/
theorem tendsto_thetaError : Tendsto thetaError atTop (nhds 0) := by
  obtain ⟨c, hc0, hO⟩ := Sieve.chebyshevTheta_sub_id_isBigO
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hO
  have hsqrt : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop := by
    refine Filter.tendsto_atTop_atTop.2 fun b => ⟨Real.exp (b ^ 2), fun x hx => ?_⟩
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hx
    have hlog : b ^ 2 ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos (b ^ 2)) hx
      rwa [Real.log_exp] at h
    calc b ≤ Real.sqrt (b ^ 2) := by
          rw [Real.sqrt_sq_eq_abs]
          exact le_abs_self b
      _ ≤ Real.sqrt (Real.log x) := Real.sqrt_le_sqrt hlog
  have hexpTop : Tendsto (fun x : ℝ => Real.exp (c * Real.sqrt (Real.log x))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (hsqrt.const_mul_atTop hc0)
  have hexp : Tendsto (fun x : ℝ => C * Real.exp (-c * Real.sqrt (Real.log x))) atTop (nhds 0) := by
    have hinv : Tendsto (fun x : ℝ => (Real.exp (c * Real.sqrt (Real.log x)))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hexpTop
    have h := hinv.const_mul C
    rw [mul_zero] at h
    refine h.congr fun x => ?_
    rw [← Real.exp_neg]
    congr 2
    ring
  refine squeeze_zero_norm' ?_ hexp
  filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hgnorm : ‖x * Real.exp (-c * Real.sqrt (Real.log x))‖
      = x * Real.exp (-c * Real.sqrt (Real.log x)) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [Pi.sub_apply, Real.norm_eq_abs, hgnorm, id_eq] at hx
  have habs : ‖thetaError x‖ = |Chebyshev.theta x - x| / x := by
    rw [Real.norm_eq_abs, thetaError, div_sub_one (ne_of_gt hx0), abs_div, abs_of_pos hx0]
  rw [habs, div_le_iff₀ hx0]
  calc |Chebyshev.theta x - x| ≤ C * (x * Real.exp (-c * Real.sqrt (Real.log x))) := hx
    _ = C * Real.exp (-c * Real.sqrt (Real.log x)) * x := by ring

theorem abs_thetaError_le {t : ℝ} (ht : 2 ≤ t) : |thetaError t| ≤ Real.log 4 + 1 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hupper : Chebyshev.theta t / t ≤ Real.log 4 := by
    rw [div_le_iff₀ ht0]
    exact Chebyshev.theta_le_log4_mul_x ht0.le
  have hlower : (0 : ℝ) ≤ Chebyshev.theta t / t := by
    apply div_nonneg (Chebyshev.theta_nonneg t) ht0.le
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [thetaError, abs_le]
  constructor <;> linarith

theorem measurable_thetaError : Measurable thetaError :=
  (Chebyshev.theta_mono.measurable.div measurable_id).sub measurable_const

theorem integrableOn_thetaError (x : ℝ) : IntegrableOn thetaError (Icc 2 x) := by
  refine MeasureTheory.Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
    measurable_thetaError.aestronglyMeasurable (M := Real.log 4 + 1) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs]
  exact abs_thetaError_le ht.1

theorem intervalIntegrable_thetaError_mul {a x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => thetaError t * t ^ (a - 1)) volume 2 x := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
  refine ((integrableOn_thetaError x).mul_continuousOn ?_ isCompact_Icc).mono_set
    Ioc_subset_Icc_self
  intro t ht
  have ht0 : t ≠ 0 := by
    have := ht.1
    intro h
    rw [h] at this
    linarith
  exact (Real.continuousAt_rpow_const t (a - 1) (Or.inl ht0)).continuousWithinAt

/-! ## Abel summation of the prime power–logarithm sum -/

/-- The prime power–logarithm sum over the window `(2, x]`. -/
def primeRpowLogSumIoc (a x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc 2 ⌊x⌋₊, (if k.Prime then ((k : ℕ) : ℝ) ^ (a - 1) * Real.log k else 0)

theorem rpowSubOne_mul_primeLogWeight {a : ℝ} (k : ℕ) :
    ((k : ℝ)) ^ (a - 1) * primeLogWeight k =
      (if k.Prime then ((k : ℕ) : ℝ) ^ (a - 1) * Real.log k else 0) := by
  rw [primeLogWeight]
  by_cases hp : k.Prime
  · rw [if_pos hp, if_pos hp]
  · rw [if_neg hp, if_neg hp, mul_zero]

theorem hasDerivAt_rpowSubOne {a t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => s ^ (a - 1)) ((a - 1) * t ^ (a - 2)) t := by
  have h := Real.hasDerivAt_rpow_const (x := t) (p := a - 1) (Or.inl ht)
  rwa [show a - 1 - 1 = a - 2 by ring] at h

theorem integrableOn_deriv_rpowSubOne {a x : ℝ} (_hx : 2 ≤ x) :
    IntegrableOn (deriv fun s : ℝ => s ^ (a - 1)) (Icc 2 x) := by
  have hcont : ContinuousOn (fun t : ℝ => (a - 1) * t ^ (a - 2)) (Icc 2 x) := by
    intro t ht
    have ht0 : t ≠ 0 := by
      have := ht.1
      intro h
      rw [h] at this
      linarith
    exact (continuousAt_const.mul
      (Real.continuousAt_rpow_const t (a - 2) (Or.inl ht0))).continuousWithinAt
  refine hcont.integrableOn_Icc.congr_fun (fun t ht => ?_) measurableSet_Icc
  have ht0 : t ≠ 0 := by
    have := ht.1
    intro h
    rw [h] at this
    linarith
  exact ((hasDerivAt_rpowSubOne (a := a) ht0).deriv).symm

/-- **Abel summation of the prime power–logarithm sum against the Chebyshev function.** -/
theorem primeRpowLogSumIoc_eq {a x : ℝ} (hx : 2 ≤ x) :
    primeRpowLogSumIoc a x =
      x ^ (a - 1) * Chebyshev.theta x - (2 : ℝ) ^ (a - 1) * Chebyshev.theta 2 -
        ∫ t in (2 : ℝ)..x, ((a - 1) * t ^ (a - 2)) * Chebyshev.theta t := by
  have habel := sum_mul_eq_sub_sub_integral_mul (𝕜 := ℝ) primeLogWeight
    (f := fun s : ℝ => s ^ (a - 1)) (a := (2 : ℝ)) (b := x) (by norm_num) hx
    (fun t ht => (hasDerivAt_rpowSubOne (a := a) (by
      have := ht.1
      intro h
      rw [h] at this
      linarith)).differentiableAt)
    (integrableOn_deriv_rpowSubOne hx)
  simp only [sum_primeLogWeight_eq_theta] at habel
  rw [show (⌊(2 : ℝ)⌋₊) = 2 from by norm_num] at habel
  have hint : (∫ t in Ioc (2 : ℝ) x, deriv (fun s : ℝ => s ^ (a - 1)) t * Chebyshev.theta t)
      = ∫ t in (2 : ℝ)..x, ((a - 1) * t ^ (a - 2)) * Chebyshev.theta t := by
    rw [intervalIntegral.integral_of_le hx]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    have ht0 : t ≠ 0 := by
      have := ht.1
      intro h
      rw [h] at this
      linarith
    rw [(hasDerivAt_rpowSubOne (a := a) ht0).deriv]
  rw [primeRpowLogSumIoc, ← hint, ← habel]
  exact Finset.sum_congr rfl fun k _ => (rpowSubOne_mul_primeLogWeight k).symm

/-- The Abel integral splits into the elementary power integral and the error remainder. -/
theorem integral_derivRpow_mul_theta_eq {a x : ℝ} (ha0 : 0 < a) (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, ((a - 1) * t ^ (a - 2)) * Chebyshev.theta t)
      = (a - 1) * ((x ^ a - (2 : ℝ) ^ a) / a)
        + (a - 1) * ∫ t in (2 : ℝ)..x, thetaError t * t ^ (a - 1) := by
  have hpt : ∀ t ∈ uIcc (2 : ℝ) x, ((a - 1) * t ^ (a - 2)) * Chebyshev.theta t
      = (a - 1) * t ^ (a - 1) + (a - 1) * (thetaError t * t ^ (a - 1)) := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    have ht0 : (0 : ℝ) < t := by
      have := ht.1
      linarith
    have hrp : t ^ (a - 2) * t = t ^ (a - 1) := by
      nth_rewrite 2 [← Real.rpow_one t]
      rw [← Real.rpow_add ht0, show a - 2 + 1 = a - 1 by ring]
    rw [theta_eq_mul_thetaError ht0]
    calc ((a - 1) * t ^ (a - 2)) * (t * (1 + thetaError t))
        = (a - 1) * (t ^ (a - 2) * t) * (1 + thetaError t) := by ring
      _ = (a - 1) * t ^ (a - 1) * (1 + thetaError t) := by rw [hrp]
      _ = (a - 1) * t ^ (a - 1) + (a - 1) * (thetaError t * t ^ (a - 1)) := by ring
  have hI1 : IntervalIntegrable (fun t : ℝ => (a - 1) * t ^ (a - 1)) volume 2 x :=
    (HTGeometry.intervalIntegrable_rpowSubOne a le_rfl hx).const_mul _
  have hI2 : IntervalIntegrable
      (fun t : ℝ => (a - 1) * (thetaError t * t ^ (a - 1))) volume 2 x :=
    (intervalIntegrable_thetaError_mul hx).const_mul _
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add hI1 hI2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    HTGeometry.integral_rpow_sub_one ha0]

/-- **The prime power–logarithm sum is asymptotic to `x^a/a`.** -/
theorem tendsto_primeRpowLogSumIoc {a : ℝ} (ha0 : 0 < a) :
    Tendsto (fun x : ℝ => primeRpowLogSumIoc a x / x ^ a) atTop (nhds (1 / a)) := by
  have hane : a ≠ 0 := ne_of_gt ha0
  have hT1 : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (nhds 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1)).add
      tendsto_thetaError
    rw [add_zero] at h
    refine h.congr fun x => ?_
    rw [thetaError]
    ring
  have hT2 : Tendsto
      (fun x : ℝ => ((2 : ℝ) ^ (a - 1) * Chebyshev.theta 2) / x ^ a) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop ha0)
  have hpow : Tendsto (fun x : ℝ => (2 : ℝ) ^ a / x ^ a) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop ha0)
  have hT3 : Tendsto (fun x : ℝ => (a - 1) / a * (1 - (2 : ℝ) ^ a / x ^ a)) atTop
      (nhds ((a - 1) / a)) := by
    have h := ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1)).sub
      hpow).const_mul ((a - 1) / a)
    rw [sub_zero, mul_one] at h
    exact h
  have hrem : Tendsto
      (fun x : ℝ => (∫ t in (2 : ℝ)..x, thetaError t * t ^ (a - 1)) / x ^ a) atTop (nhds 0) := by
    refine HTGeometry.tendsto_rpowKernelRemainder ha0 zero_le_one tendsto_thetaError
      (fun t ht => ?_) (fun x hx => intervalIntegrable_thetaError_mul hx)
    have ht0 : (0 : ℝ) < t := by linarith
    rw [one_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
  have hT4 : Tendsto
      (fun x : ℝ => (a - 1) * ((∫ t in (2 : ℝ)..x, thetaError t * t ^ (a - 1)) / x ^ a)) atTop
      (nhds 0) := by
    have h := hrem.const_mul (a - 1)
    rwa [mul_zero] at h
  have hsum := ((hT1.sub hT2).sub hT3).sub hT4
  rw [show (1 : ℝ) - 0 - (a - 1) / a - 0 = 1 / a by field_simp; ring] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hXpos : (0 : ℝ) < x ^ a := Real.rpow_pos_of_pos hx0 a
  have hXne : x ^ a ≠ 0 := ne_of_gt hXpos
  rw [primeRpowLogSumIoc_eq hx, integral_derivRpow_mul_theta_eq ha0 hx, Real.rpow_sub hx0,
    Real.rpow_one]
  field_simp
  ring

end

end RHTower
