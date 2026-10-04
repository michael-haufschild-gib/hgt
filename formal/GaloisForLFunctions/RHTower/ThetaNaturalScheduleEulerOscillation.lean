import GaloisForLFunctions.RHTower.ThetaPrimeScheduleSpectralObservation
import GaloisForLFunctions.RHTower.PrimeRpowLogSumAsymptotic

/-!
# The natural prime schedule: prime sums and the oscillating Euler envelope

For `s = σ + iτ` with `0 < σ < 1`, Abel summation against `θ(x) = x(1 + o(1))` gives

```text
Σ_{p ≤ N} p^{−s} = N^{1−s}/((1−s) log N) + o(N^{1−σ}/log N).          (3i)
```

For `1/2 < σ < 1` the quadratic Euler-log errors are summable, so

```text
log |E_{S_N^nat}(s)| = −Re[N^{1−s}/((1−s) log N)] + o(N^{1−σ}/log N).   (3j)
```

When `τ ≠ 0` the leading term rotates with `τ log N`; along integer subsequences near the
alternating phase peaks `|E_{S_N^nat}(s)|` tends to `0` and to `∞` faster than every power of
`N`.  On the first the raw spectral observation of the cutoff commutator tends to `0`; on the
second it is `−G(s−1)E_{S_N^nat}(s)(1+o(1))` and its modulus diverges.
-/

open MeasureTheory Set Filter Topology Asymptotics intervalIntegral

namespace RHTower

noncomputable section

/-! ## The complex Abel weight -/

/-- The complex Abel weight `t^{−s}/log t`. -/
def primeCpowAbelWeight (s : ℂ) (t : ℝ) : ℂ := (t : ℂ) ^ (-s) / (Real.log t : ℂ)

/-- The derivative of the complex Abel weight. -/
def primeCpowAbelWeightDeriv (s : ℂ) (t : ℝ) : ℂ :=
  ((-s) * (t : ℂ) ^ (-s - 1) * (Real.log t : ℂ) - (t : ℂ) ^ (-s) * ((t⁻¹ : ℝ) : ℂ)) /
    (Real.log t : ℂ) ^ 2

/-- The Abel kernel `t · f'(t) = −s t^{−s}/log t − t^{−s}/log² t`. -/
def primeCpowAbelKernel (s : ℂ) (t : ℝ) : ℂ :=
  -s * ((t : ℂ) ^ (-s) / (Real.log t : ℂ)) - (t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 2

/-- The primitive `t^{1−s}/log t`. -/
def primeCpowAbelPrimitive (s : ℂ) (t : ℝ) : ℂ := (t : ℂ) ^ (1 - s) / (Real.log t : ℂ)

theorem ofReal_log_ne_zero_of_one_lt {t : ℝ} (ht : 1 < t) : (Real.log t : ℂ) ≠ 0 := by
  exact_mod_cast (Real.log_pos ht).ne'

theorem hasDerivAt_primeCpowAbelWeight {s : ℂ} (hs : s ≠ 0) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (primeCpowAbelWeight s) (primeCpowAbelWeightDeriv s t) t := by
  have ht0 : t ≠ 0 := by positivity
  have h1 := hasDerivAt_ofReal_cpow_const ht0 (neg_ne_zero.2 hs)
  have h2 : HasDerivAt (fun y : ℝ => (Real.log y : ℂ)) ((t⁻¹ : ℝ) : ℂ) t :=
    (Real.hasDerivAt_log ht0).ofReal_comp
  exact h1.div h2 (ofReal_log_ne_zero_of_one_lt ht)

theorem mul_primeCpowAbelWeightDeriv (s : ℂ) {t : ℝ} (ht : 1 < t) :
    (t : ℂ) * primeCpowAbelWeightDeriv s t = primeCpowAbelKernel s t := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by positivity)
  have hlog := ofReal_log_ne_zero_of_one_lt ht
  rw [primeCpowAbelWeightDeriv, primeCpowAbelKernel, Complex.cpow_sub _ _ ht0, Complex.cpow_one,
    Complex.ofReal_inv]
  field_simp

theorem hasDerivAt_primeCpowAbelPrimitive {s : ℂ} (hs : s ≠ 1) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (primeCpowAbelPrimitive s)
      ((1 - s) * ((t : ℂ) ^ (-s) / (Real.log t : ℂ)) - (t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 2) t := by
  have ht0 : t ≠ 0 := by positivity
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  have h1 := hasDerivAt_ofReal_cpow_const ht0 (sub_ne_zero.2 (Ne.symm hs))
  have h2 : HasDerivAt (fun y : ℝ => (Real.log y : ℂ)) ((t⁻¹ : ℝ) : ℂ) t :=
    (Real.hasDerivAt_log ht0).ofReal_comp
  have hlog := ofReal_log_ne_zero_of_one_lt ht
  refine (h1.div h2 hlog).congr_deriv ?_
  rw [show (1 : ℂ) - s - 1 = -s by ring, show (1 : ℂ) - s = -s + 1 by ring,
    Complex.cpow_add _ _ htc, Complex.cpow_one, Complex.ofReal_inv]
  field_simp

/-- The kernel is a combination of the primitive's derivative and the doubly logarithmic term. -/
theorem primeCpowAbelKernel_eq {s : ℂ} (hs : s ≠ 1) (t : ℝ) :
    primeCpowAbelKernel s t =
      -(s / (1 - s)) * ((1 - s) * ((t : ℂ) ^ (-s) / (Real.log t : ℂ)) -
        (t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 2) -
        1 / (1 - s) * ((t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 2) := by
  have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.2 (Ne.symm hs)
  rw [primeCpowAbelKernel]
  field_simp
  ring

theorem continuousOn_ofReal_cpow_Icc (w : ℂ) {x : ℝ} :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ w) (Icc 2 x) := fun t ht =>
  (Complex.continuousAt_ofReal_cpow_const t w (Or.inr (by linarith [ht.1]))).continuousWithinAt

theorem continuousOn_ofReal_log_Icc {x : ℝ} :
    ContinuousOn (fun t : ℝ => (Real.log t : ℂ)) (Icc 2 x) := fun t ht =>
  (Complex.continuous_ofReal.continuousAt.comp
    (Real.continuousAt_log (by linarith [ht.1]))).continuousWithinAt

theorem log_ne_zero_of_mem_Icc {x t : ℝ} (ht : t ∈ Icc 2 x) : (Real.log t : ℂ) ≠ 0 :=
  ofReal_log_ne_zero_of_one_lt (by linarith [ht.1])

theorem continuousOn_cpow_div_log {w : ℂ} {x : ℝ} :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ w / (Real.log t : ℂ)) (Icc 2 x) :=
  (continuousOn_ofReal_cpow_Icc w).div continuousOn_ofReal_log_Icc fun _ ht =>
    log_ne_zero_of_mem_Icc ht

theorem continuousOn_cpow_div_log_sq {w : ℂ} {x : ℝ} :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ w / (Real.log t : ℂ) ^ 2) (Icc 2 x) :=
  (continuousOn_ofReal_cpow_Icc w).div (continuousOn_ofReal_log_Icc.pow 2) fun _ ht =>
    pow_ne_zero 2 (log_ne_zero_of_mem_Icc ht)

theorem continuousOn_primeCpowAbelKernel (s : ℂ) {x : ℝ} :
    ContinuousOn (primeCpowAbelKernel s) (Icc 2 x) :=
  (continuousOn_const.mul continuousOn_cpow_div_log).sub continuousOn_cpow_div_log_sq

theorem continuousOn_primeCpowAbelWeightDeriv (s : ℂ) {x : ℝ} :
    ContinuousOn (primeCpowAbelWeightDeriv s) (Icc 2 x) := by
  refine ((((continuousOn_const.mul (continuousOn_ofReal_cpow_Icc _)).mul
    continuousOn_ofReal_log_Icc).sub ((continuousOn_ofReal_cpow_Icc _).mul ?_)).div
      (continuousOn_ofReal_log_Icc.pow 2)) fun _ ht => pow_ne_zero 2 (log_ne_zero_of_mem_Icc ht)
  exact fun t ht => (Complex.continuous_ofReal.continuousAt.comp
    (continuousAt_inv₀ (by linarith [ht.1] : t ≠ 0))).continuousWithinAt

/-- `‖t^{−s}/log t‖ = t^{−σ}/log t`. -/
theorem norm_cpow_div_log {s : ℂ} {t : ℝ} (ht : 1 < t) :
    ‖(t : ℂ) ^ (-s) / (Real.log t : ℂ)‖ = t ^ (-s.re) / Real.log t := by
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.norm_real,
    Real.norm_of_nonneg (Real.log_pos ht).le, Complex.neg_re]

theorem norm_cpow_div_log_sq {s : ℂ} {t : ℝ} (ht : 1 < t) :
    ‖(t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 2‖ = t ^ (-s.re) / Real.log t ^ 2 := by
  rw [norm_div, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.norm_real,
    Real.norm_of_nonneg (Real.log_pos ht).le, Complex.neg_re]

/-- The Abel kernel is dominated by `(|s| + 1/log 2) t^{−σ}/log t`. -/
theorem norm_primeCpowAbelKernel_le (s : ℂ) {t : ℝ} (ht : 2 ≤ t) :
    ‖primeCpowAbelKernel s t‖ ≤ (‖s‖ + 1 / Real.log 2) * (t ^ (-s.re) / Real.log t) := by
  have ht1 : 1 < t := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hlpos : 0 < Real.log t := Real.log_pos ht1
  have hP : 0 ≤ t ^ (-s.re) / Real.log t := by positivity
  have hQ : t ^ (-s.re) / Real.log t ^ 2 ≤ 1 / Real.log 2 * (t ^ (-s.re) / Real.log t) := by
    rw [pow_two, ← div_div, one_div, inv_mul_eq_div]
    exact div_le_div_of_nonneg_left hP hlog2 hlogt
  calc ‖primeCpowAbelKernel s t‖
      ≤ ‖-s * ((t : ℂ) ^ (-s) / (Real.log t : ℂ))‖ + ‖(t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 2‖ :=
        norm_sub_le _ _
    _ = ‖s‖ * (t ^ (-s.re) / Real.log t) + t ^ (-s.re) / Real.log t ^ 2 := by
        rw [norm_mul, norm_neg, norm_cpow_div_log ht1, norm_cpow_div_log_sq ht1]
    _ ≤ _ := by rw [add_mul]; linarith

/-! ## Abel summation against the Chebyshev function -/

/-- The prime sum `Σ_{2 < p ≤ x} p^{−s}`. -/
def primeCpowSumIoc (s : ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.Ioc 2 ⌊x⌋₊, (if k.Prime then (k : ℂ) ^ (-s) else 0)

theorem primeCpowAbelWeight_mul_primeLogWeight (s : ℂ) {k : ℕ} (hk : 2 < k) :
    primeCpowAbelWeight s (k : ℝ) * (primeLogWeight_primeRpowAbelSummation k : ℂ) =
      (if k.Prime then (k : ℂ) ^ (-s) else 0) := by
  rw [primeCpowAbelWeight, primeLogWeight_primeRpowAbelSummation]
  by_cases hp : k.Prime
  · have hk1 : (1 : ℝ) < k := by exact_mod_cast hk.trans_le' (by norm_num)
    rw [if_pos hp, if_pos hp, Complex.ofReal_natCast,
      div_mul_cancel₀ _ (ofReal_log_ne_zero_of_one_lt hk1)]
  · rw [if_neg hp, if_neg hp, Complex.ofReal_zero, mul_zero]

theorem sum_primeLogWeight_eq_theta_complex (t : ℝ) :
    ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (primeLogWeight_primeRpowAbelSummation k : ℂ) =
      (Chebyshev.theta t : ℂ) := by
  rw [← sum_primeLogWeight_eq_theta, Complex.ofReal_sum]

/-- **Complex Abel summation of `p^{−s}` against `θ`.** -/
theorem primeCpowSumIoc_eq {s : ℂ} (hs : s ≠ 0) {x : ℝ} (hx : 2 ≤ x) :
    primeCpowSumIoc s x =
      primeCpowAbelWeight s x * (Chebyshev.theta x : ℂ) -
        primeCpowAbelWeight s 2 * (Chebyshev.theta 2 : ℂ) -
          ∫ t in Ioc (2 : ℝ) x, primeCpowAbelWeightDeriv s t * (Chebyshev.theta t : ℂ) := by
  have hderiv : ∀ t ∈ Icc (2 : ℝ) x, deriv (primeCpowAbelWeight s) t = primeCpowAbelWeightDeriv s t :=
    fun t ht => (hasDerivAt_primeCpowAbelWeight hs (by linarith [ht.1])).deriv
  have hint : IntegrableOn (deriv (primeCpowAbelWeight s)) (Icc 2 x) :=
    ((continuousOn_primeCpowAbelWeightDeriv s).congr hderiv).integrableOn_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul (𝕜 := ℂ)
    (fun k => (primeLogWeight_primeRpowAbelSummation k : ℂ)) (f := primeCpowAbelWeight s)
    (a := (2 : ℝ)) (b := x) (by norm_num) hx
    (fun t ht => (hasDerivAt_primeCpowAbelWeight hs (by linarith [ht.1])).differentiableAt) hint
  simp only [sum_primeLogWeight_eq_theta_complex] at habel
  rw [show (⌊(2 : ℝ)⌋₊) = 2 from by norm_num] at habel
  rw [primeCpowSumIoc, Finset.sum_congr rfl fun k hk =>
    (primeCpowAbelWeight_mul_primeLogWeight s (Finset.mem_Ioc.mp hk).1).symm, habel]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  rw [hderiv t (Ioc_subset_Icc_self ht)]

/-! ## The exact remainder of the prime sum -/

/-- `J(x) = ∫_2^x t^{−s}/log² t`. -/
def primeCpowLogSqIntegral (s : ℂ) (x : ℝ) : ℂ :=
  ∫ t in (2 : ℝ)..x, (t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 2

theorem integral_primeCpowAbelKernel {s : ℂ} (hs : s ≠ 1) {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in (2 : ℝ)..x, primeCpowAbelKernel s t =
      -(s / (1 - s)) * (primeCpowAbelPrimitive s x - primeCpowAbelPrimitive s 2) -
        1 / (1 - s) * primeCpowLogSqIntegral s x := by
  have hI1 : IntervalIntegrable (fun t : ℝ => (1 - s) * ((t : ℂ) ^ (-s) / (Real.log t : ℂ)) -
      (t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 2) volume 2 x :=
    ((continuousOn_const.mul continuousOn_cpow_div_log).sub
      continuousOn_cpow_div_log_sq).intervalIntegrable_of_Icc hx
  have hI2 : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 2) volume 2 x :=
    continuousOn_cpow_div_log_sq.intervalIntegrable_of_Icc hx
  have hFTC : ∫ t in (2 : ℝ)..x, ((1 - s) * ((t : ℂ) ^ (-s) / (Real.log t : ℂ)) -
      (t : ℂ) ^ (-s) / (Real.log t : ℂ) ^ 2) =
        primeCpowAbelPrimitive s x - primeCpowAbelPrimitive s 2 :=
    integral_eq_sub_of_hasDerivAt (fun t ht => hasDerivAt_primeCpowAbelPrimitive hs (by
      rw [uIcc_of_le hx] at ht; linarith [ht.1])) hI1
  simp_rw [primeCpowAbelKernel_eq hs]
  rw [integral_sub (hI1.const_mul _) (hI2.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hFTC]
  rfl

theorem integrableOn_thetaError_mul_primeCpowAbelKernel (s : ℂ) (x : ℝ) :
    IntegrableOn (fun t : ℝ => (thetaError t : ℂ) * primeCpowAbelKernel s t) (Icc 2 x) :=
  (show IntegrableOn (fun t : ℝ => (thetaError t : ℂ)) (Icc 2 x) volume from
    (integrableOn_thetaError x).ofReal).mul_continuousOn (continuousOn_primeCpowAbelKernel s)
    isCompact_Icc

theorem intervalIntegrable_thetaError_mul_primeCpowAbelKernel (s : ℂ) {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => (thetaError t : ℂ) * primeCpowAbelKernel s t) volume 2 x := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
  exact (integrableOn_thetaError_mul_primeCpowAbelKernel s x).mono_set Ioc_subset_Icc_self

/-- **Exact remainder of (3i).**  With `e = θ(t)/t − 1`, `P(t) = t^{1−s}/log t` and
`J(x) = ∫_2^x t^{−s}/log² t`,
`Σ_{2<p≤x} p^{−s} − x^{1−s}/((1−s)log x)
   = P(x)e(x) − f(2)θ(2) − (s/(1−s))P(2) + J(x)/(1−s) − ∫_2^x e(t) t f'(t) dt`. -/
theorem primeCpowSumIoc_sub_main {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) {x : ℝ} (hx : 2 ≤ x) :
    primeCpowSumIoc s x - (x : ℂ) ^ (1 - s) / ((1 - s) * (Real.log x : ℂ)) =
      primeCpowAbelPrimitive s x * (thetaError x : ℂ) -
        primeCpowAbelWeight s 2 * (Chebyshev.theta 2 : ℂ) -
        s / (1 - s) * primeCpowAbelPrimitive s 2 + 1 / (1 - s) * primeCpowLogSqIntegral s x -
        ∫ t in (2 : ℝ)..x, (thetaError t : ℂ) * primeCpowAbelKernel s t := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
  have hx0 : 0 < x := by linarith
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have hlogx := ofReal_log_ne_zero_of_one_lt (show 1 < x by linarith)
  have hKint : IntervalIntegrable (primeCpowAbelKernel s) volume 2 x :=
    (continuousOn_primeCpowAbelKernel s).intervalIntegrable_of_Icc hx
  have hsplit : ∫ t in Ioc (2 : ℝ) x, primeCpowAbelWeightDeriv s t * (Chebyshev.theta t : ℂ) =
      (∫ t in (2 : ℝ)..x, primeCpowAbelKernel s t) +
        ∫ t in (2 : ℝ)..x, (thetaError t : ℂ) * primeCpowAbelKernel s t := by
    rw [← integral_add hKint (intervalIntegrable_thetaError_mul_primeCpowAbelKernel s hx),
      integral_of_le hx]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht0 : 0 < t := by linarith [ht.1]
    rw [theta_eq_mul_thetaError ht0, ← mul_primeCpowAbelWeightDeriv s (by linarith [ht.1])]
    push_cast
    ring
  have hθx : (Chebyshev.theta x : ℂ) = (x : ℂ) * (1 + (thetaError x : ℂ)) := by
    rw [theta_eq_mul_thetaError hx0]; push_cast; ring
  have hfx : primeCpowAbelWeight s x * (x : ℂ) = primeCpowAbelPrimitive s x := by
    rw [primeCpowAbelWeight, primeCpowAbelPrimitive, show (1 : ℂ) - s = -s + 1 by ring,
      Complex.cpow_add _ _ hxc, Complex.cpow_one]
    ring
  rw [primeCpowSumIoc_eq hs0 hx, hsplit, integral_primeCpowAbelKernel hs1 hx, hθx]
  have hP : primeCpowAbelPrimitive s x = (x : ℂ) ^ (1 - s) / (Real.log x : ℂ) := rfl
  rw [← mul_assoc, hfx, hP]
  field_simp
  ring

/-- `‖t^{1−s}/log t‖ = t^{1−σ}/log t`. -/
theorem norm_primeCpowAbelPrimitive {s : ℂ} {t : ℝ} (ht : 1 < t) :
    ‖primeCpowAbelPrimitive s t‖ = t ^ (1 - s.re) / Real.log t := by
  rw [primeCpowAbelPrimitive, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith),
    Complex.norm_real, Real.norm_of_nonneg (Real.log_pos ht).le, Complex.sub_re, Complex.one_re]

theorem norm_primeCpowLogSqIntegral_le {s : ℂ} {x : ℝ} (hx : 2 ≤ x) :
    ‖primeCpowLogSqIntegral s x‖ ≤ HTGeometry.logSqRpowIntegral (1 - s.re) x := by
  rw [primeCpowLogSqIntegral, HTGeometry.logSqRpowIntegral]
  refine (intervalIntegral.norm_integral_le_integral_norm hx).trans_eq (integral_congr fun t ht => ?_)
  rw [uIcc_of_le hx] at ht
  rw [norm_cpow_div_log_sq (by linarith [ht.1]), show 1 - s.re - 1 = -s.re by ring]

theorem tendsto_log_div_rpow_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => Real.log x / x ^ a) atTop (𝓝 0) :=
  (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero

/-- **(3i) on the real line.**  For `0 < σ < 1`,
`Σ_{2<p≤x} p^{−s} = x^{1−s}/((1−s) log x) + o(x^{1−σ}/log x)`. -/
theorem tendsto_primeCpowSumIoc_sub_main {s : ℂ} (hσ0 : 0 < s.re) (hσ1 : s.re < 1) :
    Tendsto (fun x : ℝ => ‖primeCpowSumIoc s x - (x : ℂ) ^ (1 - s) / ((1 - s) * (Real.log x : ℂ))‖ *
      Real.log x / x ^ (1 - s.re)) atTop (𝓝 0) := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hσ0; simp at hσ0
  have hs1 : s ≠ 1 := fun h => by rw [h] at hσ1; simp at hσ1
  set a : ℝ := 1 - s.re with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set c₀ : ℝ := ‖primeCpowAbelWeight s 2 * (Chebyshev.theta 2 : ℂ) +
    s / (1 - s) * primeCpowAbelPrimitive s 2‖
  set C : ℝ := ‖s‖ + 1 / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 ≤ C := by positivity
  -- the four majorant pieces
  have h1 : Tendsto (fun x : ℝ => |thetaError x|) atTop (𝓝 0) := by
    simpa using tendsto_thetaError.abs
  have h2 : Tendsto (fun x : ℝ => c₀ * (Real.log x / x ^ a)) atTop (𝓝 0) := by
    simpa using (tendsto_log_div_rpow_atTop ha).const_mul c₀
  have h3 : Tendsto (fun x : ℝ => ‖1 / (1 - s)‖ *
      (HTGeometry.logSqRpowIntegral a x * Real.log x / x ^ a)) atTop (𝓝 0) := by
    simpa using (HTGeometry.tendsto_logSqRpowIntegral ha).const_mul ‖1 / (1 - s)‖
  have h4 : Tendsto (fun x : ℝ => a⁻¹ * ((∫ t in (2 : ℝ)..x,
      |thetaError t| * ‖primeCpowAbelKernel s t‖) * (a * Real.log x) / x ^ a)) atTop (𝓝 0) := by
    have := HTGeometry.tendsto_logKernelRemainder ha hC h1 (K := fun t => ‖primeCpowAbelKernel s t‖)
      (fun t ht => by
        rw [abs_of_nonneg (norm_nonneg _), show a - 1 = -s.re by rw [ha_def]; ring]
        exact norm_primeCpowAbelKernel_le s ht)
      (fun x hx => by
        simpa [norm_mul] using (intervalIntegrable_thetaError_mul_primeCpowAbelKernel s hx).norm)
    simpa using this.const_mul a⁻¹
  have hsum := ((h1.add h2).add h3).add h4
  simp only [add_zero] at hsum
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have := Real.log_nonneg (show (1 : ℝ) ≤ x by linarith)
    positivity
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hx1 : 1 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos (by linarith) a
  have hRem : ‖∫ t in (2 : ℝ)..x, (thetaError t : ℂ) * primeCpowAbelKernel s t‖ ≤
      ∫ t in (2 : ℝ)..x, |thetaError t| * ‖primeCpowAbelKernel s t‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm hx).trans_eq
      (integral_congr fun t _ => ?_)
    simp
  have hbound : ‖primeCpowSumIoc s x - (x : ℂ) ^ (1 - s) / ((1 - s) * (Real.log x : ℂ))‖ ≤
      x ^ a / Real.log x * |thetaError x| + c₀ + ‖1 / (1 - s)‖ * HTGeometry.logSqRpowIntegral a x +
        ∫ t in (2 : ℝ)..x, |thetaError t| * ‖primeCpowAbelKernel s t‖ := by
    rw [primeCpowSumIoc_sub_main hs0 hs1 hx]
    have e1 : ‖primeCpowAbelPrimitive s x * (thetaError x : ℂ)‖ = x ^ a / Real.log x * |thetaError x| := by
      rw [norm_mul, norm_primeCpowAbelPrimitive hx1, Complex.norm_real, Real.norm_eq_abs]
    have e3 : ‖1 / (1 - s) * primeCpowLogSqIntegral s x‖ ≤
        ‖1 / (1 - s)‖ * HTGeometry.logSqRpowIntegral a x := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_primeCpowLogSqIntegral_le hx) (norm_nonneg _)
    set A := primeCpowAbelPrimitive s x * (thetaError x : ℂ)
    set B := primeCpowAbelWeight s 2 * (Chebyshev.theta 2 : ℂ) +
      s / (1 - s) * primeCpowAbelPrimitive s 2
    set Cc := 1 / (1 - s) * primeCpowLogSqIntegral s x
    set D := ∫ t in (2 : ℝ)..x, (thetaError t : ℂ) * primeCpowAbelKernel s t
    have hre : A - primeCpowAbelWeight s 2 * (Chebyshev.theta 2 : ℂ) -
        s / (1 - s) * primeCpowAbelPrimitive s 2 + Cc - D = A - B + Cc - D := by
      simp only [B]; ring
    rw [hre]
    calc ‖A - B + Cc - D‖ ≤ ‖A - B + Cc‖ + ‖D‖ := norm_sub_le _ _
      _ ≤ ‖A - B‖ + ‖Cc‖ + ‖D‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖A‖ + ‖B‖ + ‖Cc‖ + ‖D‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ _ := by rw [e1]; gcongr
  have hmul := mul_le_mul_of_nonneg_right hbound (div_nonneg hlogx.le hxa.le)
  calc ‖primeCpowSumIoc s x - (x : ℂ) ^ (1 - s) / ((1 - s) * (Real.log x : ℂ))‖ * Real.log x / x ^ a
      = ‖primeCpowSumIoc s x - (x : ℂ) ^ (1 - s) / ((1 - s) * (Real.log x : ℂ))‖ *
          (Real.log x / x ^ a) := by ring
    _ ≤ _ := hmul
    _ = _ := by field_simp

/-! ## (3i) for the natural prime schedule -/

theorem sum_primesLE_eq_add_Ioc (F : ℕ → ℂ) {N : ℕ} (hN : 2 ≤ N) :
    ∑ p ∈ Nat.primesLE N, F p = F 2 + ∑ k ∈ Finset.Ioc 2 N, (if k.Prime then F k else 0) := by
  rw [Nat.primesLE, Nat.primesBelow, Finset.sum_filter, Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (show 0 ≤ 3 by norm_num) (show 3 ≤ N + 1 by omega)]
  congr 1
  rw [← Finset.range_eq_Ico]
  simp [Finset.sum_range_succ, Nat.not_prime_zero, Nat.not_prime_one, Nat.prime_two]

/-- **(3i).**  For `0 < σ < 1`,
`Σ_{p ≤ N} p^{−s} = N^{1−s}/((1−s) log N) + o(N^{1−σ}/log N)`. -/
theorem tendsto_sum_primesLE_cpow_sub_main {s : ℂ} (hσ0 : 0 < s.re) (hσ1 : s.re < 1) :
    Tendsto (fun N : ℕ => ‖(∑ p ∈ Nat.primesLE N, (p : ℂ) ^ (-s)) -
        ((N : ℝ) : ℂ) ^ (1 - s) / ((1 - s) * (Real.log N : ℂ))‖ * Real.log N / (N : ℝ) ^ (1 - s.re))
      atTop (𝓝 0) := by
  have ha : 0 < 1 - s.re := by linarith
  have hreal := (tendsto_primeCpowSumIoc_sub_main hσ0 hσ1).comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun N : ℕ => ‖(2 : ℂ) ^ (-s)‖ * (Real.log N / (N : ℝ) ^ (1 - s.re)))
      atTop (𝓝 0) := by
    simpa using ((tendsto_log_div_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).const_mul
      ‖(2 : ℂ) ^ (-s)‖
  have hsum := hreal.add hconst
  rw [zero_add] at hsum
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN)
    positivity
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN.trans_lt' (by norm_num)
  have hlog : 0 ≤ Real.log N / (N : ℝ) ^ (1 - s.re) := by
    have := Real.log_nonneg hN1.le; positivity
  rw [sum_primesLE_eq_add_Ioc (fun p => (p : ℂ) ^ (-s)) hN]
  have hIoc : (∑ k ∈ Finset.Ioc 2 N, (if k.Prime then (k : ℂ) ^ (-s) else 0)) =
      primeCpowSumIoc s (N : ℝ) := by rw [primeCpowSumIoc, Nat.floor_natCast]
  rw [hIoc]
  simp only [Function.comp]
  calc ‖((2 : ℕ) : ℂ) ^ (-s) + primeCpowSumIoc s N -
        ((N : ℝ) : ℂ) ^ (1 - s) / ((1 - s) * (Real.log N : ℂ))‖ * Real.log N / (N : ℝ) ^ (1 - s.re)
      = ‖(2 : ℂ) ^ (-s) + (primeCpowSumIoc s N -
        ((N : ℝ) : ℂ) ^ (1 - s) / ((1 - s) * (Real.log N : ℂ)))‖ *
          (Real.log N / (N : ℝ) ^ (1 - s.re)) := by push_cast; ring_nf
    _ ≤ (‖(2 : ℂ) ^ (-s)‖ + ‖primeCpowSumIoc s N -
        ((N : ℝ) : ℂ) ^ (1 - s) / ((1 - s) * (Real.log N : ℂ))‖) *
          (Real.log N / (N : ℝ) ^ (1 - s.re)) :=
        mul_le_mul_of_nonneg_right (norm_add_le _ _) hlog
    _ = _ := by ring

/-! ## (3j): the Euler envelope of the natural schedule -/

theorem norm_natCast_cpow_neg_le_two_rpow {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ (2 : ℝ) ^ (-s.re) := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp) (by linarith)

/-- The quadratic Euler-log error `log(1 − w) + w` at `w = p^{−s}`. -/
theorem norm_log_one_sub_add_le {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.log (1 - (p : ℂ) ^ (-s)) + (p : ℂ) ^ (-s)‖ ≤
      (1 - (2 : ℝ) ^ (-s.re))⁻¹ * ((p : ℝ) ^ (-s.re)) ^ 2 := by
  have hw := norm_natCast_cpow_neg_le_two_rpow hp hs
  have h2 : (2 : ℝ) ^ (-s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hw1 : ‖-((p : ℂ) ^ (-s))‖ < 1 := by rw [norm_neg]; linarith
  have h := Complex.norm_log_one_add_sub_self_le hw1
  rw [norm_neg, ← sub_eq_add_neg, sub_neg_eq_add] at h
  rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re] at h hw
  have hpos : 0 < 1 - (p : ℝ) ^ (-s.re) := by linarith
  have hpos2 : 0 < 1 - (2 : ℝ) ^ (-s.re) := by linarith
  refine h.trans ?_
  have hinv : (1 - (p : ℝ) ^ (-s.re))⁻¹ ≤ (1 - (2 : ℝ) ^ (-s.re))⁻¹ :=
    inv_anti₀ hpos2 (by linarith)
  have hsq : 0 ≤ ((p : ℝ) ^ (-s.re)) ^ 2 := sq_nonneg _
  calc ((p : ℝ) ^ (-s.re)) ^ 2 * (1 - (p : ℝ) ^ (-s.re))⁻¹ / 2
      ≤ ((p : ℝ) ^ (-s.re)) ^ 2 * (1 - (p : ℝ) ^ (-s.re))⁻¹ := by
        have : 0 ≤ ((p : ℝ) ^ (-s.re)) ^ 2 * (1 - (p : ℝ) ^ (-s.re))⁻¹ := by positivity
        linarith
    _ ≤ ((p : ℝ) ^ (-s.re)) ^ 2 * (1 - (2 : ℝ) ^ (-s.re))⁻¹ := mul_le_mul_of_nonneg_left hinv hsq
    _ = _ := by ring

theorem log_norm_finitePrimeEulerProduct {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {s : ℂ}
    (hs : 0 < s.re) :
    Real.log ‖finitePrimeEulerProduct S s‖ =
      ∑ p ∈ S, (Complex.log (1 - (p : ℂ) ^ (-s))).re := by
  rw [finitePrimeEulerProduct, Complex.norm_prod, Real.log_prod]
  · exact Finset.sum_congr rfl fun p _ => (Complex.log_re _).symm
  · intro p hp
    have := finitePrimeEulerProduct_ne_zero (S := {p}) (by simpa using hS p hp) hs
    rw [finitePrimeEulerProduct, Finset.prod_singleton] at this
    exact norm_ne_zero_iff.2 this

/-- The Euler-log error over all primes is uniformly bounded when `σ > 1/2`. -/
theorem abs_sum_primesLE_eulerLogError_le {s : ℂ} (hσ : 1 / 2 < s.re) (N : ℕ) :
    |∑ p ∈ Nat.primesLE N, (Complex.log (1 - (p : ℂ) ^ (-s)) + (p : ℂ) ^ (-s)).re| ≤
      (1 - (2 : ℝ) ^ (-s.re))⁻¹ * ∑' n : ℕ, (n : ℝ) ^ (-(2 * s.re)) := by
  have hs : 0 < s.re := by linarith
  have h2 : (2 : ℝ) ^ (-s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hK : 0 ≤ (1 - (2 : ℝ) ^ (-s.re))⁻¹ := inv_nonneg.2 (by linarith)
  have hsum : Summable fun n : ℕ => (n : ℝ) ^ (-(2 * s.re)) :=
    Real.summable_nat_rpow.2 (by linarith)
  calc _ ≤ ∑ p ∈ Nat.primesLE N, ‖Complex.log (1 - (p : ℂ) ^ (-s)) + (p : ℂ) ^ (-s)‖ :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun p _ => Complex.abs_re_le_norm _)
    _ ≤ ∑ p ∈ Nat.primesLE N, (1 - (2 : ℝ) ^ (-s.re))⁻¹ * (p : ℝ) ^ (-(2 * s.re)) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hp2 := (Nat.prime_of_mem_primesLE hp).two_le
        refine (norm_log_one_sub_add_le hp2 hs).trans_eq ?_
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
        congr 2; push_cast; ring
    _ = (1 - (2 : ℝ) ^ (-s.re))⁻¹ * ∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-(2 * s.re)) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (hsum.sum_le_tsum _ fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) hK

/-- **(3j).**  For `1/2 < σ < 1`,
`log |E_{S_N^nat}(s)| = −Re[N^{1−s}/((1−s) log N)] + o(N^{1−σ}/log N)`. -/
theorem tendsto_log_norm_naturalEuler_add_main {s : ℂ} (hσ0 : 1 / 2 < s.re) (hσ1 : s.re < 1) :
    Tendsto (fun N : ℕ => (Real.log ‖finitePrimeEulerProduct (Nat.primesLE N) s‖ +
        (((N : ℝ) : ℂ) ^ (1 - s) / ((1 - s) * (Real.log N : ℂ))).re) *
          Real.log N / (N : ℝ) ^ (1 - s.re)) atTop (𝓝 0) := by
  have hs : 0 < s.re := by linarith
  have ha : 0 < 1 - s.re := by linarith
  set Z : ℝ := (1 - (2 : ℝ) ^ (-s.re))⁻¹ * ∑' n : ℕ, (n : ℝ) ^ (-(2 * s.re))
  have hmain := tendsto_sum_primesLE_cpow_sub_main hs hσ1
  have hconst : Tendsto (fun N : ℕ => Z * (Real.log N / (N : ℝ) ^ (1 - s.re))) atTop (𝓝 0) := by
    simpa using ((tendsto_log_div_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).const_mul Z
  have hsum := hmain.add hconst
  rw [zero_add] at hsum
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hsum
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hlog : 0 ≤ Real.log N / (N : ℝ) ^ (1 - s.re) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN); positivity
  have hEq : Real.log ‖finitePrimeEulerProduct (Nat.primesLE N) s‖ +
      (((N : ℝ) : ℂ) ^ (1 - s) / ((1 - s) * (Real.log N : ℂ))).re =
        -((∑ p ∈ Nat.primesLE N, (p : ℂ) ^ (-s)) -
          ((N : ℝ) : ℂ) ^ (1 - s) / ((1 - s) * (Real.log N : ℂ))).re +
        ∑ p ∈ Nat.primesLE N, (Complex.log (1 - (p : ℂ) ^ (-s)) + (p : ℂ) ^ (-s)).re := by
    rw [log_norm_finitePrimeEulerProduct (fun p hp => Nat.prime_of_mem_primesLE hp) hs,
      Complex.sub_re, Complex.re_sum]
    simp only [Complex.add_re, Finset.sum_add_distrib]
    ring
  have hb : |Real.log ‖finitePrimeEulerProduct (Nat.primesLE N) s‖ +
      (((N : ℝ) : ℂ) ^ (1 - s) / ((1 - s) * (Real.log N : ℂ))).re| ≤
      ‖(∑ p ∈ Nat.primesLE N, (p : ℂ) ^ (-s)) -
          ((N : ℝ) : ℂ) ^ (1 - s) / ((1 - s) * (Real.log N : ℂ))‖ + Z := by
    rw [hEq]
    refine (abs_add_le _ _).trans (add_le_add ?_ (abs_sum_primesLE_eulerLogError_le hσ0 N))
    rw [abs_neg]; exact Complex.abs_re_le_norm _
  calc |(Real.log ‖finitePrimeEulerProduct (Nat.primesLE N) s‖ +
        (((N : ℝ) : ℂ) ^ (1 - s) / ((1 - s) * (Real.log N : ℂ))).re) * Real.log N /
          (N : ℝ) ^ (1 - s.re)|
      = |Real.log ‖finitePrimeEulerProduct (Nat.primesLE N) s‖ +
        (((N : ℝ) : ℂ) ^ (1 - s) / ((1 - s) * (Real.log N : ℂ))).re| *
          (Real.log N / (N : ℝ) ^ (1 - s.re)) := by
        rw [mul_div_assoc, abs_mul, abs_of_nonneg hlog]
    _ ≤ (‖(∑ p ∈ Nat.primesLE N, (p : ℂ) ^ (-s)) -
          ((N : ℝ) : ℂ) ^ (1 - s) / ((1 - s) * (Real.log N : ℂ))‖ + Z) *
          (Real.log N / (N : ℝ) ^ (1 - s.re)) := mul_le_mul_of_nonneg_right hb hlog
    _ = _ := by ring

/-! ## Phase peaks of the natural schedule -/

/-- `Re(c · x^w) = ‖c‖ x^{Re w} cos(arg c + Im w · log x)`. -/
theorem re_mul_ofReal_cpow {x : ℝ} (hx : 0 < x) (c w : ℂ) :
    (c * (x : ℂ) ^ w).re = ‖c‖ * x ^ w.re * Real.cos (c.arg + w.im * Real.log x) := by
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I c, Complex.cpow_def_of_ne_zero hxc,
    ← Complex.ofReal_log hx.le]
  rw [mul_assoc, ← Complex.exp_add, Complex.re_ofReal_mul, Complex.exp_re, Real.rpow_def_of_pos hx]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring_nf

/-- The real part of the main term is `‖1/(1−s)‖ cos(arg(1/(1−s)) − τ log x) · x^{1−σ}/log x`. -/
theorem re_naturalMainTerm (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ((x : ℂ) ^ (1 - s) / ((1 - s) * (Real.log x : ℂ))).re =
      ‖1 / (1 - s)‖ * Real.cos ((1 / (1 - s)).arg - s.im * Real.log x) *
        (x ^ (1 - s.re) / Real.log x) := by
  have h : (x : ℂ) ^ (1 - s) / ((1 - s) * (Real.log x : ℂ)) =
      1 / (1 - s) * (x : ℂ) ^ (1 - s) / (Real.log x : ℂ) := by
    simp only [div_eq_mul_inv, mul_inv, one_mul]
    ring
  rw [h, Complex.div_ofReal_re, re_mul_ofReal_cpow hx]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub, neg_mul]
  ring_nf

theorem frequently_half_le_cos_sub_mul_log_of_pos {τ : ℝ} (hτ : 0 < τ) (θ₀ : ℝ) :
    ∃ᶠ N : ℕ in atTop, 1 / 2 ≤ Real.cos (θ₀ - τ * Real.log N) := by
  set u : ℕ → ℝ := fun k => (θ₀ + k * (2 * Real.pi)) / τ with hu_def
  set M : ℕ → ℕ := fun k => ⌈Real.exp (u k)⌉₊ with hM_def
  have hu : Tendsto u atTop atTop := by
    have h : Tendsto (fun k : ℕ => (k : ℝ) * (2 * Real.pi)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
    exact (tendsto_atTop_add_const_left _ θ₀ h).atTop_div_const hτ
  have hMge : ∀ k, Real.exp (u k) ≤ (M k : ℝ) := fun k => Nat.le_ceil _
  have hMlt : ∀ k, (M k : ℝ) < Real.exp (u k) + 1 := fun k => Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hMpos : ∀ k, 0 < (M k : ℝ) := fun k => (Real.exp_pos _).trans_le (hMge k)
  have hM : Tendsto (fun k => (M k : ℝ)) atTop atTop :=
    tendsto_atTop_mono hMge (Real.tendsto_exp_atTop.comp hu)
  have hd0 : ∀ k, 0 ≤ Real.log (M k) - u k := fun k => by
    have := Real.log_le_log (Real.exp_pos _) (hMge k); rw [Real.log_exp] at this; linarith
  have hd1 : ∀ k, Real.log (M k) - u k ≤ Real.exp (-u k) := fun k => by
    have h1 : Real.log (M k) - u k = Real.log ((M k : ℝ) / Real.exp (u k)) := by
      rw [Real.log_div (hMpos k).ne' (Real.exp_pos _).ne', Real.log_exp]
    have h2 := Real.log_le_sub_one_of_pos (div_pos (hMpos k) (Real.exp_pos (u k)))
    have h3 : (M k : ℝ) / Real.exp (u k) - 1 < Real.exp (-u k) := by
      rw [Real.exp_neg, div_sub_one (Real.exp_pos _).ne', div_lt_iff₀ (Real.exp_pos _),
        inv_mul_cancel₀ (Real.exp_pos _).ne']
      linarith [hMlt k]
    linarith
  have hd : Tendsto (fun k => Real.log (M k) - u k) atTop (𝓝 0) :=
    squeeze_zero hd0 hd1 (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hu))
  have hcos : ∀ k, Real.cos (θ₀ - τ * Real.log (M k)) = Real.cos (τ * (Real.log (M k) - u k)) := by
    intro k
    have : θ₀ - τ * Real.log (M k) = -(τ * (Real.log (M k) - u k) + k * (2 * Real.pi)) := by
      simp only [hu_def]; field_simp; ring
    rw [this, Real.cos_neg, Real.cos_add_nat_mul_two_pi]
  have hlim : Tendsto (fun k => Real.cos (θ₀ - τ * Real.log (M k))) atTop (𝓝 1) := by
    simp_rw [hcos]
    have hτd : Tendsto (fun k => τ * (Real.log (M k) - u k)) atTop (𝓝 0) := by
      simpa using hd.const_mul τ
    have := (Real.continuous_cos.tendsto 0).comp hτd
    rw [Real.cos_zero] at this
    exact this
  rw [frequently_atTop]
  intro N₀
  obtain ⟨k, hk1, hk2⟩ := ((hM.eventually_ge_atTop (N₀ : ℝ)).and
    (hlim.eventually (le_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1)))).exists
  exact ⟨M k, by exact_mod_cast hk1, hk2⟩

theorem frequently_half_le_cos_sub_mul_log {τ : ℝ} (hτ : τ ≠ 0) (θ₀ : ℝ) :
    ∃ᶠ N : ℕ in atTop, 1 / 2 ≤ Real.cos (θ₀ - τ * Real.log N) := by
  rcases lt_or_gt_of_ne hτ with h | h
  · refine (frequently_half_le_cos_sub_mul_log_of_pos (neg_pos.2 h) (-θ₀)).mono fun N hN => ?_
    rwa [show -θ₀ - -τ * Real.log N = -(θ₀ - τ * Real.log N) by ring, Real.cos_neg] at hN
  · exact frequently_half_le_cos_sub_mul_log_of_pos h θ₀

theorem frequently_cos_sub_mul_log_le_neg_half {τ : ℝ} (hτ : τ ≠ 0) (θ₀ : ℝ) :
    ∃ᶠ N : ℕ in atTop, Real.cos (θ₀ - τ * Real.log N) ≤ -(1 / 2) :=
  (frequently_half_le_cos_sub_mul_log hτ (θ₀ + Real.pi)).mono fun N hN => by
    rw [show θ₀ + Real.pi - τ * Real.log N = θ₀ - τ * Real.log N + Real.pi by ring,
      Real.cos_add_pi] at hN
    linarith

/-! ## Faster than every power -/

/-- `N^a/log N` dominates every multiple of `log N`. -/
theorem eventually_mul_log_le_rpow_div_log {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∀ᶠ N : ℕ in atTop, b * Real.log N ≤ (N : ℝ) ^ a / Real.log N := by
  have h := (tendsto_rpow_div_log_atTop_of_pos (r := a / 2) (by linarith)).comp
    tendsto_natCast_atTop_atTop
  have hsq := h.atTop_mul_atTop₀ h
  filter_upwards [hsq.eventually_ge_atTop b, eventually_ge_atTop 2] with N hN hN2
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN2.trans_lt' (by norm_num)
  have hlog : 0 < Real.log N := Real.log_pos hN1
  simp only [Function.comp] at hN
  have hsplit : (N : ℝ) ^ (a / 2) * (N : ℝ) ^ (a / 2) = (N : ℝ) ^ a := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  have : (N : ℝ) ^ (a / 2) / Real.log N * ((N : ℝ) ^ (a / 2) / Real.log N) =
      (N : ℝ) ^ a / Real.log N / Real.log N := by
    rw [← hsplit]; field_simp
  rw [this, le_div_iff₀ hlog] at hN
  linarith

theorem tendsto_mul_rpow_of_log_le_neg {E Y : ℕ → ℝ} {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (hE : ∀ n, 0 < E n) {c : ℝ} (hc : 0 < c)
    (hlog : ∀ᶠ n in atTop, Real.log (E n) ≤ -c * Y n)
    (hY : ∀ b : ℝ, ∀ᶠ n in atTop, b * Real.log (φ n) ≤ Y n) (A : ℝ) :
    Tendsto (fun n => E n * (φ n : ℝ) ^ A) atTop (𝓝 0) := by
  have hYt : Tendsto Y atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    have hl : Tendsto (fun n => Real.log (φ n)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hφ)
    filter_upwards [hY 1, hl.eventually_ge_atTop b] with n h1 h2
    linarith
  have hmaj : Tendsto (fun n => Real.exp (-(c / 2) * Y n)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (hYt.const_mul_atTop_of_neg (by linarith))
  refine squeeze_zero' (Eventually.of_forall fun n => by
    have := hE n; positivity) ?_ hmaj
  filter_upwards [hlog, hY (2 * A / c),
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hφ).eventually_ge_atTop 1] with n h1 h2 h3
  have hφpos : (0 : ℝ) < φ n := by simp only [Function.comp] at h3; linarith
  rw [Real.rpow_def_of_pos hφpos, ← Real.exp_log (hE n), ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have : A * Real.log (φ n) ≤ c / 2 * Y n := by
    have := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ c / 2)
    rw [show c / 2 * (2 * A / c * Real.log (φ n)) = A * Real.log (φ n) by field_simp] at this
    linarith
  nlinarith

theorem tendsto_div_rpow_of_log_ge {E Y : ℕ → ℝ} {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (hE : ∀ n, 0 < E n) {c : ℝ} (hc : 0 < c)
    (hlog : ∀ᶠ n in atTop, c * Y n ≤ Real.log (E n))
    (hY : ∀ b : ℝ, ∀ᶠ n in atTop, b * Real.log (φ n) ≤ Y n) (A : ℝ) :
    Tendsto (fun n => E n / (φ n : ℝ) ^ A) atTop atTop := by
  have hYt : Tendsto Y atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    have hl : Tendsto (fun n => Real.log (φ n)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hφ)
    filter_upwards [hY 1, hl.eventually_ge_atTop b] with n h1 h2
    linarith
  have hmin : Tendsto (fun n => Real.exp (c / 2 * Y n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (hYt.const_mul_atTop (by linarith))
  refine tendsto_atTop_mono' atTop ?_ hmin
  filter_upwards [hlog, hY (2 * A / c),
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hφ).eventually_ge_atTop 1] with n h1 h2 h3
  have hφpos : (0 : ℝ) < φ n := by simp only [Function.comp] at h3; linarith
  rw [Real.rpow_def_of_pos hφpos, ← Real.exp_log (hE n), ← Real.exp_sub]
  refine Real.exp_le_exp.2 ?_
  have : A * Real.log (φ n) ≤ c / 2 * Y n := by
    have := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ c / 2)
    rw [show c / 2 * (2 * A / c * Real.log (φ n)) = A * Real.log (φ n) by field_simp] at this
    linarith
  linarith [mul_comm A (Real.log (φ n))]

/-! ## The raw spectral observation along the natural schedule -/

theorem tendsto_natCast_cpow_sub_one {s : ℂ} (hσ1 : s.re < 1) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ (s - 1)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (tendsto_rpow_neg_atTop (show 0 < 1 - s.re by linarith)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  simp only [Function.comp]
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  congr 1; simp

theorem tendsto_natCast_cpow_sub_one_mul_harmonicCutoff {s : ℂ} (hσ0 : 0 < s.re) (hσ1 : s.re < 1) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ (s - 1) * harmonicCutoff N s) atTop (𝓝 (1 / (1 - s))) := by
  have h := ((tendsto_natCast_cpow_sub_one hσ1).mul (harmonicCutoff_sub_tendsto hσ0 hσ1)).add
    (tendsto_const_nhds (x := 1 / (1 - s)))
  rw [zero_mul, zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hone : (N : ℂ) ^ (s - 1) * (N : ℂ) ^ (1 - s) = 1 := by
    rw [← Complex.cpow_add _ _ hNc, show s - 1 + (1 - s) = 0 by ring, Complex.cpow_zero]
  simp only [Complex.ofReal_natCast]
  rw [mul_sub, mul_div_assoc', hone]
  ring

/-- The phase decomposition of (3j): `log‖E_N‖/Y_N + R cos(θ₀ − τ log N) → 0`. -/
theorem tendsto_log_norm_naturalEuler_phase {s : ℂ} (hσ0 : 1 / 2 < s.re) (hσ1 : s.re < 1) :
    Tendsto (fun N : ℕ => Real.log ‖finitePrimeEulerProduct (Nat.primesLE N) s‖ /
        ((N : ℝ) ^ (1 - s.re) / Real.log N) +
        ‖1 / (1 - s)‖ * Real.cos ((1 / (1 - s)).arg - s.im * Real.log N)) atTop (𝓝 0) := by
  refine (tendsto_log_norm_naturalEuler_add_main hσ0 hσ1).congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN.trans_lt' (by norm_num)
  have hlog : Real.log N ≠ 0 := (Real.log_pos hN1).ne'
  have hpow : (N : ℝ) ^ (1 - s.re) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  rw [re_naturalMainTerm s (by linarith)]
  field_simp

/-- **(3j), oscillation.**  Fix `s = σ + iτ` with `1/2 < σ < 1` and `τ ≠ 0`.  Along one integer
subsequence `|E_{S_N^nat}(s)| → 0` faster than every power of `N` and the raw spectral observation
`M_{S_N^nat,N}(s−1)` tends to `0`; along another `|E_{S_N^nat}(s)| → ∞` faster than every power,
`M_{S_N^nat,N}(s−1) = −G(s−1)E_{S_N^nat}(s)(1+o(1))`, and `|M| → ∞`. -/
theorem natural_schedule_spectral_oscillation {s : ℂ} (hσ0 : 1 / 2 < s.re) (hσ1 : s.re < 1)
    (hτ : s.im ≠ 0) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ A : ℝ, Tendsto (fun n => ‖finitePrimeEulerProduct (Nat.primesLE (φ n)) s‖ *
        (φ n : ℝ) ^ A) atTop (𝓝 0)) ∧
      Tendsto (fun n => commutatorSpectralObservation (Nat.primesLE (φ n)) (φ n) (s - 1)) atTop
        (𝓝 0)) ∧
    (∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ A : ℝ, Tendsto (fun n => ‖finitePrimeEulerProduct (Nat.primesLE (φ n)) s‖ /
        (φ n : ℝ) ^ A) atTop atTop) ∧
      Tendsto (fun n => commutatorSpectralObservation (Nat.primesLE (φ n)) (φ n) (s - 1) /
        (-commutatorGammaFactor (s - 1) * finitePrimeEulerProduct (Nat.primesLE (φ n)) s)) atTop
        (𝓝 1) ∧
      Tendsto (fun n => ‖commutatorSpectralObservation (Nat.primesLE (φ n)) (φ n) (s - 1)‖) atTop
        atTop) := by
  have hs : 0 < s.re := by linarith
  have ha : 0 < 1 - s.re := by linarith
  have h1s : (1 : ℂ) - s ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  set R : ℝ := ‖1 / (1 - s)‖ with hR_def
  have hR : 0 < R := norm_pos_iff.2 (one_div_ne_zero h1s)
  set θ₀ : ℝ := (1 / (1 - s)).arg
  set Ec : ℕ → ℂ := fun N => finitePrimeEulerProduct (Nat.primesLE N) s with hEc
  have hEne : ∀ N, Ec N ≠ 0 := fun N =>
    finitePrimeEulerProduct_ne_zero (fun p hp => Nat.prime_of_mem_primesLE hp) hs
  have hEpos : ∀ N, 0 < ‖Ec N‖ := fun N => norm_pos_iff.2 (hEne N)
  set Y : ℕ → ℝ := fun N => (N : ℝ) ^ (1 - s.re) / Real.log N with hY_def
  have hphase := tendsto_log_norm_naturalEuler_phase hσ0 hσ1
  have hG : commutatorGammaFactor (s - 1) ≠ 0 := commutatorGammaFactor_ne_zero (by simp; linarith)
  have hHN := tendsto_natCast_cpow_sub_one_mul_harmonicCutoff hs hσ1
  have hNs := tendsto_natCast_cpow_sub_one hσ1
  -- the observation in terms of `E`, `N^{s−1} H_N` and `N^{s−1}`
  have hMeq : ∀ N : ℕ, 1 ≤ N → commutatorSpectralObservation (Nat.primesLE N) N (s - 1) =
      (s - 1) * commutatorGammaFactor (s - 1) *
        (Ec N * ((N : ℂ) ^ (s - 1) * harmonicCutoff N s) - (N : ℂ) ^ (s - 1)) := fun N hN => by
    rw [commutatorSpectralObservation_eq (fun p hp => Nat.prime_of_mem_primesLE hp) hN
      (fun p hp hpN => Nat.mem_primesLE.2 ⟨hpN, hp⟩) (by linarith)]
    ring
  have hYpos : ∀ᶠ N : ℕ in atTop, 0 < Y N := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hN1 : (1 : ℝ) < N := by exact_mod_cast hN.trans_lt' (by norm_num)
    exact div_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.log_pos hN1)
  constructor
  · obtain ⟨φ, hφm, hφc⟩ := extraction_of_frequently_atTop
      (frequently_half_le_cos_sub_mul_log hτ θ₀)
    have hφ : Tendsto φ atTop atTop := hφm.tendsto_atTop
    have hlog : ∀ᶠ n in atTop, Real.log ‖Ec (φ n)‖ ≤ -(R / 4) * Y (φ n) := by
      filter_upwards [(hphase.comp hφ).eventually (gt_mem_nhds (by linarith : (0 : ℝ) < R / 4)),
        hφ.eventually hYpos] with n hn hYn
      have hn' : Real.log ‖Ec (φ n)‖ / Y (φ n) + R * Real.cos (θ₀ - s.im * Real.log (φ n)) <
          R / 4 := hn
      have hc := mul_le_mul_of_nonneg_left (hφc n) hR.le
      have h1 : Real.log ‖Ec (φ n)‖ / Y (φ n) ≤ -(R / 4) := by linarith
      rwa [div_le_iff₀ hYn] at h1
    have hpow : ∀ A : ℝ, Tendsto (fun n => ‖Ec (φ n)‖ * (φ n : ℝ) ^ A) atTop (𝓝 0) :=
      tendsto_mul_rpow_of_log_le_neg hφ (fun n => hEpos _) (by linarith) hlog
        (fun b => hφ.eventually (eventually_mul_log_le_rpow_div_log ha b))
    refine ⟨φ, hφm, hpow, ?_⟩
    have hE0 : Tendsto (fun n => Ec (φ n)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simpa using hpow 0
    have hlim := ((hE0.mul (hHN.comp hφ)).sub (hNs.comp hφ)).const_mul
      ((s - 1) * commutatorGammaFactor (s - 1))
    rw [zero_mul, sub_zero, mul_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [hφ.eventually (eventually_ge_atTop 1)] with n hn
    rw [hMeq _ hn]; rfl
  · obtain ⟨φ, hφm, hφc⟩ := extraction_of_frequently_atTop
      (frequently_cos_sub_mul_log_le_neg_half hτ θ₀)
    have hφ : Tendsto φ atTop atTop := hφm.tendsto_atTop
    have hlog : ∀ᶠ n in atTop, R / 4 * Y (φ n) ≤ Real.log ‖Ec (φ n)‖ := by
      filter_upwards [(hphase.comp hφ).eventually (lt_mem_nhds (by linarith : -(R / 4) < (0 : ℝ))),
        hφ.eventually hYpos] with n hn hYn
      have hn' : -(R / 4) < Real.log ‖Ec (φ n)‖ / Y (φ n) +
          R * Real.cos (θ₀ - s.im * Real.log (φ n)) := hn
      have hc := mul_le_mul_of_nonneg_left (hφc n) hR.le
      have h1 : R / 4 ≤ Real.log ‖Ec (φ n)‖ / Y (φ n) := by linarith
      rwa [le_div_iff₀ hYn] at h1
    have hpow : ∀ A : ℝ, Tendsto (fun n => ‖Ec (φ n)‖ / (φ n : ℝ) ^ A) atTop atTop :=
      tendsto_div_rpow_of_log_ge hφ (fun n => hEpos _) (by linarith) hlog
        (fun b => hφ.eventually (eventually_mul_log_le_rpow_div_log ha b))
    have hEinf : Tendsto (fun n => ‖Ec (φ n)‖) atTop atTop := by simpa using hpow 0
    have hEinv : Tendsto (fun n => (Ec (φ n))⁻¹) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_inv]
      exact tendsto_inv_atTop_zero.comp hEinf
    have hratio : Tendsto (fun n => commutatorSpectralObservation (Nat.primesLE (φ n)) (φ n) (s - 1) /
        (-commutatorGammaFactor (s - 1) * Ec (φ n))) atTop (𝓝 1) := by
      have hlim := ((hHN.comp hφ).const_mul (-(s - 1))).add
        (((hNs.comp hφ).mul hEinv).const_mul (s - 1))
      rw [mul_zero, mul_zero, add_zero,
        show -(s - 1) * (1 / (1 - s)) = 1 by field_simp; ring] at hlim
      refine hlim.congr' ?_
      filter_upwards [hφ.eventually (eventually_ge_atTop 1)] with n hn
      rw [hMeq _ hn]
      simp only [Function.comp]
      field_simp [hEne (φ n), hG]
      ring
    refine ⟨φ, hφm, hpow, hratio, ?_⟩
    have hGE : Tendsto (fun n => ‖commutatorGammaFactor (s - 1)‖ * ‖Ec (φ n)‖ / 2) atTop atTop :=
      (hEinf.const_mul_atTop (norm_pos_iff.2 hG)).atTop_div_const (by norm_num)
    refine tendsto_atTop_mono' atTop ?_ hGE
    filter_upwards [hratio.norm.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) / 2 < ‖(1 : ℂ)‖))]
      with n hn
    have hden : -commutatorGammaFactor (s - 1) * Ec (φ n) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.2 hG) (hEne _)
    have hM : commutatorSpectralObservation (Nat.primesLE (φ n)) (φ n) (s - 1) =
        (commutatorSpectralObservation (Nat.primesLE (φ n)) (φ n) (s - 1) /
          (-commutatorGammaFactor (s - 1) * Ec (φ n))) * (-commutatorGammaFactor (s - 1) * Ec (φ n)) :=
      (div_mul_cancel₀ _ hden).symm
    rw [hM, norm_mul, norm_mul, norm_neg]
    have h0 : 0 ≤ ‖commutatorGammaFactor (s - 1)‖ * ‖Ec (φ n)‖ := by positivity
    nlinarith

end

end RHTower
