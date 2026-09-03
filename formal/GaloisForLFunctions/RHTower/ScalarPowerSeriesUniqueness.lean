import Mathlib

/-!
# Uniqueness of scalar power-series coefficients, and the complex binomial series

Two conveniences used by the semilocal boost programme:

* `eq_of_hasSum_mul_pow_eq`: if `Σ aₙ wⁿ` and `Σ bₙ wⁿ` both converge to the same function on a
  disc of positive radius, then `a = b`.
* `hasSum_one_add_cpow` / `hasSum_one_sub_cpow_neg`: the complex binomial series
  `(1 + x)^a = Σ (a choose n) xⁿ` on `‖x‖ < 1`, unpacked from Mathlib's `binomialSeries`.
-/

open Filter
open scoped Topology

namespace RHTower

namespace PowerSeriesUniqueness

/-- A convergent scalar power series on a disc is a `HasFPowerSeriesOnBall` with the
`ofScalars` series, on the half-radius. -/
theorem hasFPowerSeriesOnBall_of_hasSum {a : ℕ → ℂ} {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (ha : ∀ w : ℂ, ‖w‖ < r → HasSum (fun n => a n * w ^ n) (f w)) :
    HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ a) 0 (ENNReal.ofReal (r / 2)) where
  r_le := by
    have hsum := (ha ((r / 2 : ℝ) : ℂ) (by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith)).summable
    have htend := hsum.tendsto_atTop_zero
    have hnorm : Tendsto (fun n => ‖FormalMultilinearSeries.ofScalars ℂ a n‖ * ((⟨r / 2, by linarith⟩ : NNReal) : ℝ) ^ n)
        atTop (𝓝 0) := by
      have := htend.norm
      rw [norm_zero] at this
      refine this.congr fun n => ?_
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith),
        FormalMultilinearSeries.ofScalars_norm]
    have := FormalMultilinearSeries.le_radius_of_tendsto _ hnorm
    rwa [ENNReal.ofReal_eq_coe_nnreal (by linarith : (0 : ℝ) ≤ r / 2)]
  r_pos := by simpa using (by linarith : (0 : ℝ) < r / 2)
  hasSum := by
    intro y hy
    have hy' : ‖y‖ < r := by
      rw [Metric.mem_eball, edist_zero_right] at hy
      have : ENNReal.ofReal ‖y‖ < ENNReal.ofReal (r / 2) := by
        rwa [← ofReal_norm] at hy
      have h2 := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mp this
      linarith
    have h := ha y hy'
    rw [zero_add]
    refine h.congr_fun fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

/-- **Uniqueness of power-series coefficients.** -/
theorem eq_of_hasSum_mul_pow_eq {a b : ℕ → ℂ} {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (ha : ∀ w : ℂ, ‖w‖ < r → HasSum (fun n => a n * w ^ n) (f w))
    (hb : ∀ w : ℂ, ‖w‖ < r → HasSum (fun n => b n * w ^ n) (f w)) : a = b := by
  have hA := (hasFPowerSeriesOnBall_of_hasSum hr ha).hasFPowerSeriesAt
  have hB := (hasFPowerSeriesOnBall_of_hasSum hr hb).hasFPowerSeriesAt
  have h := hA.eq_formalMultilinearSeries hB
  funext n
  have h1 := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p n (fun _ => (1 : ℂ))) h
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one] at h1
  exact h1

/-- Coefficients of two power-series representations of the same function on a disc agree
pointwise (a restatement of `eq_of_hasSum_mul_pow_eq`). -/
theorem coeff_eq_of_hasSum_mul_pow_eq {a b : ℕ → ℂ} {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (ha : ∀ w : ℂ, ‖w‖ < r → HasSum (fun n => a n * w ^ n) (f w))
    (hb : ∀ w : ℂ, ‖w‖ < r → HasSum (fun n => b n * w ^ n) (f w)) (n : ℕ) : a n = b n :=
  congrFun (eq_of_hasSum_mul_pow_eq hr ha hb) n

/-! ## The complex binomial series -/

/-- `(1 + x)^a = Σ (a choose n) xⁿ` for `‖x‖ < 1`. -/
theorem hasSum_one_add_cpow (a : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => Ring.choose a n * x ^ n) ((1 + x) ^ a) := by
  have hmem : x ∈ Metric.eball (0 : ℂ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
    exact ENNReal.ofReal_lt_one.mpr hx
  have h := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := a)).hasSum hmem
  rw [zero_add] at h
  refine h.congr_fun fun n => ?_
  rw [binomialSeries_apply, List.ofFn_const, List.prod_replicate, smul_eq_mul]

/-- `(1 − u)^{−a} = Σ ((−a) choose n) (−u)ⁿ` for `‖u‖ < 1`. -/
theorem hasSum_one_sub_cpow_neg (a : ℂ) {u : ℂ} (hu : ‖u‖ < 1) :
    HasSum (fun n : ℕ => Ring.choose (-a) n * (-u) ^ n) ((1 - u) ^ (-a)) := by
  have h := hasSum_one_add_cpow (-a) (x := -u) (by simpa using hu)
  simpa [sub_eq_add_neg] using h

/-! ## Taylor coefficients and real-axis uniqueness -/

/-- The coefficients of a convergent power series are the Taylor coefficients. -/
theorem coeff_eq_iteratedDeriv_div_factorial_of_hasSum {a : ℕ → ℂ} {f : ℂ → ℂ} {r : ℝ}
    (hr : 0 < r) (ha : ∀ w : ℂ, ‖w‖ < r → HasSum (fun n => a n * w ^ n) (f w)) (n : ℕ) :
    a n = iteratedDeriv n f 0 / n.factorial := by
  have hball := hasFPowerSeriesOnBall_of_hasSum hr ha
  have hdiff : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) (r / 2)) := by
    have := hball.differentiableOn
    rwa [Metric.emetric_ball] at this
  have hb : ∀ w : ℂ, ‖w‖ < r / 2 →
      HasSum (fun n => (iteratedDeriv n f 0 / n.factorial) * w ^ n) (f w) := by
    intro w hw
    have h := Complex.hasSum_taylorSeries_on_ball hdiff (z := w) (by simpa using hw)
    refine h.congr_fun fun n => ?_
    rw [sub_zero, smul_eq_mul, smul_eq_mul]
    ring
  have ha' : ∀ w : ℂ, ‖w‖ < r / 2 → HasSum (fun n => a n * w ^ n) (f w) :=
    fun w hw => ha w (by linarith)
  exact congrFun (eq_of_hasSum_mul_pow_eq (by linarith) ha' hb) n

/-- **Real-axis uniqueness.**  Two power series converging on a complex disc whose sums agree on
the real diameter have the same coefficients. -/
theorem eq_of_hasSum_mul_pow_eq_of_ofReal {a b : ℕ → ℂ} {F H : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (ha : ∀ w : ℂ, ‖w‖ < r → HasSum (fun n => a n * w ^ n) (F w))
    (hb : ∀ w : ℂ, ‖w‖ < r → HasSum (fun n => b n * w ^ n) (H w))
    (hFH : ∀ x : ℝ, |x| < r → F x = H x) : a = b := by
  have hA := (hasFPowerSeriesOnBall_of_hasSum hr ha).analyticOnNhd
  have hB := (hasFPowerSeriesOnBall_of_hasSum hr hb).analyticOnNhd
  rw [Metric.emetric_ball] at hA hB
  have hpre : IsPreconnected (Metric.ball (0 : ℂ) (r / 2)) := (convex_ball _ _).isPreconnected
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (r / 2) := Metric.mem_ball_self (by linarith)
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), F z = H z := by
    rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hU
    refine ⟨((min ε r / 2 : ℝ) : ℂ), hsub ⟨?_, ?_⟩, hFH _ ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith [min_le_left ε r]
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
      positivity
    · rw [abs_of_pos (by positivity)]
      linarith [min_le_right ε r]
  have hEq := hA.eqOn_of_preconnected_of_frequently_eq hB hpre h0 hfreq
  have hb' : ∀ w : ℂ, ‖w‖ < r / 2 → HasSum (fun n => b n * w ^ n) (F w) := by
    intro w hw
    rw [hEq (by simpa using hw)]
    exact hb w (by linarith)
  exact eq_of_hasSum_mul_pow_eq (by linarith) (fun w hw => ha w (by linarith)) hb'

end PowerSeriesUniqueness

end RHTower
