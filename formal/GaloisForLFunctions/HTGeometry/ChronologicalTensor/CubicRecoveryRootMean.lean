import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRecoveryExponentialRate

/-!
# The mean root location of the recovery optimizers

For the weighted Chebyshev optimizers `T_m` (roots `r_i ∈ (0, 1/4)`, `S_m = Σ r_i`),

  `S_m / m → A = b/(4π) + 3b²/16`,

where `b = cos θ` is the recovery edge.  Equivalently, with `t_i = √(1 - 4r_i)`, the mean of `t_i²`
tends to `1 - b/π - 3b²/4`.

The proof averages `log(W^m |T_m|) ≤ log t_m` along `r(θ) = (1 - b² cos² θ)/4` against the positive
weights `(1 + δ cos 2θ)/π`, `|δ| ≤ 1`.  On the support the weighted arcsine potential is
`π log(b/2) - δ(π/2)(2t²/b² - 1)`; off it, it is monotone in `t`, and the unweighted potential
`π log((t + √(t² - b²))/2)` controls the roots outside `[-b, b]`.  With `log t_m - m log ρ = o(m)`,
`δ = ±1` pin down `(1/m)Σ(2t_i²/b² - 1)` to `E₂/π`, where
`E₂ = ∫_0^π log(1 - b|cos θ|) cos 2θ dθ = 2(π/b² - 1/b - 5π/4)` at the edge (`I(b) = 3π/2`).
-/

open MeasureTheory Set Filter intervalIntegral Polynomial
open scoped Real Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor

/-! ### The weighted arcsine potential -/

theorem integral_cos_two_mul_zero_pi : ∫ θ in (0 : ℝ)..π, Real.cos (2 * θ) = 0 := by
  rw [intervalIntegral.integral_comp_mul_left (fun θ => Real.cos θ) two_ne_zero, integral_cos]
  simp [Real.sin_two_pi]

theorem integral_one_add_mul_cos_two (δ : ℝ) :
    ∫ θ in (0 : ℝ)..π, (1 + δ * Real.cos (2 * θ)) = π := by
  rw [integral_add intervalIntegrable_const
    ((by fun_prop : Continuous fun θ : ℝ => δ * Real.cos (2 * θ)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_cos_two_mul_zero_pi]
  simp

theorem one_add_mul_cos_two_nonneg {δ : ℝ} (hδ : |δ| ≤ 1) (θ : ℝ) :
    0 ≤ 1 + δ * Real.cos (2 * θ) := by
  have h : |δ * Real.cos (2 * θ)| ≤ 1 := by
    rw [abs_mul]; exact mul_le_one₀ hδ (abs_nonneg _) (Real.abs_cos_le_one _)
  linarith [(abs_le.mp h).1]

theorem intervalIntegrable_log_mul_cos_sub_mul {b : ℝ} (hb : 0 < b) (x : ℝ) {g : ℝ → ℝ}
    (hg : Continuous g) :
    IntervalIntegrable (fun θ => Real.log (b * Real.cos θ - x) * g θ) volume 0 π :=
  (intervalIntegrable_log_mul_cos_sub hb x).mul_continuousOn hg.continuousOn

/-- On the support, `∫_0^π log|b cos θ - x| (1 + δ cos 2θ) dθ = π log(b/2) - δ(π/2)(2x²/b² - 1)`. -/
theorem integral_log_mul_cos_sub_weight_of_abs_le {b x : ℝ} (hb : 0 < b) (hx : |x| ≤ b)
    (δ : ℝ) :
    ∫ θ in (0 : ℝ)..π, Real.log (b * Real.cos θ - x) * (1 + δ * Real.cos (2 * θ)) =
      π * Real.log (b / 2) - δ * (π / 2) * (2 * x ^ 2 / b ^ 2 - 1) := by
  have h1 := intervalIntegrable_log_mul_cos_sub hb x
  have h2 := intervalIntegrable_log_mul_cos_sub_mul hb x
    (g := fun θ => Real.cos (2 * θ)) (by fun_prop)
  have e : ∀ θ, Real.log (b * Real.cos θ - x) * (1 + δ * Real.cos (2 * θ)) =
      Real.log (b * Real.cos θ - x) + δ * (Real.log (b * Real.cos θ - x) * Real.cos (2 * θ)) :=
    fun θ => by ring
  simp_rw [e]
  rw [integral_add h1 (h2.const_mul δ), intervalIntegral.integral_const_mul,
    integral_log_mul_cos_sub_of_abs_le hb hx, integral_log_mul_cos_sub_mul_cos_two hb hx]
  ring

/-- Off the support the weighted potential increases: `b ≤ y ≤ x`, `|δ| ≤ 1`. -/
theorem integral_log_mul_cos_sub_weight_mono {b x y δ : ℝ} (hb : 0 < b) (hby : b ≤ y)
    (hyx : y ≤ x) (hδ : |δ| ≤ 1) :
    ∫ θ in (0 : ℝ)..π, Real.log (b * Real.cos θ - y) * (1 + δ * Real.cos (2 * θ)) ≤
      ∫ θ in (0 : ℝ)..π, Real.log (b * Real.cos θ - x) * (1 + δ * Real.cos (2 * θ)) := by
  refine integral_mono_ae_restrict Real.pi_pos.le
    (intervalIntegrable_log_mul_cos_sub_mul hb y (by fun_prop))
    (intervalIntegrable_log_mul_cos_sub_mul hb x (by fun_prop)) ?_
  have hne : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∉ ({0} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp (measure_singleton 0)
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with θ hθ hθ0
  simp only [mem_singleton_iff] at hθ0
  have hc : Real.cos θ < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθ.2 (lt_of_le_of_ne hθ.1 (Ne.symm hθ0))
    rwa [Real.cos_zero] at this
  refine mul_le_mul_of_nonneg_right ?_ (one_add_mul_cos_two_nonneg hδ θ)
  rw [← Real.log_neg_eq_log (b * Real.cos θ - y), ← Real.log_neg_eq_log (b * Real.cos θ - x)]
  exact Real.log_le_log (by nlinarith) (by linarith)

/-- The weighted potential is even in `x`. -/
theorem integral_log_mul_cos_add_weight (b t δ : ℝ) :
    ∫ θ in (0 : ℝ)..π, Real.log (b * Real.cos θ - -t) * (1 + δ * Real.cos (2 * θ)) =
      ∫ θ in (0 : ℝ)..π, Real.log (b * Real.cos θ - t) * (1 + δ * Real.cos (2 * θ)) := by
  have h := integral_comp_sub_left (a := 0) (b := π)
    (fun θ => Real.log (b * Real.cos θ - t) * (1 + δ * Real.cos (2 * θ))) π
  simp only [sub_zero, sub_self, Real.cos_pi_sub] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [show 2 * (π - θ) = -(2 * θ) + ((1 : ℕ) : ℝ) * (2 * π) by push_cast; ring,
    Real.cos_add_nat_mul_two_pi, Real.cos_neg,
    show b * -Real.cos θ - t = -(b * Real.cos θ - -t) by ring, Real.log_neg_eq_log]

/-- `δ = 1`: `π log(b/2) - (π/2)(2t²/b² - 1) ≤ ∫ log|b cos θ - t| (1 + cos 2θ)` for `t ≥ 0`. -/
theorem integral_log_mul_cos_sub_weight_one_ge {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    π * Real.log (b / 2) - (π / 2) * (2 * t ^ 2 / b ^ 2 - 1) ≤
      ∫ θ in (0 : ℝ)..π, Real.log (b * Real.cos θ - t) * (1 + 1 * Real.cos (2 * θ)) := by
  rcases le_or_gt t b with htb | hbt
  · rw [integral_log_mul_cos_sub_weight_of_abs_le hb (by rwa [abs_of_nonneg ht]) 1]
    exact le_of_eq (by ring)
  · have hmono := integral_log_mul_cos_sub_weight_mono hb le_rfl hbt.le (δ := 1) (by norm_num)
    rw [integral_log_mul_cos_sub_weight_of_abs_le hb (by rw [abs_of_pos hb]) 1] at hmono
    have : 1 ≤ 2 * t ^ 2 / b ^ 2 - 1 := by
      rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]; nlinarith
    have hb2 : 2 * b ^ 2 / b ^ 2 - 1 = 1 := by field_simp; norm_num
    rw [hb2] at hmono
    nlinarith [Real.pi_pos]

/-- `δ = -1`: the lower bound loses `(π/b²) max(t² - b², 0)` off the support. -/
theorem integral_log_mul_cos_sub_weight_neg_one_ge {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    π * Real.log (b / 2) + (π / 2) * (2 * t ^ 2 / b ^ 2 - 1) - π / b ^ 2 * max (t ^ 2 - b ^ 2) 0 ≤
      ∫ θ in (0 : ℝ)..π, Real.log (b * Real.cos θ - t) * (1 + -1 * Real.cos (2 * θ)) := by
  rcases le_or_gt t b with htb | hbt
  · rw [integral_log_mul_cos_sub_weight_of_abs_le hb (by rwa [abs_of_nonneg ht]) (-1),
      max_eq_right (by nlinarith)]
    exact le_of_eq (by ring)
  · have hmono := integral_log_mul_cos_sub_weight_mono hb le_rfl hbt.le (δ := -1) (by norm_num)
    rw [integral_log_mul_cos_sub_weight_of_abs_le hb (by rw [abs_of_pos hb]) (-1)] at hmono
    rw [max_eq_left (by nlinarith)]
    have hb2 : (2 * b ^ 2 / b ^ 2 - 1) = 1 := by field_simp; norm_num
    rw [hb2] at hmono
    have e : π * Real.log (b / 2) + (π / 2) * (2 * t ^ 2 / b ^ 2 - 1) - π / b ^ 2 * (t ^ 2 - b ^ 2) =
        π * Real.log (b / 2) - -1 * (π / 2) * 1 := by
      field_simp; ring
    rw [e]; exact hmono

/-- `δ = 0`: `π log(b/2) + π max(log(t/b), 0) ≤ ∫_0^π log|b cos θ - t| dθ` for `t ≥ 0`. -/
theorem integral_log_mul_cos_sub_ge_excess {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    π * Real.log (b / 2) + π * max (Real.log (t / b)) 0 ≤
      ∫ θ in (0 : ℝ)..π, Real.log (b * Real.cos θ - t) * (1 + 0 * Real.cos (2 * θ)) := by
  simp only [zero_mul, add_zero, mul_one]
  rcases le_or_gt t b with htb | hbt
  · rw [integral_log_mul_cos_sub_of_abs_le hb (by rwa [abs_of_nonneg ht])]
    rw [max_eq_right (Real.log_nonpos (div_nonneg ht hb.le) (by rwa [div_le_one hb]))]
    exact le_of_eq (by ring)
  · have htpos : 0 < t := hb.trans hbt
    rw [integral_log_mul_cos_sub_of_lt_abs hb (by rwa [abs_of_pos htpos]), abs_of_pos htpos,
      max_eq_left (Real.log_nonneg (by rw [le_div_iff₀ hb]; linarith))]
    have hle : Real.log (t / 2) ≤ Real.log ((t + Real.sqrt (t ^ 2 - b ^ 2)) / 2) :=
      Real.log_le_log (by positivity) (by linarith [Real.sqrt_nonneg (t ^ 2 - b ^ 2)])
    rw [Real.log_div htpos.ne' two_ne_zero] at hle
    rw [Real.log_div hb.ne' two_ne_zero, Real.log_div htpos.ne' hb.ne']
    nlinarith [Real.pi_pos]

/-- `max(t² - b², 0) ≤ 2 max(log(t/b), 0)` for `0 ≤ t ≤ 1`. -/
theorem max_sq_sub_le_two_mul_max_log {b t : ℝ} (hb : 0 < b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    max (t ^ 2 - b ^ 2) 0 ≤ 2 * max (Real.log (t / b)) 0 := by
  rcases le_or_gt t b with htb | hbt
  · rw [max_eq_right (by nlinarith)]; positivity
  · have htpos : 0 < t := hb.trans hbt
    have hlog := Real.one_sub_inv_le_log_of_pos (div_pos htpos hb)
    rw [inv_div] at hlog
    rw [max_eq_left (by nlinarith), max_eq_left (Real.log_nonneg (by rw [le_div_iff₀ hb]; linarith))]
    have h1 : t - b ≤ t * Real.log (t / b) := by
      have := mul_le_mul_of_nonneg_left hlog htpos.le
      rwa [mul_sub, mul_one, mul_div_cancel₀ _ htpos.ne'] at this
    have h2 : t * Real.log (t / b) ≤ Real.log (t / b) := by
      have hl : 0 ≤ Real.log (t / b) := Real.log_nonneg (by rw [le_div_iff₀ hb]; linarith)
      nlinarith
    nlinarith

/-! ### The weighted Jensen inequality -/

theorem intervalIntegrable_jensenIntegrand (m : ℕ) (s : Finset ℝ) {b : ℝ}
    (hb : b ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun θ => jensenIntegrand m s b θ) volume 0 π := by
  have hW : ∀ θ, 0 < 1 - b * |Real.cos θ| := fun θ => by
    have := Real.abs_cos_le_one θ; nlinarith [hb.1, hb.2, abs_nonneg (Real.cos θ)]
  have h1 : IntervalIntegrable (fun θ => (m : ℝ) * Real.log (1 - b * |Real.cos θ|)) volume 0 π :=
    ContinuousOn.intervalIntegrable (continuousOn_const.mul
      (ContinuousOn.log (by fun_prop) fun θ _ => (hW θ).ne'))
  have h2 : IntervalIntegrable (fun θ => ∑ r ∈ s, (Real.log (b * Real.cos θ -
      Real.sqrt (1 - 4 * r)) + Real.log (b * Real.cos θ - -Real.sqrt (1 - 4 * r)) -
        Real.log 4)) volume 0 π := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum s fun r _ =>
      ((intervalIntegrable_log_mul_cos_sub hb.1 _).add
        (intervalIntegrable_log_mul_cos_sub hb.1 _)).sub intervalIntegrable_const
  exact h1.add h2

/-- **The weighted Jensen identity.**  For the weight `1 + δ cos 2θ`,
`∫ J (1 + δ cos 2θ) = m E_δ + Σ_r (2 Φ_δ(t_r) - π log 4)`. -/
theorem integral_jensenIntegrand_mul_weight (m : ℕ) (s : Finset ℝ) {b : ℝ}
    (hb : b ∈ Ioo (0 : ℝ) 1) (δ : ℝ) :
    ∫ θ in (0 : ℝ)..π, jensenIntegrand m s b θ * (1 + δ * Real.cos (2 * θ)) =
      m * (∫ θ in (0 : ℝ)..π, Real.log (1 - b * |Real.cos θ|) * (1 + δ * Real.cos (2 * θ))) +
        ∑ r ∈ s, (2 * (∫ θ in (0 : ℝ)..π, Real.log (b * Real.cos θ - Real.sqrt (1 - 4 * r)) *
          (1 + δ * Real.cos (2 * θ))) - π * Real.log 4) := by
  have hW : ∀ θ, 0 < 1 - b * |Real.cos θ| := fun θ => by
    have := Real.abs_cos_le_one θ; nlinarith [hb.1, hb.2, abs_nonneg (Real.cos θ)]
  have hwc : Continuous fun θ : ℝ => 1 + δ * Real.cos (2 * θ) := by fun_prop
  have hi0 : IntervalIntegrable (fun θ => Real.log (1 - b * |Real.cos θ|) *
      (1 + δ * Real.cos (2 * θ))) volume 0 π :=
    ContinuousOn.intervalIntegrable ((ContinuousOn.log (by fun_prop) fun θ _ => (hW θ).ne').mul
      hwc.continuousOn)
  have hir : ∀ r ∈ s, IntervalIntegrable (fun θ => (Real.log (b * Real.cos θ -
      Real.sqrt (1 - 4 * r)) + Real.log (b * Real.cos θ - -Real.sqrt (1 - 4 * r)) -
        Real.log 4) * (1 + δ * Real.cos (2 * θ))) volume 0 π := fun r _ =>
    (((intervalIntegrable_log_mul_cos_sub hb.1 _).add
      (intervalIntegrable_log_mul_cos_sub hb.1 _)).sub intervalIntegrable_const).mul_continuousOn
        hwc.continuousOn
  have e : ∀ θ, jensenIntegrand m s b θ * (1 + δ * Real.cos (2 * θ)) =
      m * (Real.log (1 - b * |Real.cos θ|) * (1 + δ * Real.cos (2 * θ))) +
        ∑ r ∈ s, (Real.log (b * Real.cos θ - Real.sqrt (1 - 4 * r)) +
          Real.log (b * Real.cos θ - -Real.sqrt (1 - 4 * r)) - Real.log 4) *
            (1 + δ * Real.cos (2 * θ)) := fun θ => by
    rw [jensenIntegrand, add_mul, Finset.sum_mul]; ring
  simp_rw [e]
  have hsumI : IntervalIntegrable (fun θ => ∑ r ∈ s, (Real.log (b * Real.cos θ -
      Real.sqrt (1 - 4 * r)) + Real.log (b * Real.cos θ - -Real.sqrt (1 - 4 * r)) -
        Real.log 4) * (1 + δ * Real.cos (2 * θ))) volume 0 π := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum s hir
  rw [integral_add (hi0.const_mul _) hsumI, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum hir]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  have e2 : ∀ θ, (Real.log (b * Real.cos θ - Real.sqrt (1 - 4 * r)) +
      Real.log (b * Real.cos θ - -Real.sqrt (1 - 4 * r)) - Real.log 4) *
        (1 + δ * Real.cos (2 * θ)) =
      Real.log (b * Real.cos θ - Real.sqrt (1 - 4 * r)) * (1 + δ * Real.cos (2 * θ)) +
        Real.log (b * Real.cos θ - -Real.sqrt (1 - 4 * r)) * (1 + δ * Real.cos (2 * θ)) -
          Real.log 4 * (1 + δ * Real.cos (2 * θ)) := fun θ => by ring
  simp_rw [e2]
  rw [integral_sub ((intervalIntegrable_log_mul_cos_sub_mul hb.1 _ hwc).add
      (intervalIntegrable_log_mul_cos_sub_mul hb.1 _ hwc)) ((hwc.intervalIntegrable 0 π).const_mul _),
    integral_add (intervalIntegrable_log_mul_cos_sub_mul hb.1 _ hwc)
      (intervalIntegrable_log_mul_cos_sub_mul hb.1 _ hwc),
    integral_log_mul_cos_add_weight, intervalIntegral.integral_const_mul,
    integral_one_add_mul_cos_two]
  ring

/-- **The weighted Jensen inequality** `∫ J (1 + δ cos 2θ) ≤ π log ‖T‖_m`, `|δ| ≤ 1`. -/
theorem integral_jensenIntegrand_mul_weight_le {m : ℕ} {T : Polynomial ℝ} {s : Finset ℝ}
    (hroots : ∀ r ∈ s, 0 < r ∧ r < 1 / 4) (hprod : T = ∏ r ∈ s, (X - C r)) {b : ℝ}
    (hb : b ∈ Ioo (0 : ℝ) 1) {δ : ℝ} (hδ : |δ| ≤ 1) :
    ∫ θ in (0 : ℝ)..π, jensenIntegrand m s b θ * (1 + δ * Real.cos (2 * θ)) ≤
      π * Real.log (cubicWeightedIntervalNorm m T) := by
  have hwc : Continuous fun θ : ℝ => 1 + δ * Real.cos (2 * θ) := by fun_prop
  have hle := integral_mono_ae_restrict Real.pi_pos.le
    ((intervalIntegrable_jensenIntegrand m s hb).mul_continuousOn hwc.continuousOn)
    ((hwc.intervalIntegrable 0 π).const_mul (Real.log (cubicWeightedIntervalNorm m T)))
    (ae_restrict_of_ae ((ae_jensenIntegrand_le hroots hprod hb).mono fun θ hθ =>
      mul_le_mul_of_nonneg_right hθ (one_add_mul_cos_two_nonneg hδ θ)))
  rw [intervalIntegral.integral_const_mul, integral_one_add_mul_cos_two] at hle
  linarith

/-! ### The cos 2θ moment of the weight -/

/-- `∫_0^{π/2} log(1 - b cos s) cos 2s ds = -(1/b + π/(2b²) + (1 - 1/b²) I(b) - π/4)`, by parts. -/
theorem integral_log_one_sub_mul_cos_mul_cos_two {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) :
    ∫ s in (0 : ℝ)..π / 2, Real.log (1 - b * Real.cos s) *
      (Real.cos s * Real.cos s - Real.sin s * Real.sin s) =
      -(1 / b + π / (2 * b ^ 2) + (1 - 1 / b ^ 2) * recoveryI b - π / 4) := by
  have hpos : ∀ s, 0 < 1 - b * Real.cos s := fun s => by
    have := Real.cos_le_one s; nlinarith [hb.1, hb.2, Real.neg_one_le_cos s]
  have hu : ∀ x ∈ uIcc (0 : ℝ) (π / 2), HasDerivAt (fun s => Real.log (1 - b * Real.cos s))
      (b * Real.sin x / (1 - b * Real.cos x)) x := fun x _ => by
    have := (((Real.hasDerivAt_cos x).const_mul b).const_sub 1).log (hpos x).ne'
    refine this.congr_deriv ?_; ring
  have hv : ∀ x ∈ uIcc (0 : ℝ) (π / 2), HasDerivAt (fun s => Real.sin s * Real.cos s)
      (Real.cos x * Real.cos x - Real.sin x * Real.sin x) x := fun x _ => by
    have := (Real.hasDerivAt_sin x).mul (Real.hasDerivAt_cos x)
    refine this.congr_deriv ?_; ring
  have hu' : IntervalIntegrable (fun s => b * Real.sin s / (1 - b * Real.cos s)) volume 0 (π / 2) :=
    ContinuousOn.intervalIntegrable (ContinuousOn.div (by fun_prop) (by fun_prop)
      fun s _ => (hpos s).ne')
  have hv' : IntervalIntegrable (fun s => Real.cos s * Real.cos s - Real.sin s * Real.sin s)
      volume 0 (π / 2) := (by fun_prop : Continuous fun s =>
        Real.cos s * Real.cos s - Real.sin s * Real.sin s).intervalIntegrable _ _
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv']
  simp only [Real.cos_pi_div_two, Real.sin_zero, mul_zero, zero_mul, sub_zero]
  have hpt : ∀ s, b * Real.sin s / (1 - b * Real.cos s) * (Real.sin s * Real.cos s) =
      Real.cos s / b + 1 / b ^ 2 + (1 - 1 / b ^ 2) * (1 / (1 - b * Real.cos s)) -
        Real.sin s ^ 2 := fun s => by
    have hb0 := hb.1.ne'
    have := (hpos s).ne'
    have hsc := Real.sin_sq_add_cos_sq s
    field_simp
    linear_combination b ^ 2 * hsc
  simp_rw [hpt]
  have hI : IntervalIntegrable (fun s => 1 / (1 - b * Real.cos s)) volume 0 (π / 2) :=
    ContinuousOn.intervalIntegrable (ContinuousOn.div continuousOn_const (by fun_prop)
      fun s _ => (hpos s).ne')
  rw [integral_sub (((((by fun_prop : Continuous fun s => Real.cos s / b).intervalIntegrable _ _).add
      intervalIntegrable_const)).add (hI.const_mul _))
      ((by fun_prop : Continuous fun s => Real.sin s ^ 2).intervalIntegrable _ _),
    integral_add ((((by fun_prop : Continuous fun s => Real.cos s / b).intervalIntegrable _ _).add
      intervalIntegrable_const)) (hI.const_mul _),
    integral_add ((by fun_prop : Continuous fun s => Real.cos s / b).intervalIntegrable _ _)
      intervalIntegrable_const, intervalIntegral.integral_div, integral_cos,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_sin_sq]
  simp only [Real.sin_pi_div_two, Real.sin_zero, Real.cos_pi_div_two, Real.cos_zero, smul_eq_mul]
  rw [← recoveryI]
  ring

/-- **`E₂ = ∫_0^π log(1 - b|cos θ|) cos 2θ dθ = 2(π/b² - 1/b - 5π/4)`** at the recovery edge. -/
theorem integral_log_one_sub_edge_abs_cos_mul_cos_two :
    ∫ θ in (0 : ℝ)..π, Real.log (1 - recoveryEdge * |Real.cos θ|) * Real.cos (2 * θ) =
      2 * (π / recoveryEdge ^ 2 - 1 / recoveryEdge - 5 * π / 4) := by
  have hb := recoveryEdge_mem
  set b := recoveryEdge with hbdef
  have hf : ContinuousOn (fun y => Real.log (1 - b * y) * (2 * y ^ 2 - 1)) (Icc 0 1) :=
    (ContinuousOn.log (by fun_prop) fun y hy => by nlinarith [hb.1, hb.2, hy.1, hy.2]).mul
      (by fun_prop)
  have e : ∀ θ, Real.log (1 - b * |Real.cos θ|) * Real.cos (2 * θ) =
      Real.log (1 - b * |Real.cos θ|) * (2 * |Real.cos θ| ^ 2 - 1) := fun θ => by
    rw [sq_abs, Real.cos_two_mul]
  simp_rw [e]
  rw [integral_abs_cos_symm _ hf]
  have e2 : ∀ s, Real.log (1 - b * Real.cos s) * (2 * Real.cos s ^ 2 - 1) =
      Real.log (1 - b * Real.cos s) * (Real.cos s * Real.cos s - Real.sin s * Real.sin s) :=
    fun s => by
      have := Real.sin_sq_add_cos_sq s
      congr 1; nlinarith
  simp_rw [e2]
  rw [integral_log_one_sub_mul_cos_mul_cos_two hb, recoveryI_edge]
  have hb0 := hb.1.ne'
  field_simp
  ring

/-! ### The mean root location -/

/-- **The two-sided root estimate.**  For `T = ∏_{r ∈ s} (X - r)` with `m` roots in `(0, 1/4)`,
`|m E₂ - π Σ (2(1-4r)/b² - 1)| ≤ (π + 2π/b²)(log ‖T‖_m - m log ρ)`. -/
theorem abs_rootMoment_sub_le {m : ℕ} {T : Polynomial ℝ} {s : Finset ℝ} (hcard : s.card = m) (hroots : ∀ r ∈ s, 0 < r ∧ r < 1 / 4)
    (hprod : T = ∏ r ∈ s, (X - C r)) :
    |m * (∫ θ in (0 : ℝ)..π, Real.log (1 - recoveryEdge * |Real.cos θ|) * Real.cos (2 * θ)) -
      π * ∑ r ∈ s, (2 * (1 - 4 * r) / recoveryEdge ^ 2 - 1)| ≤
      (π + 2 * π / recoveryEdge ^ 2) *
        (Real.log (cubicWeightedIntervalNorm m T) - m * Real.log recoveryRate) := by
  have hb := recoveryEdge_mem
  set b := recoveryEdge with hbdef
  set tm := cubicWeightedIntervalNorm m T with htm
  set E₂ := ∫ θ in (0 : ℝ)..π, Real.log (1 - b * |Real.cos θ|) * Real.cos (2 * θ) with hE₂
  set E₀ := ∫ θ in (0 : ℝ)..π, Real.log (1 - b * |Real.cos θ|) with hE₀
  have hW : ∀ θ, 0 < 1 - b * |Real.cos θ| := fun θ => by
    have := Real.abs_cos_le_one θ; nlinarith [hb.1, hb.2, abs_nonneg (Real.cos θ)]
  have hEδ : ∀ δ : ℝ, ∫ θ in (0 : ℝ)..π, Real.log (1 - b * |Real.cos θ|) *
      (1 + δ * Real.cos (2 * θ)) = E₀ + δ * E₂ := fun δ => by
    have hc0 : Continuous fun θ => Real.log (1 - b * |Real.cos θ|) :=
      Continuous.log (by fun_prop) fun θ => (hW θ).ne'
    have e : ∀ θ, Real.log (1 - b * |Real.cos θ|) * (1 + δ * Real.cos (2 * θ)) =
        Real.log (1 - b * |Real.cos θ|) + δ * (Real.log (1 - b * |Real.cos θ|) *
          Real.cos (2 * θ)) := fun θ => by ring
    simp_rw [e]
    have hi0 : IntervalIntegrable (fun θ => Real.log (1 - b * |Real.cos θ|)) volume 0 π :=
      hc0.intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun θ => Real.log (1 - b * |Real.cos θ|) * Real.cos (2 * θ))
        volume 0 π := (hc0.mul (by fun_prop)).intervalIntegrable _ _
    rw [integral_add hi0 (hi2.const_mul _), intervalIntegral.integral_const_mul]
  -- `π log ρ = E₀ + 2π log(b/2) - π log 4`
  have hρ : π * Real.log recoveryRate = E₀ + 2 * π * Real.log (b / 2) - π * Real.log 4 := by
    have hsymm := integral_abs_cos_symm (fun y => Real.log (1 - b * y))
      (ContinuousOn.log (by fun_prop) fun y hy => by nlinarith [hb.1, hb.2, hy.1, hy.2])
    rw [recoveryRate, recoveryRateFun, Real.log_mul (by have := hb.1; positivity)
      (Real.exp_pos _).ne', Real.log_exp, hE₀, hsymm,
      show b ^ 2 / 16 = (b / 2) ^ 2 / 4 by ring, Real.log_div (by have := hb.1; positivity)
        (by norm_num), Real.log_pow]
    have := Real.pi_pos.ne'
    field_simp
    ring
  have hJ := fun δ (hδ : |δ| ≤ 1) => integral_jensenIntegrand_mul_weight_le (m := m) hroots hprod
    hb hδ
  have hId := fun δ => integral_jensenIntegrand_mul_weight m s hb δ
  set t : ℝ → ℝ := fun r => Real.sqrt (1 - 4 * r) with ht
  have ht0 : ∀ r ∈ s, 0 ≤ t r := fun r _ => Real.sqrt_nonneg _
  have ht1 : ∀ r ∈ s, t r ≤ 1 := fun r hr =>
    Real.sqrt_le_one.mpr (by linarith [(hroots r hr).1])
  have ht2 : ∀ r ∈ s, t r ^ 2 = 1 - 4 * r := fun r hr =>
    Real.sq_sqrt (by linarith [(hroots r hr).2])
  set Δ := Real.log tm - m * Real.log recoveryRate with hΔ
  have hρm : (m : ℝ) * (π * Real.log recoveryRate) =
      m * (E₀ + 2 * π * Real.log (b / 2) - π * Real.log 4) := by rw [hρ]
  have hπΔ : π * Δ = π * Real.log tm - m * (π * Real.log recoveryRate) := by rw [hΔ]; ring
  have hmc : ∀ c : ℝ, (m : ℝ) * c = ∑ _r ∈ s, c := fun c => by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
  -- `δ = 0`: the excess of the roots outside `[-b, b]`
  have h0 : ∑ r ∈ s, max (t r ^ 2 - b ^ 2) 0 ≤ Δ := by
    have hj := hJ 0 (by norm_num)
    rw [hId 0, hEδ 0] at hj
    have hsum : ∑ r ∈ s, (2 * (π * Real.log (b / 2) + π * max (Real.log (t r / b)) 0) -
        π * Real.log 4) ≤ ∑ r ∈ s, (2 * (∫ θ in (0 : ℝ)..π, Real.log (b * Real.cos θ - t r) *
          (1 + 0 * Real.cos (2 * θ))) - π * Real.log 4) :=
      Finset.sum_le_sum fun r hr => sub_le_sub_right (mul_le_mul_of_nonneg_left
        (integral_log_mul_cos_sub_ge_excess hb.1 (ht0 r hr)) zero_le_two) _
    have hexc : ∑ r ∈ s, max (t r ^ 2 - b ^ 2) 0 ≤ 2 * ∑ r ∈ s, max (Real.log (t r / b)) 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun r hr =>
        max_sq_sub_le_two_mul_max_log hb.1 (ht0 r hr) (ht1 r hr)
    have hexp : ∑ r ∈ s, (2 * (π * Real.log (b / 2) + π * max (Real.log (t r / b)) 0) -
        π * Real.log 4) = m * (2 * π * Real.log (b / 2) - π * Real.log 4) +
          π * (2 * ∑ r ∈ s, max (Real.log (t r / b)) 0) := by
      rw [hmc, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [hexp] at hsum
    have key : π * (2 * ∑ r ∈ s, max (Real.log (t r / b)) 0) ≤ π * Δ := by
      rw [hπΔ]; linarith
    have := le_of_mul_le_mul_left key Real.pi_pos
    linarith
  have hΔ0 : 0 ≤ Δ := le_trans (Finset.sum_nonneg fun r _ => le_max_right _ _) h0
  -- `δ = 1`
  have h1 : m * E₂ - π * ∑ r ∈ s, (2 * (1 - 4 * r) / b ^ 2 - 1) ≤ π * Δ := by
    have hj := hJ 1 (by norm_num)
    rw [hId 1, hEδ 1] at hj
    have hsum : ∑ r ∈ s, (2 * (π * Real.log (b / 2) - (π / 2) * (2 * t r ^ 2 / b ^ 2 - 1)) -
        π * Real.log 4) ≤ ∑ r ∈ s, (2 * (∫ θ in (0 : ℝ)..π, Real.log (b * Real.cos θ - t r) *
          (1 + 1 * Real.cos (2 * θ))) - π * Real.log 4) :=
      Finset.sum_le_sum fun r hr => sub_le_sub_right (mul_le_mul_of_nonneg_left
        (integral_log_mul_cos_sub_weight_one_ge hb.1 (ht0 r hr)) zero_le_two) _
    have hexp : ∑ r ∈ s, (2 * (π * Real.log (b / 2) - (π / 2) * (2 * t r ^ 2 / b ^ 2 - 1)) -
        π * Real.log 4) = m * (2 * π * Real.log (b / 2) - π * Real.log 4) -
          π * ∑ r ∈ s, (2 * (1 - 4 * r) / b ^ 2 - 1) := by
      rw [hmc, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun r hr => by rw [ht2 r hr]; ring
    rw [hexp] at hsum
    rw [hπΔ]; linarith
  -- `δ = -1`
  have h2 : π * ∑ r ∈ s, (2 * (1 - 4 * r) / b ^ 2 - 1) - m * E₂ ≤ π * Δ + 2 * π / b ^ 2 * Δ := by
    have hj := hJ (-1) (by norm_num)
    rw [hId (-1), hEδ (-1)] at hj
    have hsum : ∑ r ∈ s, (2 * (π * Real.log (b / 2) + (π / 2) * (2 * t r ^ 2 / b ^ 2 - 1) -
        π / b ^ 2 * max (t r ^ 2 - b ^ 2) 0) - π * Real.log 4) ≤
        ∑ r ∈ s, (2 * (∫ θ in (0 : ℝ)..π, Real.log (b * Real.cos θ - t r) *
          (1 + -1 * Real.cos (2 * θ))) - π * Real.log 4) :=
      Finset.sum_le_sum fun r hr => sub_le_sub_right (mul_le_mul_of_nonneg_left
        (integral_log_mul_cos_sub_weight_neg_one_ge hb.1 (ht0 r hr)) zero_le_two) _
    have hexp : ∑ r ∈ s, (2 * (π * Real.log (b / 2) + (π / 2) * (2 * t r ^ 2 / b ^ 2 - 1) -
        π / b ^ 2 * max (t r ^ 2 - b ^ 2) 0) - π * Real.log 4) =
        m * (2 * π * Real.log (b / 2) - π * Real.log 4) +
          π * ∑ r ∈ s, (2 * (1 - 4 * r) / b ^ 2 - 1) -
            2 * π / b ^ 2 * ∑ r ∈ s, max (t r ^ 2 - b ^ 2) 0 := by
      rw [hmc, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun r hr => by rw [ht2 r hr]; ring
    rw [hexp] at hsum
    have hb2 : 0 < 2 * π / b ^ 2 := by have := hb.1; positivity
    have := mul_le_mul_of_nonneg_left h0 hb2.le
    rw [hπΔ]; linarith
  have hb2 : 0 ≤ 2 * π / b ^ 2 * Δ := mul_nonneg (by have := hb.1; positivity) hΔ0
  have hK : (π + 2 * π / b ^ 2) * Δ = π * Δ + 2 * π / b ^ 2 * Δ := by ring
  rw [abs_le, hK]
  constructor <;> linarith

/-- **The mean root location** `S_m/m → b/(4π) + 3b²/16`. -/
theorem tendsto_rootSum_div {T : ℕ → Polynomial ℝ} {s : ℕ → Finset ℝ}
    (hT : ∀ m, IsCubicChebyshev m (T m)) (hcard : ∀ m, (s m).card = m)
    (hroots : ∀ m, ∀ r ∈ s m, 0 < r ∧ r < 1 / 4) (hprod : ∀ m, T m = ∏ r ∈ s m, (X - C r)) :
    Tendsto (fun m : ℕ => (∑ r ∈ s m, r) / m) atTop
      (𝓝 (recoveryEdge / (4 * π) + 3 * recoveryEdge ^ 2 / 16)) := by
  have hb := recoveryEdge_mem
  have hE₂ := integral_log_one_sub_edge_abs_cos_mul_cos_two
  set b := recoveryEdge with hbdef
  set K := π + 2 * π / b ^ 2 with hK
  -- `(log t_m - m log ρ)/m → 0`
  have hΔ : Tendsto (fun m : ℕ => (Real.log (cubicWeightedIntervalNorm m (T m)) -
      m * Real.log recoveryRate) / m) atTop (𝓝 0) := by
    have h := (tendsto_log_cubicChebyshev_norm hT).sub_const (Real.log recoveryRate)
    rw [sub_self] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hm)
    field_simp
  set c := b / (4 * π) + 3 * b ^ 2 / 16 with hc
  -- the root estimate, rearranged
  have hbound : ∀ m : ℕ, 1 ≤ m → |(∑ r ∈ s m, r) / m - c| ≤
      b ^ 2 / (8 * π) * K * ((Real.log (cubicWeightedIntervalNorm m (T m)) -
        m * Real.log recoveryRate) / m) := by
    intro m hm
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have h := abs_rootMoment_sub_le (hcard m) (hroots m) (hprod m)
    have hsum : ∑ r ∈ s m, (2 * (1 - 4 * r) / b ^ 2 - 1) =
        (2 / b ^ 2 - 1) * m - 8 / b ^ 2 * ∑ r ∈ s m, r := by
      have hc : (2 / b ^ 2 - 1) * (m : ℝ) = ∑ _r ∈ s m, (2 / b ^ 2 - 1) := by
        rw [Finset.sum_const, hcard m, nsmul_eq_mul]; ring
      rw [Finset.mul_sum, hc, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [hsum, hE₂] at h
    have hb0 := hb.1.ne'
    have hπ := Real.pi_pos
    have key : (∑ r ∈ s m, r) / m - c = b ^ 2 / (8 * π) / m *
        (m * (2 * (π / b ^ 2 - 1 / b - 5 * π / 4)) - π * ((2 / b ^ 2 - 1) * m -
          8 / b ^ 2 * ∑ r ∈ s m, r)) := by
      rw [hc]; field_simp; ring
    rw [key, abs_mul, abs_of_pos (by positivity : 0 < b ^ 2 / (8 * π) / m)]
    calc b ^ 2 / (8 * π) / m * |m * (2 * (π / b ^ 2 - 1 / b - 5 * π / 4)) -
          π * ((2 / b ^ 2 - 1) * m - 8 / b ^ 2 * ∑ r ∈ s m, r)|
        ≤ b ^ 2 / (8 * π) / m * (K * (Real.log (cubicWeightedIntervalNorm m (T m)) -
          m * Real.log recoveryRate)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = b ^ 2 / (8 * π) * K * ((Real.log (cubicWeightedIntervalNorm m (T m)) -
          m * Real.log recoveryRate) / m) := by ring
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlim := (hΔ.const_mul (b ^ 2 / (8 * π) * K))
  rw [mul_zero, Metric.tendsto_atTop] at hlim
  obtain ⟨N, hN⟩ := hlim ε hε
  refine ⟨max N 1, fun m hm => ?_⟩
  have hNm := hN m (le_of_max_le_left hm)
  rw [Real.dist_eq, sub_zero] at hNm
  rw [Real.dist_eq]
  exact lt_of_le_of_lt ((hbound m (le_of_max_le_right hm)).trans (le_abs_self _)) hNm

end GaloisForLFunctions.HTGeometry.ChronologicalTensor
