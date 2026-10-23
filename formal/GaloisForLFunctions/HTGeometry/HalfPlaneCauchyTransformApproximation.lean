import GaloisForLFunctions.HTGeometry.HalfPlanePoleApproximation

/-!
# Entire approximation of a Cauchy transform on a closed half plane

The truncated Laplace approximant of a single simple pole is upgraded here to an arbitrary
superposition of Cauchy kernels.  If a complex measure `φ dμ` is carried by the closed half plane
`Re w ≤ 1 - δ`, its Cauchy transform

```text
s ↦ ∫ φ(x) / (s - w x) dμ(x)
```

is uniformly approximable on the *closed, unbounded* half plane `Re s ≥ 1` by entire functions,
with an error that decays exponentially in the truncation parameter.

The approximant is the same truncated Laplace transform integrated against `φ dμ`.  Its entirety
comes from differentiation under the integral sign; the uniform bound comes from the fact that the
kernel `truncPole a T` is uniformly bounded on `Re s ≥ 1` once `Re a ≤ 1 - δ`, with a bound
depending only on `T` and on a lower bound for `Re (s - a)`.

This is the analytic engine behind uniform approximation on a closed half plane: every function
that can be written as a superposition of Cauchy kernels carried strictly to the left of the line
is a uniform limit of entire functions on the closed half plane.
-/

noncomputable section

open Complex MeasureTheory Metric

namespace GaloisForLFunctions.HTGeometry

/-! ### The kernel depends only on the difference -/

/-- The truncated Laplace kernel depends only on `s - a`. -/
theorem truncPole_eq_shift (a : ℂ) (T : ℝ) (s : ℂ) :
    truncPole a T s = truncPole 0 T (s - a) := by
  rcases eq_or_ne s a with rfl | h
  · rw [truncPole_self, sub_self, truncPole_self]
  · have h0 : s - a ≠ 0 := sub_ne_zero.mpr h
    rw [truncPole_of_ne h, truncPole_of_ne h0, sub_zero]

/-- The truncated Laplace kernel is the Laplace transform of the constant density on `[0,T]`. -/
theorem truncPole_zero_eq_intervalIntegral (T : ℝ) (z : ℂ) :
    truncPole 0 T z = ∫ t in (0:ℝ)..T, Complex.exp (-(t : ℂ) * z) := by
  rcases eq_or_ne z 0 with rfl | h
  · simp [truncPole_self]
  · have hz : -z ≠ 0 := neg_ne_zero.mpr h
    have hcongr : (∫ t in (0:ℝ)..T, Complex.exp (-(t : ℂ) * z))
        = ∫ t in (0:ℝ)..T, Complex.exp (-z * (t : ℂ)) := by
      refine intervalIntegral.integral_congr ?_
      intro t _
      ring_nf
    rw [truncPole_of_ne h, sub_zero, hcongr, integral_exp_mul_complex hz]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    have hTz : (-(T : ℂ)) * z = -z * (T : ℂ) := by ring
    rw [hTz]
    field_simp
    ring

/-! ### Uniform bounds on the kernel and its derivative -/

private theorem norm_exp_neg_mul_le (t : ℝ) (z : ℂ) :
    ‖Complex.exp (-(t : ℂ) * z)‖ = Real.exp (-(t * z.re)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- The truncated Laplace kernel is bounded by `T e^{T max(0, -Re z)}`. -/
theorem norm_truncPole_zero_le {T : ℝ} (hT : 0 ≤ T) (z : ℂ) :
    ‖truncPole 0 T z‖ ≤ T * Real.exp (T * max 0 (-z.re)) := by
  rw [truncPole_zero_eq_intervalIntegral]
  have hbound : ∀ t ∈ Set.uIoc (0:ℝ) T,
      ‖Complex.exp (-(t : ℂ) * z)‖ ≤ Real.exp (T * max 0 (-z.re)) := by
    intro t ht
    rw [Set.uIoc_of_le hT] at ht
    have ht0 : 0 ≤ t := le_of_lt ht.1
    rw [norm_exp_neg_mul_le]
    refine Real.exp_le_exp.mpr ?_
    have h1 : -(t * z.re) = t * (-z.re) := by ring
    rw [h1]
    have h2 : t * (-z.re) ≤ t * max 0 (-z.re) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) ht0
    refine h2.trans ?_
    exact mul_le_mul_of_nonneg_right ht.2 (le_max_left _ _)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [sub_zero, abs_of_nonneg hT] at this
  linarith [this]

/-- The derivative of the truncated Laplace kernel, as a Laplace transform. -/
theorem hasDerivAt_truncPole_zero (T : ℝ) (z : ℂ) :
    HasDerivAt (truncPole 0 T)
      (∫ t in (0:ℝ)..T, (-(t : ℂ)) * Complex.exp (-(t : ℂ) * z)) z := by
  have hcont : ∀ x : ℂ, Continuous fun t : ℝ => Complex.exp (-(t : ℂ) * x) := by
    intro x; fun_prop
  have hcont' : ∀ x : ℂ, Continuous fun t : ℝ => (-(t : ℂ)) * Complex.exp (-(t : ℂ) * x) := by
    intro x; fun_prop
  have hboundcont : Continuous fun t : ℝ => |t| * Real.exp (|t| * (|z.re| + 1)) := by fun_prop
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (x : ℂ) (t : ℝ) => Complex.exp (-(t : ℂ) * x))
    (F' := fun (x : ℂ) (t : ℝ) => (-(t : ℂ)) * Complex.exp (-(t : ℂ) * x))
    (bound := fun t : ℝ => |t| * Real.exp (|t| * (|z.re| + 1)))
    (x₀ := z) (s := Metric.ball z 1) (a := 0) (b := T) (μ := volume)
    (ball_mem_nhds z one_pos)
    (Filter.Eventually.of_forall fun x => (hcont x).aestronglyMeasurable)
    ((hcont z).intervalIntegrable _ _)
    ((hcont' z).aestronglyMeasurable)
    (Filter.Eventually.of_forall ?_)
    (hboundcont.intervalIntegrable _ _)
    (Filter.Eventually.of_forall ?_)
  · have heq : (fun x : ℂ => ∫ t in (0:ℝ)..T, Complex.exp (-(t : ℂ) * x)) = truncPole 0 T := by
      funext x
      exact (truncPole_zero_eq_intervalIntegral T x).symm
    rw [heq] at key
    exact key.2
  · intro t _ x hx
    have hre : |x.re| ≤ |z.re| + 1 := by
      have h1 : |x.re - z.re| ≤ ‖x - z‖ := by
        simpa using Complex.abs_re_le_norm (x - z)
      have h2 : ‖x - z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hx
      have h3 : |x.re| - |z.re| ≤ |x.re - z.re| := abs_sub_abs_le_abs_sub x.re z.re
      linarith
    have hnorm : ‖(-(t : ℂ)) * Complex.exp (-(t : ℂ) * x)‖
        = |t| * Real.exp (-(t * x.re)) := by
      rw [norm_mul, Complex.norm_exp]
      congr 1
      · simp
      · congr 1
        simp [Complex.mul_re]
    rw [hnorm]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg t)
    refine Real.exp_le_exp.mpr ?_
    calc -(t * x.re) ≤ |t * x.re| := neg_le_abs _
      _ = |t| * |x.re| := abs_mul _ _
      _ ≤ |t| * (|z.re| + 1) := mul_le_mul_of_nonneg_left hre (abs_nonneg t)
  · intro t _ x _
    have h1 : HasDerivAt (fun y : ℂ => -(t : ℂ) * y) (-(t : ℂ)) x := by
      simpa using (hasDerivAt_id x).const_mul (-(t : ℂ))
    have h2 := h1.cexp
    simpa [mul_comm] using h2

theorem deriv_truncPole_zero (T : ℝ) (z : ℂ) :
    deriv (truncPole 0 T) z = ∫ t in (0:ℝ)..T, (-(t : ℂ)) * Complex.exp (-(t : ℂ) * z) :=
  (hasDerivAt_truncPole_zero T z).deriv

/-- The derivative of the truncated Laplace kernel is bounded by `T² e^{T max(0, -Re z)}`. -/
theorem norm_deriv_truncPole_zero_le {T : ℝ} (hT : 0 ≤ T) (z : ℂ) :
    ‖deriv (truncPole 0 T) z‖ ≤ T * (T * Real.exp (T * max 0 (-z.re))) := by
  rw [deriv_truncPole_zero]
  have hbound : ∀ t ∈ Set.uIoc (0:ℝ) T,
      ‖(-(t : ℂ)) * Complex.exp (-(t : ℂ) * z)‖ ≤ T * Real.exp (T * max 0 (-z.re)) := by
    intro t ht
    rw [Set.uIoc_of_le hT] at ht
    have ht0 : 0 ≤ t := le_of_lt ht.1
    have hnorm : ‖(-(t : ℂ)) * Complex.exp (-(t : ℂ) * z)‖ = t * Real.exp (-(t * z.re)) := by
      rw [norm_mul, norm_exp_neg_mul_le]
      congr 1
      simp [abs_of_nonneg ht0]
    rw [hnorm]
    refine mul_le_mul ht.2 (Real.exp_le_exp.mpr ?_) (Real.exp_nonneg _) (le_trans ht0 ht.2)
    have h1 : -(t * z.re) = t * (-z.re) := by ring
    rw [h1]
    refine le_trans (mul_le_mul_of_nonneg_left (le_max_right 0 (-z.re)) ht0) ?_
    exact mul_le_mul_of_nonneg_right ht.2 (le_max_left _ _)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [sub_zero, abs_of_nonneg hT] at this
  calc ‖∫ t in (0:ℝ)..T, (-(t : ℂ)) * Complex.exp (-(t : ℂ) * z)‖
      ≤ T * Real.exp (T * max 0 (-z.re)) * T := this
    _ = T * (T * Real.exp (T * max 0 (-z.re))) := by ring

/-- The shifted kernel and its derivative. -/
theorem hasDerivAt_truncPole (a : ℂ) (T : ℝ) (s : ℂ) :
    HasDerivAt (truncPole a T) (deriv (truncPole 0 T) (s - a)) s := by
  have h : HasDerivAt (fun z : ℂ => z - a) 1 s := (hasDerivAt_id s).sub_const a
  have := (hasDerivAt_truncPole_zero T (s - a)).comp s h
  rw [deriv_truncPole_zero]
  have heq : (truncPole 0 T ∘ fun z : ℂ => z - a) = truncPole a T := by
    funext z
    exact (truncPole_eq_shift a T z).symm
  rw [heq] at this
  simpa using this

/-! ### Entire approximation of a Cauchy transform -/

variable {α : Type*} [MeasurableSpace α]

/-- The truncated Cauchy transform of a measure carried by a left half plane is entire. -/
theorem differentiable_truncCauchyTransform (μ : Measure α) {w : α → ℂ} {φ : α → ℂ} {C : ℝ}
    (hw : ∀ x, (w x).re ≤ C) (hwm : Measurable w) (hφ : Integrable φ μ) {T : ℝ} (hT : 0 ≤ T) :
    Differentiable ℂ fun s => ∫ x, φ x * truncPole (w x) T s ∂μ := by
  intro s₀
  set K : ℝ := T * Real.exp (T * max 0 (C - s₀.re + 1)) with hK
  have hKnonneg : 0 ≤ K := mul_nonneg hT (Real.exp_nonneg _)
  have hmeasker : ∀ z : ℂ, Measurable fun x => truncPole (w x) T z := by
    intro z
    have heq : (fun x => truncPole (w x) T z) = fun x => truncPole 0 T (z - w x) := by
      funext x
      exact truncPole_eq_shift (w x) T z
    rw [heq]
    exact ((differentiable_truncPole 0 T).continuous.measurable).comp
      (measurable_const.sub hwm)
  have hmeasderiv : ∀ z : ℂ, Measurable fun x => deriv (truncPole 0 T) (z - w x) := by
    intro z
    exact (((differentiable_truncPole 0 T).deriv).continuous.measurable).comp
      (measurable_const.sub hwm)
  have hballre : ∀ z ∈ Metric.ball s₀ (1:ℝ), s₀.re - 1 ≤ z.re := by
    intro z hz
    have h2 : ‖z - s₀‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have h1 : |(z - s₀).re| ≤ ‖z - s₀‖ := by simpa using Complex.abs_re_le_norm (z - s₀)
    have h3 : |z.re - s₀.re| ≤ ‖z - s₀‖ := by simpa [Complex.sub_re] using h1
    have h4 := abs_le.mp (h3.trans h2.le)
    linarith [h4.1]
  have hmaxle : ∀ z ∈ Metric.ball s₀ (1:ℝ), ∀ x,
      max 0 (-(z - w x).re) ≤ max 0 (C - s₀.re + 1) := by
    intro z hz x
    refine max_le_max le_rfl ?_
    have : -(z - w x).re = (w x).re - z.re := by simp [Complex.sub_re]
    rw [this]
    linarith [hw x, hballre z hz]
  have hkerbound : ∀ z ∈ Metric.ball s₀ (1:ℝ), ∀ x, ‖truncPole (w x) T z‖ ≤ K := by
    intro z hz x
    rw [truncPole_eq_shift]
    refine (norm_truncPole_zero_le hT (z - w x)).trans ?_
    rw [hK]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hmaxle z hz x) hT)) hT
  have hderivbound : ∀ z ∈ Metric.ball s₀ (1:ℝ), ∀ x,
      ‖deriv (truncPole 0 T) (z - w x)‖ ≤ T * K := by
    intro z hz x
    refine (norm_deriv_truncPole_zero_le hT (z - w x)).trans ?_
    rw [hK]
    refine mul_le_mul_of_nonneg_left ?_ hT
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hmaxle z hz x) hT)) hT
  have hint0 : Integrable (fun x => φ x * truncPole (w x) T s₀) μ := by
    refine Integrable.mono' (hφ.norm.mul_const K)
      (hφ.aestronglyMeasurable.mul (hmeasker s₀).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hkerbound s₀ (Metric.mem_ball_self one_pos) x) (norm_nonneg _)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (z : ℂ) (x : α) => φ x * truncPole (w x) T z)
    (F' := fun (z : ℂ) (x : α) => φ x * deriv (truncPole 0 T) (z - w x))
    (bound := fun x => ‖φ x‖ * (T * K))
    (x₀ := s₀) (s := Metric.ball s₀ 1) (μ := μ)
    (Metric.ball_mem_nhds s₀ one_pos)
    (Filter.Eventually.of_forall fun z =>
      hφ.aestronglyMeasurable.mul (hmeasker z).aestronglyMeasurable)
    hint0
    (hφ.aestronglyMeasurable.mul (hmeasderiv s₀).aestronglyMeasurable)
    ?_ (hφ.norm.mul_const (T * K)) ?_
  · exact key.2.differentiableAt
  · filter_upwards with x z hz
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hderivbound z hz x) (norm_nonneg _)
  · filter_upwards with x z _
    exact (hasDerivAt_truncPole (w x) T z).const_mul (φ x)

/-- **Entire approximation of a Cauchy transform on a closed half plane.**  If the complex measure
`φ dμ` is carried by `{Re w ≤ 1 - δ}` with `δ > 0`, then its Cauchy transform is uniformly
approximable on the closed half plane `{Re s ≥ 1}` by entire functions.  The approximant is the
same superposition of truncated Laplace kernels. -/
theorem exists_entire_approx_cauchyTransform (μ : Measure α) {w : α → ℂ} {φ : α → ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hw : ∀ x, (w x).re ≤ 1 - δ) (hwm : Measurable w) (hφ : Integrable φ μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ s : ℂ, 1 ≤ s.re → ‖(∫ x, φ x / (s - w x) ∂μ) - g s‖ ≤ ε := by
  set A : ℝ := ∫ x, ‖φ x‖ ∂μ with hA
  have hAnonneg : 0 ≤ A := integral_nonneg fun x => norm_nonneg _
  have htend : Filter.Tendsto (fun T : ℝ => A * (Real.exp (-(T * δ)) / δ)) Filter.atTop
      (nhds 0) := by
    have h1 : Filter.Tendsto (fun T : ℝ => T * δ) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.atTop_mul_const hδ
    have h2 : Filter.Tendsto (fun T : ℝ => -(T * δ)) Filter.atTop Filter.atBot :=
      Filter.tendsto_neg_atTop_atBot.comp h1
    have h3 : Filter.Tendsto (fun T : ℝ => Real.exp (-(T * δ))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp h2
    simpa using (h3.div_const δ).const_mul A
  obtain ⟨T, hTε, hT0⟩ :=
    ((htend.eventually (gt_mem_nhds hε)).and (Filter.eventually_ge_atTop (0:ℝ))).exists
  refine ⟨fun s => ∫ x, φ x * truncPole (w x) T s ∂μ,
    differentiable_truncCauchyTransform μ hw hwm hφ hT0, ?_⟩
  intro s hs
  set c : ℝ := Real.exp (-(T * δ)) / δ with hc
  have hcnonneg : 0 ≤ c := div_nonneg (Real.exp_nonneg _) hδ.le
  have hdist : ∀ x, δ ≤ ‖s - w x‖ := by
    intro x
    have h1 : |(s - w x).re| ≤ ‖s - w x‖ := by simpa using Complex.abs_re_le_norm (s - w x)
    have h2 : (s - w x).re = s.re - (w x).re := by simp [Complex.sub_re]
    have h3 : δ ≤ (s - w x).re := by rw [h2]; linarith [hw x]
    exact h3.trans ((le_abs_self _).trans h1)
  have hne : ∀ x, s - w x ≠ 0 := by
    intro x h
    have := hdist x
    rw [h, norm_zero] at this
    linarith
  have hkerdiff : ∀ x, ‖(s - w x)⁻¹ - truncPole (w x) T s‖ ≤ c := by
    intro x
    have hax : (w x).re < 1 := by linarith [hw x]
    refine (norm_pole_sub_truncPole_le hax hT0 hs).trans ?_
    have hu : δ ≤ 1 - (w x).re := by linarith [hw x]
    have hnum : -(T * (1 - (w x).re)) ≤ -(T * δ) := by nlinarith
    rw [hc]
    gcongr
  have hmeasker : Measurable fun x => truncPole (w x) T s := by
    have heq : (fun x => truncPole (w x) T s) = fun x => truncPole 0 T (s - w x) := by
      funext x
      exact truncPole_eq_shift (w x) T s
    rw [heq]
    exact ((differentiable_truncPole 0 T).continuous.measurable).comp
      (measurable_const.sub hwm)
  have hmeasdiv : AEStronglyMeasurable (fun x => φ x / (s - w x)) μ := by
    have heq : (fun x => φ x / (s - w x)) = fun x => φ x * (s - w x)⁻¹ := by
      funext x
      rw [div_eq_mul_inv]
    rw [heq]
    exact hφ.aestronglyMeasurable.mul ((measurable_const.sub hwm).inv).aestronglyMeasurable
  have hint1 : Integrable (fun x => φ x / (s - w x)) μ := by
    refine Integrable.mono' (hφ.norm.div_const δ) hmeasdiv ?_
    filter_upwards with x
    rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hδ (hdist x)
  have hint3 : Integrable (fun x => φ x * ((s - w x)⁻¹ - truncPole (w x) T s)) μ := by
    refine Integrable.mono' (hφ.norm.mul_const c)
      (hφ.aestronglyMeasurable.mul
        (((measurable_const.sub hwm).inv).sub hmeasker).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hkerdiff x) (norm_nonneg _)
  have hint2 : Integrable (fun x => φ x * truncPole (w x) T s) μ := by
    have : (fun x => φ x * truncPole (w x) T s)
        = fun x => φ x / (s - w x) - φ x * ((s - w x)⁻¹ - truncPole (w x) T s) := by
      funext x
      rw [div_eq_mul_inv, mul_sub]
      ring
    rw [this]
    exact hint1.sub hint3
  have hsplit : (∫ x, φ x / (s - w x) ∂μ) - ∫ x, φ x * truncPole (w x) T s ∂μ
      = ∫ x, φ x * ((s - w x)⁻¹ - truncPole (w x) T s) ∂μ := by
    rw [← integral_sub hint1 hint2]
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [div_eq_mul_inv, mul_sub]
  rw [hsplit]
  calc ‖∫ x, φ x * ((s - w x)⁻¹ - truncPole (w x) T s) ∂μ‖
      ≤ ∫ x, ‖φ x * ((s - w x)⁻¹ - truncPole (w x) T s)‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖φ x‖ * c ∂μ := by
        refine integral_mono hint3.norm (hφ.norm.mul_const c) fun x => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hkerdiff x) (norm_nonneg _)
    _ = A * c := integral_mul_const _ _
    _ ≤ ε := hTε.le

/-! ### Approximation on a general set to the right of the carrier -/

/-- The truncated Laplace kernel error, controlled by a lower bound for `Re (s - a)` alone.  This is
what makes a *far left* pole approximable simultaneously on a right half plane and on a disc. -/
theorem norm_pole_sub_truncPole_le_of_re {a s : ℂ} {T d : ℝ} (hT : 0 ≤ T) (hd : 0 < d)
    (h : d ≤ (s - a).re) :
    ‖(s - a)⁻¹ - truncPole a T s‖ ≤ Real.exp (-(T * d)) / d := by
  have hre : (0:ℝ) < (s - a).re := lt_of_lt_of_le hd h
  have hne : s - a ≠ 0 := by
    intro h0
    rw [h0] at hre
    simp at hre
  have hsa : s ≠ a := sub_ne_zero.mp hne
  have hnorm : d ≤ ‖s - a‖ :=
    le_trans h (le_trans (le_abs_self _) (Complex.abs_re_le_norm _))
  rw [truncPole_of_ne hsa]
  have hkey : (s - a)⁻¹ - (1 - Complex.exp (-(T : ℂ) * (s - a))) / (s - a)
      = Complex.exp (-(T : ℂ) * (s - a)) / (s - a) := by
    field_simp
    ring
  rw [hkey, norm_div, Complex.norm_exp]
  have hexp : (-(T : ℂ) * (s - a)).re = -(T * (s - a).re) := by
    simp [Complex.mul_re]
  rw [hexp]
  have hnum : Real.exp (-(T * (s - a).re)) ≤ Real.exp (-(T * d)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc Real.exp (-(T * (s - a).re)) / ‖s - a‖ ≤ Real.exp (-(T * d)) / ‖s - a‖ := by
        gcongr
    _ ≤ Real.exp (-(T * d)) / d := by
        gcongr

/-- **Entire approximation of a Cauchy transform on any set lying to the right of the carrier.**
If every point of `S` sees every carrier point at real distance at least `d > 0`, the Cauchy
transform of `φ dμ` is uniformly approximable on `S` by entire functions. -/
theorem exists_entire_approx_cauchyTransform_of_re_ge {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {w : α → ℂ} {φ : α → ℂ} {S : Set ℂ} {d : ℝ} (hd : 0 < d) (hS : S.Nonempty)
    (hw : ∀ x, ∀ s ∈ S, d ≤ (s - w x).re) (hwm : Measurable w) (hφ : Integrable φ μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ s ∈ S, ‖(∫ x, φ x / (s - w x) ∂μ) - g s‖ ≤ ε := by
  obtain ⟨s₀, hs₀⟩ := hS
  have hcarrier : ∀ x, (w x).re ≤ s₀.re - d := by
    intro x
    have := hw x s₀ hs₀
    rw [Complex.sub_re] at this
    linarith
  set A : ℝ := ∫ x, ‖φ x‖ ∂μ with hA
  have hAnonneg : 0 ≤ A := integral_nonneg fun x => norm_nonneg _
  have htend : Filter.Tendsto (fun T : ℝ => A * (Real.exp (-(T * d)) / d)) Filter.atTop
      (nhds 0) := by
    have h1 : Filter.Tendsto (fun T : ℝ => T * d) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.atTop_mul_const hd
    have h2 : Filter.Tendsto (fun T : ℝ => -(T * d)) Filter.atTop Filter.atBot :=
      Filter.tendsto_neg_atTop_atBot.comp h1
    have h3 : Filter.Tendsto (fun T : ℝ => Real.exp (-(T * d))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp h2
    simpa using (h3.div_const d).const_mul A
  obtain ⟨T, hTε, hT0⟩ :=
    ((htend.eventually (gt_mem_nhds hε)).and (Filter.eventually_ge_atTop (0:ℝ))).exists
  refine ⟨fun s => ∫ x, φ x * truncPole (w x) T s ∂μ,
    differentiable_truncCauchyTransform μ hcarrier hwm hφ hT0, ?_⟩
  intro s hs
  set c : ℝ := Real.exp (-(T * d)) / d with hc
  have hcnonneg : 0 ≤ c := div_nonneg (Real.exp_nonneg _) hd.le
  have hred : ∀ x, d ≤ (s - w x).re := fun x => hw x s hs
  have hdist : ∀ x, d ≤ ‖s - w x‖ := fun x =>
    le_trans (hred x) (le_trans (le_abs_self _) (Complex.abs_re_le_norm _))
  have hkerdiff : ∀ x, ‖(s - w x)⁻¹ - truncPole (w x) T s‖ ≤ c :=
    fun x => norm_pole_sub_truncPole_le_of_re hT0 hd (hred x)
  have hmeasker : Measurable fun x => truncPole (w x) T s := by
    have heq : (fun x => truncPole (w x) T s) = fun x => truncPole 0 T (s - w x) := by
      funext x
      exact truncPole_eq_shift (w x) T s
    rw [heq]
    exact ((differentiable_truncPole 0 T).continuous.measurable).comp
      (measurable_const.sub hwm)
  have hmeasdiv : AEStronglyMeasurable (fun x => φ x / (s - w x)) μ := by
    have heq : (fun x => φ x / (s - w x)) = fun x => φ x * (s - w x)⁻¹ := by
      funext x
      rw [div_eq_mul_inv]
    rw [heq]
    exact hφ.aestronglyMeasurable.mul ((measurable_const.sub hwm).inv).aestronglyMeasurable
  have hint1 : Integrable (fun x => φ x / (s - w x)) μ := by
    refine Integrable.mono' (hφ.norm.div_const d) hmeasdiv ?_
    filter_upwards with x
    rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hd (hdist x)
  have hint3 : Integrable (fun x => φ x * ((s - w x)⁻¹ - truncPole (w x) T s)) μ := by
    refine Integrable.mono' (hφ.norm.mul_const c)
      (hφ.aestronglyMeasurable.mul
        (((measurable_const.sub hwm).inv).sub hmeasker).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hkerdiff x) (norm_nonneg _)
  have hint2 : Integrable (fun x => φ x * truncPole (w x) T s) μ := by
    have heq : (fun x => φ x * truncPole (w x) T s)
        = fun x => φ x / (s - w x) - φ x * ((s - w x)⁻¹ - truncPole (w x) T s) := by
      funext x
      rw [div_eq_mul_inv, mul_sub]
      ring
    rw [heq]
    exact hint1.sub hint3
  have hsplit : (∫ x, φ x / (s - w x) ∂μ) - ∫ x, φ x * truncPole (w x) T s ∂μ
      = ∫ x, φ x * ((s - w x)⁻¹ - truncPole (w x) T s) ∂μ := by
    rw [← integral_sub hint1 hint2]
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [div_eq_mul_inv, mul_sub]
  rw [hsplit]
  calc ‖∫ x, φ x * ((s - w x)⁻¹ - truncPole (w x) T s) ∂μ‖
      ≤ ∫ x, ‖φ x * ((s - w x)⁻¹ - truncPole (w x) T s)‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖φ x‖ * c ∂μ := by
        refine integral_mono hint3.norm (hφ.norm.mul_const c) fun x => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hkerdiff x) (norm_nonneg _)
    _ = A * c := integral_mul_const _ _
    _ ≤ ε := hTε.le

/-- **A far-left carrier is approximable simultaneously on the closed half plane and on a disc.**
This is the two-piece approximation that drives the `∂̄` construction of an entire approximant on a
closed half plane. -/
theorem exists_entire_approx_cauchyTransform_halfPlane_union_ball {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {w : α → ℂ} {φ : α → ℂ} {ρ d : ℝ} (hd : 0 < d) (hρ : 0 ≤ ρ)
    (hw : ∀ x, (w x).re ≤ -ρ - d) (hwm : Measurable w) (hφ : Integrable φ μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ s : ℂ, (1 ≤ s.re ∨ ‖s‖ ≤ ρ) → ‖(∫ x, φ x / (s - w x) ∂μ) - g s‖ ≤ ε := by
  set S : Set ℂ := {s : ℂ | 1 ≤ s.re ∨ ‖s‖ ≤ ρ} with hSdef
  have hS : S.Nonempty := ⟨1, Or.inl (by simp)⟩
  have hwS : ∀ x, ∀ s ∈ S, d ≤ (s - w x).re := by
    intro x s hs
    rw [Complex.sub_re]
    rcases hs with h | h
    · linarith [hw x]
    · have : -‖s‖ ≤ s.re := by
        have := Complex.abs_re_le_norm s
        cases abs_le.mp this with
        | intro h1 _ => exact h1
      linarith [hw x]
  exact exists_entire_approx_cauchyTransform_of_re_ge μ hd hS hwS hwm hφ hε

end GaloisForLFunctions.HTGeometry

end
