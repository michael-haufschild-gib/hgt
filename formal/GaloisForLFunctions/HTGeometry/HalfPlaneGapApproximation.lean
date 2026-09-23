import GaloisForLFunctions.HTGeometry.HalfPlanePolePushing

/-!
# Entire approximation on a closed half plane together with a disc

The carrier of the measure sits in the *gap*: to the left of the line `Re s = 1`, and far above or
below a disc `‖s‖ ≤ ρ`.  A single truncated Laplace kernel cannot approximate `1/(s-w)` on both
pieces, because the exponent changes sign; pushing the pole left by `L` first, and then truncating,
does work, and this file assembles the pushed kernels into an entire approximant of the whole Cauchy
transform.

The differentiability of the approximant comes from a general parametric-integral lemma: an
integral `∫ φ(x) K(x, s) dμ(x)` is entire as soon as `K(x, ·)` is differentiable with a derivative
bounded uniformly in `x` on balls.
-/

noncomputable section

open Complex MeasureTheory Metric

namespace GaloisForLFunctions.HTGeometry

/-! ### A parametric-integral entirety criterion -/

/-- **Entirety of a parametric integral.**  A uniformly bounded family of entire kernels with
uniformly bounded derivatives integrates to an entire function. -/
theorem differentiable_integral_kernel {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {φ : α → ℂ} (hφ : Integrable φ μ) (K K' : α → ℂ → ℂ)
    (hmeas : ∀ s : ℂ, Measurable fun x => K x s)
    (hmeas' : ∀ s : ℂ, Measurable fun x => K' x s)
    (hderiv : ∀ x s, HasDerivAt (K x) (K' x s) s)
    (hbdd : ∀ s₀ : ℂ, ∃ C : ℝ, ∀ x, ∀ s ∈ Metric.ball s₀ (1:ℝ), ‖K x s‖ ≤ C ∧ ‖K' x s‖ ≤ C) :
    Differentiable ℂ fun s => ∫ x, φ x * K x s ∂μ := by
  intro s₀
  obtain ⟨C, hC⟩ := hbdd s₀
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hbound1 : ∀ x, ∀ s ∈ Metric.ball s₀ (1:ℝ), ‖K x s‖ ≤ C' :=
    fun x s hs => le_trans (hC x s hs).1 (le_max_left _ _)
  have hbound2 : ∀ x, ∀ s ∈ Metric.ball s₀ (1:ℝ), ‖K' x s‖ ≤ C' :=
    fun x s hs => le_trans (hC x s hs).2 (le_max_left _ _)
  have hint0 : Integrable (fun x => φ x * K x s₀) μ := by
    refine Integrable.mono' (hφ.norm.mul_const C')
      (hφ.aestronglyMeasurable.mul (hmeas s₀).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound1 x s₀ (Metric.mem_ball_self one_pos)) (norm_nonneg _)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (s : ℂ) (x : α) => φ x * K x s)
    (F' := fun (s : ℂ) (x : α) => φ x * K' x s)
    (bound := fun x => ‖φ x‖ * C')
    (x₀ := s₀) (s := Metric.ball s₀ 1) (μ := μ)
    (Metric.ball_mem_nhds s₀ one_pos)
    (Filter.Eventually.of_forall fun s =>
      hφ.aestronglyMeasurable.mul (hmeas s).aestronglyMeasurable)
    hint0
    (hφ.aestronglyMeasurable.mul (hmeas' s₀).aestronglyMeasurable)
    ?_ (hφ.norm.mul_const C') ?_
  · exact key.2.differentiableAt
  · filter_upwards with x s hs
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound2 x s hs) (norm_nonneg _)
  · filter_upwards with x s _
    exact (hderiv x s).const_mul (φ x)

/-! ### The pushed kernel as a parametric family -/

/-- The derivative of the pushed kernel. -/
theorem hasDerivAt_pushedKernel (z z' : ℂ) (N : ℕ) (T : ℝ) (s : ℂ) :
    HasDerivAt (pushedKernel z z' N T)
      (∑ j ∈ Finset.range N, (z - z') ^ j *
        (((j + 1 : ℕ) : ℂ) * (truncPole z' T s) ^ j * deriv (truncPole 0 T) (s - z'))) s := by
  have hbase : HasDerivAt (truncPole z' T) (deriv (truncPole 0 T) (s - z')) s :=
    hasDerivAt_truncPole z' T s
  have hpow : ∀ j : ℕ, HasDerivAt (fun t => (truncPole z' T t) ^ (j + 1))
      (((j + 1 : ℕ) : ℂ) * (truncPole z' T s) ^ j * deriv (truncPole 0 T) (s - z')) s := by
    intro j
    have h := hbase.pow (j + 1)
    have hidx : j + 1 - 1 = j := by omega
    rw [hidx] at h
    exact h
  have hsum := HasDerivAt.sum (u := Finset.range N)
    (A := fun (j : ℕ) (t : ℂ) => (z - z') ^ j * (truncPole z' T t) ^ (j + 1))
    (A' := fun j => (z - z') ^ j *
      (((j + 1 : ℕ) : ℂ) * (truncPole z' T s) ^ j * deriv (truncPole 0 T) (s - z')))
    (fun j _ => (hpow j).const_mul ((z - z') ^ j))
  have heq : (∑ i ∈ Finset.range N, fun t : ℂ => (z - z') ^ i * (truncPole z' T t) ^ (i + 1))
      = pushedKernel z z' N T := by
    funext t
    simp [pushedKernel, Finset.sum_apply]
  rw [heq] at hsum
  exact hsum

/-- A crude but uniform bound for the pushed kernel. -/
theorem norm_pushedKernel_le {z z' s : ℂ} {T M A : ℝ} (N : ℕ) (hT : 0 ≤ T)
    (hM : ‖z - z'‖ ≤ M) (hM0 : 0 ≤ M) (hA : max 0 (z'.re - s.re) ≤ A) :
    ‖pushedKernel z z' N T s‖
      ≤ ∑ j ∈ Finset.range N, M ^ j * (T * Real.exp (T * A)) ^ (j + 1) := by
  have hker : ‖truncPole z' T s‖ ≤ T * Real.exp (T * A) := by
    rw [truncPole_eq_shift]
    refine le_trans (norm_truncPole_zero_le hT (s - z')) ?_
    have hre : max 0 (-(s - z').re) ≤ A := by
      have : -(s - z').re = z'.re - s.re := by simp [Complex.sub_re]
      rw [this]
      exact hA
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hre hT)) hT
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_pow, norm_pow]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hM j)
    (pow_le_pow_left₀ (norm_nonneg _) hker (j + 1)) (by positivity) (by positivity)

/-- A crude but uniform bound for the derivative of the pushed kernel. -/
theorem norm_deriv_pushedKernel_le {z z' s : ℂ} {T M A : ℝ} (N : ℕ) (hT : 0 ≤ T)
    (hM : ‖z - z'‖ ≤ M) (hM0 : 0 ≤ M) (hA : max 0 (z'.re - s.re) ≤ A) :
    ‖∑ j ∈ Finset.range N, (z - z') ^ j *
        (((j + 1 : ℕ) : ℂ) * (truncPole z' T s) ^ j * deriv (truncPole 0 T) (s - z'))‖
      ≤ ∑ j ∈ Finset.range N,
          M ^ j * (((j : ℝ) + 1) * (T * Real.exp (T * A)) ^ j * (T * (T * Real.exp (T * A)))) := by
  have hre : max 0 (-(s - z').re) ≤ A := by
    have h : -(s - z').re = z'.re - s.re := by simp [Complex.sub_re]
    rw [h]
    exact hA
  have hker : ‖truncPole z' T s‖ ≤ T * Real.exp (T * A) := by
    rw [truncPole_eq_shift]
    refine le_trans (norm_truncPole_zero_le hT (s - z')) ?_
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hre hT)) hT
  have hderiv : ‖deriv (truncPole 0 T) (s - z')‖ ≤ T * (T * Real.exp (T * A)) := by
    refine le_trans (norm_deriv_truncPole_zero_le hT (s - z')) ?_
    refine mul_le_mul_of_nonneg_left ?_ hT
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hre hT)) hT
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_pow, norm_mul, norm_mul, norm_pow]
  have hj : ‖((j + 1 : ℕ) : ℂ)‖ = (j : ℝ) + 1 := by
    rw [Complex.norm_natCast]
    push_cast
    ring
  rw [hj]
  refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hM j) ?_ (by positivity) (by positivity)
  refine mul_le_mul (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hker j) (by positivity)) hderiv (norm_nonneg _)
    (by positivity)

/-! ### The two-piece approximation theorem -/

/-- **Entire approximation of a Cauchy transform on a closed half plane together with a disc.**
The carrier lies to the left of the line `Re s = 1` by `δ`, and at imaginary height at least
`ρ + L + δ`, so that pushing every pole left by `L` places it far to the left of both the half
plane and the disc.  The pushed and truncated kernels then approximate the Cauchy transform
uniformly on `{Re s ≥ 1} ∪ {‖s‖ ≤ ρ}`. -/
theorem exists_entire_approx_cauchyTransform_gap {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {w : α → ℂ} {φ : α → ℂ} {ρ δ L : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 < δ) (hL : 1 + ρ < L)
    (hcar1 : ∀ x, (w x).re ≤ 1 - δ)
    (hcar2 : ∀ x, ρ + L + δ ≤ |(w x).im|)
    (hwm : Measurable w) (hφ : Integrable φ μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ s : ℂ, (1 ≤ s.re ∨ ‖s‖ ≤ ρ) → ‖(∫ x, φ x / (s - w x) ∂μ) - g s‖ ≤ ε := by
  have hL0 : 0 < L := by linarith
  set d₁ : ℝ := L - ρ - 1 with hd₁def
  set d₂ : ℝ := L + δ with hd₂def
  have hd₁ : 0 < d₁ := by rw [hd₁def]; linarith
  have hd₂ : 0 < d₂ := by rw [hd₂def]; linarith
  set w' : α → ℂ := fun x => w x - (L : ℂ) with hw'def
  have hw'meas : Measurable w' := hwm.sub measurable_const
  have hshift : ∀ x, w x - w' x = (L : ℂ) := by
    intro x
    rw [hw'def]
    ring
  have hshiftnorm : ∀ x, ‖w x - w' x‖ = L := by
    intro x
    rw [hshift x, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL0]
  have hw're : ∀ x, (w' x).re = (w x).re - L := by
    intro x
    rw [hw'def]
    simp
  -- the two geometric estimates on the target set
  have hre1 : ∀ x, ∀ s : ℂ, (1 ≤ s.re ∨ ‖s‖ ≤ ρ) → d₁ ≤ (s - w' x).re := by
    intro x s hs
    rw [Complex.sub_re, hw're x, hd₁def]
    rcases hs with h | h
    · linarith [hcar1 x]
    · have hsre : -ρ ≤ s.re := by
        have habs := Complex.abs_re_le_norm s
        have := abs_le.mp habs
        linarith [this.1]
      linarith [hcar1 x]
  have hnorm2 : ∀ x, ∀ s : ℂ, (1 ≤ s.re ∨ ‖s‖ ≤ ρ) → d₂ ≤ ‖s - w' x‖ := by
    intro x s hs
    rcases hs with h | h
    · refine le_trans ?_ (le_trans (le_abs_self _) (Complex.abs_re_le_norm (s - w' x)))
      rw [Complex.sub_re, hw're x, hd₂def]
      linarith [hcar1 x]
    · refine le_trans ?_ (Complex.abs_im_le_norm (s - w' x))
      have hsim : |s.im| ≤ ρ := le_trans (Complex.abs_im_le_norm s) h
      have hwim : ρ + L + δ ≤ |(w x).im| := hcar2 x
      have himeq : (s - w' x).im = s.im - (w x).im := by
        rw [Complex.sub_im, hw'def]
        simp
      have h2 : |(w x).im| - |s.im| ≤ |s.im - (w x).im| := by
        rw [abs_sub_comm]
        exact abs_sub_abs_le_abs_sub (w x).im s.im
      rw [himeq, hd₂def]
      linarith
  -- choose the truncation order and the truncation length
  set A : ℝ := ∫ x, ‖φ x‖ ∂μ with hA
  have hAnonneg : 0 ≤ A := integral_nonneg fun x => norm_nonneg _
  set q : ℝ := L / d₂ with hq
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq1 : q < 1 := by
    rw [hq, div_lt_one hd₂, hd₂def]
    linarith
  have htendN : Filter.Tendsto (fun N : ℕ => A * (q ^ N / (d₂ - L))) Filter.atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    simpa using ((h.div_const (d₂ - L)).const_mul A)
  obtain ⟨N, hN⟩ := (htendN.eventually (gt_mem_nhds (by linarith : (0:ℝ) < ε / 2))).exists
  set B : ℝ := (N : ℝ) ^ (2 : ℕ) * (max 1 (2 * L / d₁)) ^ N with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    positivity
  have htendT : Filter.Tendsto (fun T : ℝ => A * (B * (Real.exp (-(T * d₁)) / d₁)))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun T : ℝ => T * d₁) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.atTop_mul_const hd₁
    have h2 : Filter.Tendsto (fun T : ℝ => -(T * d₁)) Filter.atTop Filter.atBot :=
      Filter.tendsto_neg_atTop_atBot.comp h1
    have h3 : Filter.Tendsto (fun T : ℝ => Real.exp (-(T * d₁))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp h2
    simpa using (((h3.div_const d₁).const_mul B).const_mul A)
  obtain ⟨T, hT, hT0⟩ :=
    ((htendT.eventually (gt_mem_nhds (by linarith : (0:ℝ) < ε / 2))).and
      (Filter.eventually_ge_atTop (0:ℝ))).exists
  -- the approximant
  refine ⟨fun s => ∫ x, φ x * pushedKernel (w x) (w' x) N T s ∂μ, ?_, ?_⟩
  · -- entirety
    refine differentiable_integral_kernel μ hφ (fun x s => pushedKernel (w x) (w' x) N T s)
      (fun x s => ∑ j ∈ Finset.range N, (w x - w' x) ^ j *
        (((j + 1 : ℕ) : ℂ) * (truncPole (w' x) T s) ^ j * deriv (truncPole 0 T) (s - w' x)))
      ?_ ?_ (fun x s => hasDerivAt_pushedKernel (w x) (w' x) N T s) ?_
    · intro s
      have hker : Measurable fun x => truncPole (w' x) T s := by
        have heq : (fun x => truncPole (w' x) T s) = fun x => truncPole 0 T (s - w' x) := by
          funext x
          exact truncPole_eq_shift (w' x) T s
        rw [heq]
        exact ((differentiable_truncPole 0 T).continuous.measurable).comp
          (measurable_const.sub hw'meas)
      refine Finset.measurable_sum _ fun j _ => ?_
      exact ((hwm.sub hw'meas).pow_const j).mul (hker.pow_const (j + 1))
    · intro s
      have hker : Measurable fun x => truncPole (w' x) T s := by
        have heq : (fun x => truncPole (w' x) T s) = fun x => truncPole 0 T (s - w' x) := by
          funext x
          exact truncPole_eq_shift (w' x) T s
        rw [heq]
        exact ((differentiable_truncPole 0 T).continuous.measurable).comp
          (measurable_const.sub hw'meas)
      have hderivmeas : Measurable fun x => deriv (truncPole 0 T) (s - w' x) :=
        (((differentiable_truncPole 0 T).deriv).continuous.measurable).comp
          (measurable_const.sub hw'meas)
      refine Finset.measurable_sum _ fun j _ => ?_
      exact ((hwm.sub hw'meas).pow_const j).mul
        ((measurable_const.mul (hker.pow_const j)).mul hderivmeas)
    · intro s₀
      set Aexp : ℝ := max 0 (1 - δ - L - (s₀.re - 1)) with hAexp
      have hAexp0 : 0 ≤ Aexp := le_max_left _ _
      have hAle : ∀ x, ∀ s ∈ Metric.ball s₀ (1:ℝ), max 0 ((w' x).re - s.re) ≤ Aexp := by
        intro x s hs
        have hsre : s₀.re - 1 ≤ s.re := by
          have h2 : ‖s - s₀‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hs
          have h1 : |(s - s₀).re| ≤ ‖s - s₀‖ := by simpa using Complex.abs_re_le_norm (s - s₀)
          have h3 : |s.re - s₀.re| ≤ ‖s - s₀‖ := by simpa [Complex.sub_re] using h1
          have h4 := abs_le.mp (h3.trans h2.le)
          linarith [h4.1]
        refine max_le_max le_rfl ?_
        rw [hw're x]
        linarith [hcar1 x]
      refine ⟨max (∑ j ∈ Finset.range N, L ^ j * (T * Real.exp (T * Aexp)) ^ (j + 1))
        (∑ j ∈ Finset.range N, L ^ j *
          (((j : ℝ) + 1) * (T * Real.exp (T * Aexp)) ^ j * (T * (T * Real.exp (T * Aexp))))),
        fun x s hs => ⟨?_, ?_⟩⟩
      · exact le_trans (norm_pushedKernel_le N hT0 (le_of_eq (hshiftnorm x)) hL0.le
          (hAle x s hs)) (le_max_left _ _)
      · exact le_trans (norm_deriv_pushedKernel_le N hT0 (le_of_eq (hshiftnorm x)) hL0.le
          (hAle x s hs)) (le_max_right _ _)
  · -- the error bound
    intro s hs
    set c : ℝ := q ^ N / (d₂ - L) + B * (Real.exp (-(T * d₁)) / d₁) with hc
    have hc0 : 0 ≤ c := by
      rw [hc]
      have h1 : 0 ≤ q ^ N / (d₂ - L) := by
        have : 0 < d₂ - L := by rw [hd₂def]; linarith
        positivity
      have h2 : 0 ≤ B * (Real.exp (-(T * d₁)) / d₁) := by positivity
      linarith
    have hkerdiff : ∀ x, ‖(s - w x)⁻¹ - pushedKernel (w x) (w' x) N T s‖ ≤ c := by
      intro x
      have hMlt : ‖w x - w' x‖ < d₂ := by
        rw [hshiftnorm x, hd₂def]
        linarith
      have h := norm_inv_sub_pushedKernel_le (z := w x) (z' := w' x) (s := s)
        (d₁ := d₁) (d₂ := d₂) (T := T) N hd₁ (hre1 x s hs) hd₂ (hnorm2 x s hs) hT0 hMlt
      rw [hshiftnorm x] at h
      rw [hc, hB, hq]
      exact h
    have hdist : ∀ x, δ ≤ ‖s - w x‖ := by
      intro x
      rcases hs with h | h
      · refine le_trans ?_ (le_trans (le_abs_self _) (Complex.abs_re_le_norm (s - w x)))
        rw [Complex.sub_re]
        linarith [hcar1 x]
      · refine le_trans ?_ (Complex.abs_im_le_norm (s - w x))
        have hsim : |s.im| ≤ ρ := le_trans (Complex.abs_im_le_norm s) h
        have h2 : |(w x).im| - |s.im| ≤ |s.im - (w x).im| := by
          rw [abs_sub_comm]
          exact abs_sub_abs_le_abs_sub (w x).im s.im
        rw [Complex.sub_im]
        linarith [hcar2 x]
    have hmeasker : Measurable fun x => pushedKernel (w x) (w' x) N T s := by
      have hker : Measurable fun x => truncPole (w' x) T s := by
        have heq : (fun x => truncPole (w' x) T s) = fun x => truncPole 0 T (s - w' x) := by
          funext x
          exact truncPole_eq_shift (w' x) T s
        rw [heq]
        exact ((differentiable_truncPole 0 T).continuous.measurable).comp
          (measurable_const.sub hw'meas)
      refine Finset.measurable_sum _ fun j _ => ?_
      exact ((hwm.sub hw'meas).pow_const j).mul (hker.pow_const (j + 1))
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
    have hint3 : Integrable
        (fun x => φ x * ((s - w x)⁻¹ - pushedKernel (w x) (w' x) N T s)) μ := by
      refine Integrable.mono' (hφ.norm.mul_const c)
        (hφ.aestronglyMeasurable.mul
          (((measurable_const.sub hwm).inv).sub hmeasker).aestronglyMeasurable) ?_
      filter_upwards with x
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hkerdiff x) (norm_nonneg _)
    have hint2 : Integrable (fun x => φ x * pushedKernel (w x) (w' x) N T s) μ := by
      have heq : (fun x => φ x * pushedKernel (w x) (w' x) N T s)
          = fun x => φ x / (s - w x)
            - φ x * ((s - w x)⁻¹ - pushedKernel (w x) (w' x) N T s) := by
        funext x
        rw [div_eq_mul_inv, mul_sub]
        ring
      rw [heq]
      exact hint1.sub hint3
    have hsplit : (∫ x, φ x / (s - w x) ∂μ)
        - ∫ x, φ x * pushedKernel (w x) (w' x) N T s ∂μ
        = ∫ x, φ x * ((s - w x)⁻¹ - pushedKernel (w x) (w' x) N T s) ∂μ := by
      rw [← integral_sub hint1 hint2]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [div_eq_mul_inv, mul_sub]
    rw [hsplit]
    have hfinal : A * c ≤ ε := by
      rw [hc, mul_add]
      linarith [hN, hT]
    calc ‖∫ x, φ x * ((s - w x)⁻¹ - pushedKernel (w x) (w' x) N T s) ∂μ‖
        ≤ ∫ x, ‖φ x * ((s - w x)⁻¹ - pushedKernel (w x) (w' x) N T s)‖ ∂μ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖φ x‖ * c ∂μ := by
          refine integral_mono hint3.norm (hφ.norm.mul_const c) fun x => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hkerdiff x) (norm_nonneg _)
      _ = A * c := integral_mul_const _ _
      _ ≤ ε := hfinal

/-! ### A single Cauchy kernel -/

/-- **A single Cauchy kernel with pole off the half plane is entirely approximable on the half
plane together with a disc**, as soon as the pole is far enough out compared with the disc.  Either
the pole already lies to the left of the disc, and the truncated Laplace kernel works directly, or
its imaginary part is large, and the pushed kernel works. -/
theorem exists_entire_approx_single_kernel {c a : ℂ} (ha : a.re < 1) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hbig : 8 * ρ + 16 ≤ ‖a‖) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ s : ℂ, (1 ≤ s.re ∨ ‖s‖ ≤ ρ) → ‖c * (s - a)⁻¹ - g s‖ ≤ ε := by
  have hdiracInt : Integrable (fun _ : Unit => c) (Measure.dirac ()) := integrable_const c
  have hdiracEval : ∀ s : ℂ,
      (∫ _x : Unit, c / (s - a) ∂(Measure.dirac ())) = c * (s - a)⁻¹ := by
    intro s
    rw [integral_const]
    simp [div_eq_mul_inv]
  by_cases hleft : a.re ≤ -ρ - 1
  · obtain ⟨g, hgd, hgb⟩ :=
      exists_entire_approx_cauchyTransform_halfPlane_union_ball (α := Unit)
        (Measure.dirac ()) (w := fun _ => a) (φ := fun _ => c)
        (ρ := ρ) (d := 1) one_pos hρ (fun _ => by linarith) measurable_const hdiracInt hε
    refine ⟨g, hgd, fun s hs => ?_⟩
    have := hgb s hs
    rwa [hdiracEval s] at this
  · rw [not_le] at hleft
    set δ : ℝ := 1 - a.re with hδdef
    have hδ : 0 < δ := by rw [hδdef]; linarith
    set L : ℝ := ‖a‖ / 4 with hLdef
    have hanorm : (16 : ℝ) ≤ ‖a‖ := by linarith
    have hL : 1 + ρ < L := by
      rw [hLdef]
      linarith
    have hreabs : |a.re| ≤ ‖a‖ / 8 := by
      refine abs_le.mpr ⟨by linarith, by linarith⟩
    have hsq : (a.re) ^ (2 : ℕ) ≤ (‖a‖ / 8) ^ (2 : ℕ) := by
      have h1 : |a.re| ^ (2 : ℕ) = (a.re) ^ (2 : ℕ) := sq_abs _
      calc (a.re) ^ (2 : ℕ) = |a.re| ^ (2 : ℕ) := h1.symm
        _ ≤ (‖a‖ / 8) ^ (2 : ℕ) := by
            refine pow_le_pow_left₀ (abs_nonneg _) hreabs 2
    have hnormsq : ‖a‖ ^ (2 : ℕ) = (a.re) ^ (2 : ℕ) + (a.im) ^ (2 : ℕ) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    have himsq : (‖a‖ / 2) ^ (2 : ℕ) ≤ (a.im) ^ (2 : ℕ) := by
      have h64 : (‖a‖ / 8) ^ (2 : ℕ) = ‖a‖ ^ (2 : ℕ) / 64 := by ring
      have h4 : (‖a‖ / 2) ^ (2 : ℕ) = ‖a‖ ^ (2 : ℕ) / 4 := by ring
      nlinarith [hnormsq, hsq, h64, h4, sq_nonneg (a.im)]
    have him : ‖a‖ / 2 ≤ |a.im| := by
      have h1 : (0:ℝ) ≤ ‖a‖ / 2 := by positivity
      have h2 : |a.im| ^ (2 : ℕ) = (a.im) ^ (2 : ℕ) := sq_abs _
      nlinarith [abs_nonneg a.im, himsq, h2]
    have hcar2 : ρ + L + δ ≤ |a.im| := by
      refine le_trans ?_ him
      rw [hLdef, hδdef]
      linarith
    obtain ⟨g, hgd, hgb⟩ :=
      exists_entire_approx_cauchyTransform_gap (α := Unit)
        (Measure.dirac ()) (w := fun _ => a) (φ := fun _ => c)
        (ρ := ρ) (δ := δ) (L := L) hρ hδ hL (fun _ => by rw [hδdef]; linarith)
        (fun _ => hcar2) measurable_const hdiracInt hε
    refine ⟨g, hgd, fun s hs => ?_⟩
    have := hgb s hs
    rwa [hdiracEval s] at this

/-- A single Cauchy kernel with pole to the left of the line is entirely approximable on the closed
half plane alone, with no condition on the pole beyond `Re a < 1`. -/
theorem exists_entire_approx_single_kernel_halfPlane {c a : ℂ} (ha : a.re < 1) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ s : ℂ, 1 ≤ s.re → ‖c * (s - a)⁻¹ - g s‖ ≤ ε := by
  have hdiracInt : Integrable (fun _ : Unit => c) (Measure.dirac ()) := integrable_const c
  have hdiracEval : ∀ s : ℂ,
      (∫ _x : Unit, c / (s - a) ∂(Measure.dirac ())) = c * (s - a)⁻¹ := by
    intro s
    rw [integral_const]
    simp [div_eq_mul_inv]
  obtain ⟨g, hgd, hgb⟩ := exists_entire_approx_cauchyTransform (α := Unit) (Measure.dirac ())
    (w := fun _ => a) (φ := fun _ => c) (δ := 1 - a.re) (by linarith) (fun _ => by linarith)
    measurable_const hdiracInt hε
  refine ⟨g, hgd, fun s hs => ?_⟩
  have hb := hgb s hs
  rwa [hdiracEval s] at hb

end GaloisForLFunctions.HTGeometry

end
