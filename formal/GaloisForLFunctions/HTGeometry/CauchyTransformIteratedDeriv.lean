import GaloisForLFunctions.HTGeometry.RegularizedHerglotzTransform

/-!
# Higher derivatives of the Cauchy transform

The carrier freeness predicate is stated with iterated derivatives of the Cauchy transform at
shifted nodes, while the controllability theory is stated with powers of the Cauchy kernel.  The two
differ by a factorial.

Each differentiation under the integral raises the kernel power by one and multiplies by that power.
The domination is again by a constant on any ball avoiding the real axis, since the kernel powers are
uniformly bounded there, so the argument of the first derivative repeats verbatim at every order.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- The `k`-th kernel moment of a measure. -/
def cauchyKernelMoment (ν : Measure ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  ∫ t, (((t : ℝ) : ℂ) - z)⁻¹ ^ (k + 1) ∂ν

theorem cauchyKernelMoment_zero (ν : Measure ℝ) (z : ℂ) :
    cauchyKernelMoment ν 0 z = cauchyTransform ν z := by
  rw [cauchyKernelMoment, cauchyTransform]
  simp

/-- Off the real axis every kernel power is uniformly bounded. -/
theorem norm_kernelPow_le {z : ℂ} (hz : z.im ≠ 0) (k : ℕ) (t : ℝ) :
    ‖(((t : ℝ) : ℂ) - z)⁻¹ ^ (k + 1)‖ ≤ (|z.im|⁻¹) ^ (k + 1) := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inv_real_sub_le hz t) _

/-- Every kernel power is integrable against a finite measure. -/
theorem integrable_kernelPow (ν : Measure ℝ) [IsFiniteMeasure ν]
    {z : ℂ} (hz : z.im ≠ 0) (k : ℕ) :
    Integrable (fun t : ℝ => (((t : ℝ) : ℂ) - z)⁻¹ ^ (k + 1)) ν := by
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (((t : ℝ) : ℂ) - z)⁻¹ ^ (k + 1)) ν := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  refine Integrable.mono' (integrable_const ((|z.im|⁻¹) ^ (k + 1))) hmeas ?_
  filter_upwards with t
  exact norm_kernelPow_le hz k t

/-- **Differentiating a kernel moment raises its order.**  The derivative of the `k`-th kernel
moment is `k + 1` times the `(k + 1)`-st. -/
theorem hasDerivAt_cauchyKernelMoment (ν : Measure ℝ) [IsFiniteMeasure ν]
    (k : ℕ) {z₀ : ℂ} (hz₀ : z₀.im ≠ 0) :
    HasDerivAt (cauchyKernelMoment ν k)
      (((k : ℂ) + 1) * cauchyKernelMoment ν (k + 1) z₀) z₀ := by
  have himpos : 0 < |z₀.im| := abs_pos.mpr hz₀
  have hrpos : 0 < |z₀.im| / 2 := by linarith
  set s : Set ℂ := Metric.ball z₀ (|z₀.im| / 2) with hs
  have hsnhds : s ∈ nhds z₀ := Metric.ball_mem_nhds z₀ hrpos
  have hmemne : ∀ z ∈ s, z.im ≠ 0 := by
    intro z hz
    have hlow := lt_abs_im_of_mem_ball hz
    intro hzero
    rw [hzero] at hlow
    simp at hlow
    linarith
  have hmeas : ∀ z : ℂ,
      AEStronglyMeasurable
        (fun t : ℝ => (((t : ℝ) : ℂ) - z)⁻¹ ^ (k + 1)) ν := by
    intro z
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hmeas' : AEStronglyMeasurable
      (fun t : ℝ => ((k : ℂ) + 1) * (((t : ℝ) : ℂ) - z₀)⁻¹ ^ (k + 2)) ν := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hbound : ∀ᵐ t : ℝ ∂ν, ∀ z ∈ s,
      ‖((k : ℂ) + 1) * (((t : ℝ) : ℂ) - z)⁻¹ ^ (k + 2)‖ ≤
        ((k : ℝ) + 1) * ((|z₀.im| / 2)⁻¹) ^ (k + 2) := by
    filter_upwards with t z hz
    have hzne : z.im ≠ 0 := hmemne z hz
    have hlow : |z₀.im| / 2 < |z.im| := lt_abs_im_of_mem_ball hz
    have hstep : |z.im|⁻¹ ≤ (|z₀.im| / 2)⁻¹ := inv_anti₀ hrpos (le_of_lt hlow)
    rw [norm_mul]
    have hk : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
      rw [show ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hk]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine le_trans (norm_kernelPow_le hzne (k + 1) t) ?_
    exact pow_le_pow_left₀ (by positivity) hstep _
  have hdiff : ∀ᵐ t : ℝ ∂ν, ∀ z ∈ s,
      HasDerivAt (fun w : ℂ => (((t : ℝ) : ℂ) - w)⁻¹ ^ (k + 1))
        (((k : ℂ) + 1) * (((t : ℝ) : ℂ) - z)⁻¹ ^ (k + 2)) z := by
    filter_upwards with t z hz
    have hzne : z.im ≠ 0 := hmemne z hz
    have hden : ((t : ℝ) : ℂ) - z ≠ 0 := real_sub_ne_zero_of_im_ne_zero hzne t
    have hbase : HasDerivAt (fun w : ℂ => ((t : ℝ) : ℂ) - w) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub ((t : ℝ) : ℂ)
    have hinv : HasDerivAt (fun w : ℂ => (((t : ℝ) : ℂ) - w)⁻¹)
        ((((t : ℝ) : ℂ) - z)⁻¹ ^ 2) z := by
      have := hbase.inv hden
      exact this.congr_deriv (by field_simp)
    have hpow := hinv.pow (k + 1)
    exact hpow.congr_deriv (by
      push_cast
      ring)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := ν) (F := fun z t => (((t : ℝ) : ℂ) - z)⁻¹ ^ (k + 1))
    (F' := fun z t => ((k : ℂ) + 1) * (((t : ℝ) : ℂ) - z)⁻¹ ^ (k + 2))
    (bound := fun _ => ((k : ℝ) + 1) * ((|z₀.im| / 2)⁻¹) ^ (k + 2))
    hsnhds (Filter.Eventually.of_forall fun z => hmeas z)
    (integrable_kernelPow ν hz₀ k) hmeas' hbound
    (integrable_const _) hdiff
  have hval : ∫ t, ((k : ℂ) + 1) * (((t : ℝ) : ℂ) - z₀)⁻¹ ^ (k + 2) ∂ν =
      ((k : ℂ) + 1) * cauchyKernelMoment ν (k + 1) z₀ := by
    rw [integral_const_mul]
    rfl
  rw [← hval]
  exact hmain.2

/-- The complement of the real axis is open. -/
theorem isOpen_im_ne_zero : IsOpen {z : ℂ | z.im ≠ 0} :=
  (isOpen_compl_singleton).preimage Complex.continuous_im

/-- **Iterated derivatives are factorial multiples of the kernel moments.**  This is the exact
dictionary between the freeness predicate, stated with iterated derivatives of the Cauchy
transform, and the controllability theory, stated with kernel powers. -/
theorem iteratedDeriv_cauchyTransform (ν : Measure ℝ) [IsFiniteMeasure ν] :
    ∀ (k : ℕ) {z : ℂ}, z.im ≠ 0 →
      iteratedDeriv k (cauchyTransform ν) z =
        ((Nat.factorial k : ℕ) : ℂ) * cauchyKernelMoment ν k z := by
  intro k
  induction k with
  | zero =>
      intro z hz
      rw [iteratedDeriv_zero, cauchyKernelMoment_zero]
      simp
  | succ k ih =>
      intro z hz
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv k (cauchyTransform ν)
          =ᶠ[nhds z] fun w => ((Nat.factorial k : ℕ) : ℂ) * cauchyKernelMoment ν k w := by
        filter_upwards [isOpen_im_ne_zero.mem_nhds hz] with w hw
        exact ih hw
      rw [hev.deriv_eq,
        deriv_const_mul _ (hasDerivAt_cauchyKernelMoment ν k hz).differentiableAt,
        (hasDerivAt_cauchyKernelMoment ν k hz).deriv, Nat.factorial_succ]
      push_cast
      ring

/-- Each kernel moment is differentiable off the real axis. -/
theorem differentiableOn_cauchyKernelMoment (ν : Measure ℝ) [IsFiniteMeasure ν]
    (k : ℕ) {U : Set ℂ} (hUne : ∀ z ∈ U, z.im ≠ 0) :
    DifferentiableOn ℂ (cauchyKernelMoment ν k) U := by
  intro z hz
  exact (hasDerivAt_cauchyKernelMoment ν k (hUne z hz)).differentiableAt.differentiableWithinAt

/-- **Kernel moments are analytic in the node.**  On every open set avoiding the real axis each
kernel moment is analytic, hence in particular continuous in the node variable. -/
theorem analyticOnNhd_cauchyKernelMoment (ν : Measure ℝ) [IsFiniteMeasure ν]
    (k : ℕ) {U : Set ℂ} (hU : IsOpen U) (hUne : ∀ z ∈ U, z.im ≠ 0) :
    AnalyticOnNhd ℂ (cauchyKernelMoment ν k) U :=
  (differentiableOn_cauchyKernelMoment ν k hUne).analyticOnNhd hU

/-- Each kernel moment is continuous in the node off the real axis. -/
theorem continuousOn_cauchyKernelMoment (ν : Measure ℝ) [IsFiniteMeasure ν]
    (k : ℕ) {U : Set ℂ} (hUne : ∀ z ∈ U, z.im ≠ 0) :
    ContinuousOn (cauchyKernelMoment ν k) U :=
  (differentiableOn_cauchyKernelMoment ν k hUne).continuousOn

end

end GaloisForLFunctions.HTGeometry
