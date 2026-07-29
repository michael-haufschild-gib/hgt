import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The regularized Herglotz transform as a rational gauge of a Cauchy transform

A positive Borel measure carrying a Herglotz transform need not be finite: the only standing
hypothesis is the Nevanlinna growth condition

```text
∫ (1 + t ^ 2)⁻¹ dμ(t) < ∞.
```

The regularization `t / (1 + t ^ 2)` subtracted from the Cauchy kernel is exactly what makes the
integral converge under that hypothesis.  This module isolates the algebraic content of the
regularization: the regularized kernel is the plain Cauchy kernel of the *weighted* measure
`(1 + t ^ 2)⁻¹ dμ`, read through a rational gauge in the spectral variable.

Concretely, for real `t` and non-real `z`,

```text
1 / (t - z) - t / (1 + t ^ 2) = (1 + t ^ 2)⁻¹ * (z + (1 + z ^ 2) / (t - z)).
```

Because the weighted measure is finite precisely under the growth condition, this exhibits the
regularized transform as `z * (total mass) + (1 + z ^ 2) *` (an honest Cauchy transform of a finite
measure).  Both operations are rational in `z`, so they do not change the differential field
generated over `ℂ(z)`.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-- The Cauchy kernel regularized by the Nevanlinna subtraction. -/
def regularizedHerglotzKernel (t : ℝ) (z : ℂ) : ℂ :=
  1 / ((t : ℂ) - z) - (t : ℂ) / (1 + (t : ℂ) ^ 2)

/-- The Nevanlinna weight `(1 + t ^ 2)⁻¹`, as a nonnegative real. -/
def nevanlinnaWeight (t : ℝ) : ℝ := (1 + t ^ 2)⁻¹

theorem nevanlinnaWeight_pos (t : ℝ) : 0 < nevanlinnaWeight t := by
  have h : (0 : ℝ) < 1 + t ^ 2 := by positivity
  exact inv_pos.mpr h

theorem one_add_sq_ne_zero (t : ℝ) : (1 : ℂ) + (t : ℂ) ^ 2 ≠ 0 := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hcast : (1 : ℂ) + (t : ℂ) ^ 2 = ((1 + t ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast]
  exact_mod_cast hpos.ne'

/-- A real point never meets a non-real spectral parameter. -/
theorem real_sub_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) :
    (t : ℂ) - z ≠ 0 := by
  intro h
  apply hz
  have : ((t : ℂ) - z).im = 0 := by rw [h]; simp
  simpa using this

/-- **Regularization is a rational gauge.**  Pointwise, the regularized Herglotz kernel is the
plain Cauchy kernel of the Nevanlinna-weighted measure, corrected by a term affine in the
spectral variable. -/
theorem regularizedHerglotzKernel_eq {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) :
    regularizedHerglotzKernel t z =
      (nevanlinnaWeight t : ℂ) * (z + (1 + z ^ 2) / ((t : ℂ) - z)) := by
  have hden : (t : ℂ) - z ≠ 0 := real_sub_ne_zero_of_im_ne_zero hz t
  have hsq : (1 : ℂ) + (t : ℂ) ^ 2 ≠ 0 := one_add_sq_ne_zero t
  have hw : (nevanlinnaWeight t : ℂ) = (1 + (t : ℂ) ^ 2)⁻¹ := by
    rw [nevanlinnaWeight]
    push_cast
    ring
  rw [regularizedHerglotzKernel, hw]
  field_simp
  ring

/-- Off the real axis the Cauchy kernel is uniformly bounded by the reciprocal distance to the
axis. -/
theorem norm_inv_real_sub_le {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) :
    ‖((t : ℂ) - z)⁻¹‖ ≤ |z.im|⁻¹ := by
  have himpos : 0 < |z.im| := abs_pos.mpr hz
  have hlow : |z.im| ≤ ‖(t : ℂ) - z‖ := by
    have h := Complex.abs_im_le_norm ((t : ℂ) - z)
    have him : ((t : ℂ) - z).im = -z.im := by simp
    rw [him, abs_neg] at h
    exact h
  rw [norm_inv]
  exact inv_anti₀ himpos hlow

/-- The Nevanlinna-weighted reweighted measure `(1 + t ^ 2)⁻¹ exp (u t) dμ`. -/
def nevanlinnaWeightedMeasure (μ : Measure ℝ) (u : ℝ → ℝ) : Measure ℝ :=
  μ.withDensity (fun t => (Real.toNNReal (nevanlinnaWeight t * Real.exp (u t)) : ℝ≥0∞))

/-- Against a finite measure the Cauchy kernel of a non-real parameter is integrable. -/
theorem integrable_cauchyKernel (ν : Measure ℝ) [IsFiniteMeasure ν] {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (fun t : ℝ => ((t : ℂ) - z)⁻¹) ν := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => ((t : ℂ) - z)⁻¹) ν := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  refine Integrable.mono' (integrable_const |z.im|⁻¹) hmeas ?_
  filter_upwards with t
  simpa using norm_inv_real_sub_le hz t

/-- **The regularized transform is a rational gauge of a Cauchy transform.**  Under the Nevanlinna
growth condition — recorded here as finiteness of the weighted measure — the regularized Herglotz
transform of `μ` reweighted by `exp u` is the Cauchy transform of the finite weighted measure,
multiplied by `1 + z ^ 2` and shifted by `z` times the total mass.  Both corrections are rational
in the spectral variable. -/
theorem regularizedHerglotzTransform_eq
    (μ : Measure ℝ) (u : ℝ → ℝ) (hu : Measurable u) {z : ℂ} (hz : z.im ≠ 0)
    [IsFiniteMeasure (nevanlinnaWeightedMeasure μ u)] :
    ∫ t, regularizedHerglotzKernel t z * (Real.exp (u t) : ℂ) ∂μ =
      z * (((nevanlinnaWeightedMeasure μ u).real Set.univ : ℝ) : ℂ) +
        (1 + z ^ 2) *
          ∫ t, ((t : ℂ) - z)⁻¹ ∂(nevanlinnaWeightedMeasure μ u) := by
  classical
  set ν := nevanlinnaWeightedMeasure μ u with hν
  have hdensmeas : Measurable
      (fun t : ℝ => Real.toNNReal (nevanlinnaWeight t * Real.exp (u t))) := by
    apply Measurable.real_toNNReal
    apply Measurable.mul
    · unfold nevanlinnaWeight
      fun_prop
    · exact (Real.measurable_exp.comp hu)
  -- Split the Cauchy-gauge integral over the finite weighted measure.
  have hsplit :
      ∫ t, (z + (1 + z ^ 2) * ((t : ℂ) - z)⁻¹) ∂ν =
        z * (((ν.real Set.univ : ℝ)) : ℂ) +
          (1 + z ^ 2) * ∫ t, ((t : ℂ) - z)⁻¹ ∂ν := by
    rw [integral_add (integrable_const z)
      ((integrable_cauchyKernel ν hz).const_mul (1 + z ^ 2)),
      integral_const, integral_const_mul]
    simp [Measure.real, mul_comm]
  rw [← hsplit]
  -- Transfer the weighted integral back to `μ` and match integrands pointwise.
  rw [hν, nevanlinnaWeightedMeasure,
    integral_withDensity_eq_integral_smul hdensmeas]
  apply integral_congr_ae
  filter_upwards with t
  have hwpos : 0 ≤ nevanlinnaWeight t * Real.exp (u t) :=
    le_of_lt (mul_pos (nevanlinnaWeight_pos t) (Real.exp_pos _))
  have htonn : ((Real.toNNReal (nevanlinnaWeight t * Real.exp (u t)) : ℝ) : ℂ) =
      ((nevanlinnaWeight t : ℝ) : ℂ) * ((Real.exp (u t) : ℝ) : ℂ) := by
    rw [Real.coe_toNNReal _ hwpos]
    push_cast
    ring
  rw [regularizedHerglotzKernel_eq hz t]
  rw [NNReal.smul_def, Complex.real_smul, htonn]
  have hden : (t : ℂ) - z ≠ 0 := real_sub_ne_zero_of_im_ne_zero hz t
  field_simp

/-- The Cauchy transform of a measure at a spectral parameter.  This is the transform the
probability-carrier freeness layer is stated in. -/
def cauchyTransform (ν : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ t, ((t : ℂ) - z)⁻¹ ∂ν

/-- Rescaling a measure rescales its Cauchy transform by the same factor. -/
theorem cauchyTransform_smul (c : ℝ≥0∞) (ν : Measure ℝ) (z : ℂ) :
    cauchyTransform (c • ν) z = (c.toReal : ℂ) * cauchyTransform ν z := by
  rw [cauchyTransform, cauchyTransform, integral_smul_measure]
  simp [Complex.real_smul]

/-- Total mass of a rescaled probability measure. -/
theorem real_univ_smul_probability (c : ℝ≥0∞) (P : Measure ℝ)
    [IsProbabilityMeasure P] : (c • P).real Set.univ = c.toReal := by
  simp [Measure.real, Measure.smul_apply, smul_eq_mul, measure_univ]

/-- **Normalized form of the regularized transform.**  Once the Nevanlinna-weighted measure is
written as a mass times a probability measure, the regularized Herglotz transform is that mass
times a single rational gauge of the probability Cauchy transform used by the carrier freeness
layer.  The gauge `w ↦ z + (1 + z ^ 2) * w` is invertible over `ℂ(z)`, so it generates the same
differential field. -/
theorem regularizedHerglotzTransform_eq_mass_mul_gauge
    (μ : Measure ℝ) (u : ℝ → ℝ) (hu : Measurable u) {z : ℂ} (hz : z.im ≠ 0)
    [IsFiniteMeasure (nevanlinnaWeightedMeasure μ u)]
    (c : ℝ≥0∞) (P : Measure ℝ) [IsProbabilityMeasure P]
    (hdecomp : nevanlinnaWeightedMeasure μ u = c • P) :
    ∫ t, regularizedHerglotzKernel t z * (Real.exp (u t) : ℂ) ∂μ =
      (c.toReal : ℂ) * (z + (1 + z ^ 2) * cauchyTransform P z) := by
  have hmain := regularizedHerglotzTransform_eq μ u hu hz
  rw [hmain, hdecomp, real_univ_smul_probability c P]
  have hcauchy : ∫ t, ((t : ℂ) - z)⁻¹ ∂(c • P) =
      (c.toReal : ℂ) * cauchyTransform P z := cauchyTransform_smul c P z
  rw [hcauchy]
  ring

/-- Every nonzero finite measure is its total mass times a probability measure. -/
theorem exists_mass_probability_decomposition
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hne : ν ≠ 0) :
    ∃ P : Measure ℝ, IsProbabilityMeasure P ∧ ν = (ν Set.univ) • P := by
  have hzero : ν Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hne
  have htop : ν Set.univ ≠ ⊤ := measure_ne_top ν Set.univ
  refine ⟨(ν Set.univ)⁻¹ • ν, ?_, ?_⟩
  · constructor
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hzero htop
  · rw [smul_smul, ENNReal.mul_inv_cancel hzero htop, one_smul]

/-- **Standalone normalized form.**  For any measure whose Nevanlinna-weighted reweighting is
finite and nonzero, the regularized Herglotz transform is a positive multiple of a single rational
gauge of the Cauchy transform of an honest probability measure — the exact object the carrier
freeness layer is stated about.  No decomposition is assumed; it is constructed. -/
theorem exists_probability_regularizedHerglotzTransform_eq
    (μ : Measure ℝ) (u : ℝ → ℝ) (hu : Measurable u)
    [IsFiniteMeasure (nevanlinnaWeightedMeasure μ u)]
    (hne : nevanlinnaWeightedMeasure μ u ≠ 0) :
    ∃ (c : ℝ≥0∞) (P : Measure ℝ), IsProbabilityMeasure P ∧
      ∀ z : ℂ, z.im ≠ 0 →
        ∫ t, regularizedHerglotzKernel t z * (Real.exp (u t) : ℂ) ∂μ =
          (c.toReal : ℂ) * (z + (1 + z ^ 2) * cauchyTransform P z) := by
  obtain ⟨P, hP, hdecomp⟩ :=
    exists_mass_probability_decomposition (nevanlinnaWeightedMeasure μ u) hne
  refine ⟨(nevanlinnaWeightedMeasure μ u) Set.univ, P, hP, ?_⟩
  intro z hz
  exact regularizedHerglotzTransform_eq_mass_mul_gauge μ u hu hz _ P hdecomp

/-- On a ball avoiding the real axis the imaginary part stays uniformly bounded away from zero. -/
theorem lt_abs_im_of_mem_ball {z₀ z : ℂ}
    (hz : z ∈ Metric.ball z₀ (|z₀.im| / 2)) :
    |z₀.im| / 2 < |z.im| := by
  rw [Metric.mem_ball, Complex.dist_eq] at hz
  have h1 : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
    simpa using Complex.abs_im_le_norm (z - z₀)
  have h2 : |z₀.im| - |z.im| ≤ |z₀.im - z.im| := abs_sub_abs_le_abs_sub _ _
  have h3 : |z₀.im - z.im| = |z.im - z₀.im| := abs_sub_comm _ _
  rw [h3] at h2
  linarith

/-- **Holomorphy of the Cauchy transform.**  Off the real axis the Cauchy transform of a finite
measure is complex differentiable, and its derivative is obtained by differentiating the kernel
under the integral.  Domination is by a constant, since the kernel is uniformly bounded on any
ball avoiding the axis. -/
theorem hasDerivAt_cauchyTransform (ν : Measure ℝ) [IsFiniteMeasure ν]
    {z₀ : ℂ} (hz₀ : z₀.im ≠ 0) :
    HasDerivAt (cauchyTransform ν) (∫ t, (((t : ℂ) - z₀)⁻¹) ^ 2 ∂ν) z₀ := by
  have himpos : 0 < |z₀.im| := abs_pos.mpr hz₀
  have hrpos : 0 < |z₀.im| / 2 := by linarith
  set s : Set ℂ := Metric.ball z₀ (|z₀.im| / 2) with hs
  have hsnhds : s ∈ nhds z₀ := Metric.ball_mem_nhds z₀ hrpos
  have hmemne : ∀ z ∈ s, z.im ≠ 0 := by
    intro z hz
    have := lt_abs_im_of_mem_ball hz
    intro hzero
    rw [hzero] at this
    simp at this
    linarith
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun t : ℝ => ((t : ℂ) - z)⁻¹) ν := by
    intro z
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hmeas2 : AEStronglyMeasurable (fun t : ℝ => (((t : ℂ) - z₀)⁻¹) ^ 2) ν := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hbound : ∀ᵐ t : ℝ ∂ν, ∀ z ∈ s,
      ‖(((t : ℂ) - z)⁻¹) ^ 2‖ ≤ (|z₀.im| / 2)⁻¹ ^ 2 := by
    filter_upwards with t z hz
    have hzne : z.im ≠ 0 := hmemne z hz
    have hlow : |z₀.im| / 2 < |z.im| := lt_abs_im_of_mem_ball hz
    have hker : ‖((t : ℂ) - z)⁻¹‖ ≤ |z.im|⁻¹ := norm_inv_real_sub_le hzne t
    have hstep : |z.im|⁻¹ ≤ (|z₀.im| / 2)⁻¹ := by
      apply inv_anti₀ hrpos (le_of_lt hlow)
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (le_trans hker hstep) 2
  have hdiff : ∀ᵐ t : ℝ ∂ν, ∀ z ∈ s,
      HasDerivAt (fun w : ℂ => ((t : ℂ) - w)⁻¹) ((((t : ℂ) - z)⁻¹) ^ 2) z := by
    filter_upwards with t z hz
    have hzne : z.im ≠ 0 := hmemne z hz
    have hden : (t : ℂ) - z ≠ 0 := real_sub_ne_zero_of_im_ne_zero hzne t
    have hbase : HasDerivAt (fun w : ℂ => (t : ℂ) - w) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub (t : ℂ)
    have hinv := hbase.inv hden
    have hfun :
        (fun w : ℂ => (t : ℂ) - w)⁻¹ =
          (fun w : ℂ => ((t : ℂ) - w)⁻¹) := by
      funext w
      rfl
    rw [hfun] at hinv
    apply hinv.congr_deriv
    field_simp [hden]
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := ν) (F := fun z t => ((t : ℂ) - z)⁻¹)
    (F' := fun z t => (((t : ℂ) - z)⁻¹) ^ 2)
    (bound := fun _ => (|z₀.im| / 2)⁻¹ ^ 2)
    hsnhds (Filter.Eventually.of_forall fun z => hmeas z)
    (integrable_cauchyKernel ν hz₀) hmeas2 hbound
    (integrable_const _) hdiff
  exact hmain.2

/-- The Cauchy transform of a finite measure is analytic on every open set avoiding the real
axis. -/
theorem analyticOnNhd_cauchyTransform (ν : Measure ℝ) [IsFiniteMeasure ν]
    {U : Set ℂ} (hU : IsOpen U) (hUne : ∀ z ∈ U, z.im ≠ 0) :
    AnalyticOnNhd ℂ (cauchyTransform ν) U := by
  apply DifferentiableOn.analyticOnNhd _ hU
  intro z hz
  exact ((hasDerivAt_cauchyTransform ν (hUne z hz)).differentiableAt).differentiableWithinAt

end

end GaloisForLFunctions.HTGeometry
