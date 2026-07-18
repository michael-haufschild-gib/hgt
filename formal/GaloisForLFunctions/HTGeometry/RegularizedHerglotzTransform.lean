import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Measure.WithDensity

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

end

end GaloisForLFunctions.HTGeometry
