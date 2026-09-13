import GaloisForLFunctions.HTGeometry.TranslationModulus

/-!
# Smooth directional variation and translation control

This is the smooth one-dimensional specialization of the first inequality in Lemma 3.1.  It
extends the corpus's nonnegative translation estimate to arbitrary signed displacements and then
packages scalar directions homogeneously.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- Smooth scalar directional variation: `|u|` times total variation in direction one. -/
noncomputable def smoothDirectionalVariation (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  |u| * ∫ x, ‖deriv f x‖

/-- Arbitrary signed translations satisfy the smooth total-variation bound. -/
theorem integral_norm_translation_le_abs (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hfc : Continuous (deriv f)) (hfi : Integrable (deriv f)) (h : ℝ)
    (htrans : Integrable (fun x => ‖f (x + h) - f x‖)) :
    ∫ x, ‖f (x + h) - f x‖ ≤ |h| * ∫ x, ‖deriv f x‖ := by
  by_cases hh : 0 ≤ h
  · simpa [abs_of_nonneg hh] using integral_norm_translation_le f hf hfc hfi hh htrans
  · have hh' : h < 0 := lt_of_not_ge hh
    let q := -h
    have hq : 0 ≤ q := by dsimp [q]; linarith
    have hshiftInt := htrans.comp_add_right q
    have hqInt : Integrable (fun x => ‖f (x + q) - f x‖) := by
      simpa only [q, add_assoc, neg_add_cancel, add_zero, Real.norm_eq_abs,
        abs_sub_comm] using hshiftInt
    have hbound := integral_norm_translation_le f hf hfc hfi hq hqInt
    have heq : (∫ x, ‖f (x + h) - f x‖) = ∫ x, ‖f (x + q) - f x‖ := by
      calc
        (∫ x, ‖f (x + h) - f x‖) =
            ∫ x, ‖f ((x + q) + h) - f (x + q)‖ := by
          symm
          exact MeasureTheory.integral_add_right_eq_self
            (fun x => ‖f (x + h) - f x‖) q
        _ = ∫ x, ‖f (x + q) - f x‖ := by
          congr 1
          funext x
          dsimp [q]
          rw [add_assoc, neg_add_cancel, add_zero]
          exact abs_sub_comm _ _
    rw [heq]
    simpa [q, abs_of_neg hh'] using hbound

/-- Paper's directional translation inequality for smooth scalar functions. -/
theorem integral_norm_directional_translation_le (f : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hfc : Continuous (deriv f)) (hfi : Integrable (deriv f))
    (u h : ℝ) (htrans : Integrable (fun x => ‖f (x + h * u) - f x‖)) :
    ∫ x, ‖f (x + h * u) - f x‖ ≤ |h| * smoothDirectionalVariation f u := by
  have hbound := integral_norm_translation_le_abs f hf hfc hfi (h * u) htrans
  rw [smoothDirectionalVariation]
  rw [abs_mul] at hbound
  simpa only [mul_assoc] using hbound

/-- Direction reversal leaves smooth directional variation unchanged. -/
@[simp] theorem smoothDirectionalVariation_neg (f : ℝ → ℝ) (u : ℝ) :
    smoothDirectionalVariation f (-u) = smoothDirectionalVariation f u := by
  simp [smoothDirectionalVariation]

/-- Positive homogeneity in the direction, matching distributional directional variation. -/
theorem smoothDirectionalVariation_smul (f : ℝ → ℝ) (c u : ℝ) :
    smoothDirectionalVariation f (c * u) = |c| * smoothDirectionalVariation f u := by
  simp [smoothDirectionalVariation, abs_mul, mul_assoc]

end GaloisForLFunctions.HTGeometry

