import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Rescaling a line parametrisation

Composing with `y ↦ a y`, `a ≠ 0`, preserves square-integrability on `ℝ` and rescales the mass by
`|a|⁻¹`.  This converts between the two natural parametrisations of a vertical line, `w = σ + iy`
and `w = σ + 2πiξ`, used respectively by contour integration and by the Fourier transform.

## Main results

* `memLp_two_comp_const_mul`
* `integral_norm_sq_comp_const_mul`
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set

noncomputable section

theorem quasiMeasurePreserving_const_mul {a : ℝ} (ha : a ≠ 0) :
    Measure.QuasiMeasurePreserving (fun y : ℝ => a * y) volume volume := by
  refine ⟨by fun_prop, ?_⟩
  rw [Real.map_volume_mul_left ha]
  exact Measure.smul_absolutelyContinuous

theorem memLp_two_comp_const_mul {g : ℝ → ℂ} (hg : MemLp g 2 (volume : Measure ℝ))
    {a : ℝ} (ha : a ≠ 0) : MemLp (fun y : ℝ => g (a * y)) 2 (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (fun y : ℝ => g (a * y)) volume :=
    hg.aestronglyMeasurable.comp_quasiMeasurePreserving (quasiMeasurePreserving_const_mul ha)
  refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  have hint : Integrable (fun x : ℝ => ‖g x‖ ^ (2 : ℕ)) volume :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  exact (integrable_comp_mul_left_iff (fun x : ℝ => ‖g x‖ ^ (2 : ℕ)) ha).2 hint

theorem integral_norm_sq_comp_const_mul (g : ℝ → ℂ) (a : ℝ) :
    (∫ y : ℝ, ‖g (a * y)‖ ^ (2 : ℕ)) = |a|⁻¹ * ∫ x : ℝ, ‖g x‖ ^ (2 : ℕ) := by
  have h := MeasureTheory.Measure.integral_comp_mul_left (fun x : ℝ => ‖g x‖ ^ (2 : ℕ)) a
  simpa [smul_eq_mul] using h

end

end GaloisForLFunctions.HTGeometry
