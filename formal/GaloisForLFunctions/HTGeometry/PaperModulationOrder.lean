import GaloisForLFunctions.HTGeometry.PaperModulationCalkin
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Order survives compact corrections of the modulation commutant

Conjugating a compact correction by escaping modulations removes it strongly.
The real quadratic form of the original operator therefore retains every lower bound.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory Filter
open scoped Topology

private abbrev H := Lp ℂ 2 (volume : Measure ℝ)

theorem inner_modulationMul (t : ℝ) (f g : H) :
    inner ℂ (modulationMul t f) (modulationMul t g) = inner ℂ f g :=
  (LinearMap.norm_map_iff_inner_map_map (modulationMul t)).mp
    (norm_modulationMul_eq t) f g

theorem paperModulationCommutant_corrected_tendsto (A : paperModulationCommutant)
    (K : compactOperatorStarAlgebra H) (f : H) :
    Tendsto (fun n : ℕ => modulationMul (-(n : ℝ))
      ((A.1 + K.1) (modulationMul (n : ℝ) f))) atTop (𝓝 (A.1 f)) := by
  have h := (tendsto_const_nhds (x := A.1 f)).add
    (modulationMul_compact_conjugation_tendsto K f)
  simpa only [add_apply, map_add,
    (mem_paperModulationCommutant_iff A.1).mp A.2,
    modulationMul_neg_modulationMul, add_zero] using h

/-- Every quadratic lower bound of a compact correction already holds before correction. -/
theorem paperModulationCommutant_form_lower_bound (A : paperModulationCommutant)
    (K : compactOperatorStarAlgebra H) (c : ℝ)
    (h : ∀ f : H, c * ‖f‖ ^ 2 ≤ (inner ℂ f ((A.1 + K.1) f)).re) (f : H) :
    c * ‖f‖ ^ 2 ≤ (inner ℂ f (A.1 f)).re := by
  have ht : Tendsto (fun n : ℕ => inner ℂ f (modulationMul (-(n : ℝ))
      ((A.1 + K.1) (modulationMul (n : ℝ) f)))) atTop (𝓝 (inner ℂ f (A.1 f))) :=
    (tendsto_const_nhds (x := f)).inner
      (paperModulationCommutant_corrected_tendsto A K f)
  apply ge_of_tendsto' (Complex.continuous_re.continuousAt.tendsto.comp ht)
  intro n
  simp only [Function.comp_apply]
  have hi := inner_modulationMul (-(n : ℝ)) (modulationMul (n : ℝ) f)
    ((A.1 + K.1) (modulationMul (n : ℝ) f))
  rw [modulationMul_neg_modulationMul] at hi
  rw [hi]
  simpa only [norm_modulationMul_eq] using h (modulationMul (n : ℝ) f)

theorem paperModulationCommutant_positive_of_compact (A : paperModulationCommutant)
    (hA : IsSelfAdjoint A.1) (K : compactOperatorStarAlgebra H)
    (h : (A.1 + K.1).IsPositive) : A.1.IsPositive := by
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨hA, fun f => ?_⟩
  have hn := paperModulationCommutant_form_lower_bound A K 0
    (fun g => by simpa only [zero_mul, RCLike.re_eq_complex_re]
      using h.re_inner_nonneg_right g) f
  simpa only [zero_mul, ContinuousLinearMap.reApplyInnerSelf_apply,
    inner_re_symm (𝕜 := ℂ), RCLike.re_eq_complex_re] using hn

/-- Compact repairs do not enlarge the positive cone of self-adjoint multipliers. -/
theorem paperModulationCommutant_exists_compact_positive_iff (A : paperModulationCommutant)
    (hA : IsSelfAdjoint A.1) :
    (∃ K : compactOperatorStarAlgebra H, (A.1 + K.1).IsPositive) ↔ A.1.IsPositive := by
  constructor
  · rintro ⟨K, hK⟩
    exact paperModulationCommutant_positive_of_compact A hA K hK
  · intro h
    exact ⟨0, by simpa using h⟩

end
end GaloisForLFunctions.HTGeometry
