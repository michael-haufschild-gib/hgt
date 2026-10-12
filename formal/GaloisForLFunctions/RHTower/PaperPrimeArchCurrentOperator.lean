import GaloisForLFunctions.RHTower.PaperPrimeArchCurrentBounds
import GaloisForLFunctions.HTGeometry.LpContinuousMultiplierOrder
import GaloisForLFunctions.HTGeometry.PaperModulationOrder

/-!
# The full signed source on the frequency continuum

The original prime–archimedean current acts by multiplication on Lebesgue L².
Its norm, spectrum and order retain all source values. Compact corrections cannot
supply a missing sign, although the source decays exponentially at both ends.
-/

namespace RHTower.PaperPrimeArch
noncomputable section
open GaloisForLFunctions.HTGeometry MeasureTheory Classical
open scoped ENNReal

abbrev Space := Lp ℂ 2 (volume : Measure ℝ)

def operator (a : Height) : Space →L[ℂ] Space :=
  lpBoundedMulCLM (Complex.continuous_ofReal.comp (continuous_current a)).measurable
    decayBudget_nonneg (norm_current_le a)

theorem operator_apply_ae (a : Height) (f : Space) :
    (operator a f : ℝ → ℂ) =ᵐ[volume] fun x => (current a x : ℂ) * f x :=
  lpBoundedMulCLM_coeFn _ _ _ f

def commutant (a : Height) : paperModulationCommutant :=
  ⟨operator a, mem_paperModulationCommutant_of_mul _ _ (operator_apply_ae a)⟩

theorem operator_selfAdjoint (a : Height) : IsSelfAdjoint (operator a) :=
  lpBoundedRealMul_selfAdjoint (continuous_current a) decayBudget_nonneg (norm_current_le a)

theorem operator_positive_iff (a : Height) :
    (operator a).IsPositive ↔ ∀ x, 0 ≤ current a x :=
  lpBoundedRealMul_positive_iff (continuous_current a) decayBudget_nonneg (norm_current_le a)

theorem forall_operator_positive_iff_rh :
    (∀ a : Height, (operator a).IsPositive) ↔ RiemannHypothesis := by
  simp_rw [operator_positive_iff]
  exact forall_current_nonneg_iff_rh

/-- Even arbitrary compact corrections leave the exact arithmetic sign criterion. -/
theorem forall_exists_compact_positive_iff_rh :
    (∀ a : Height, ∃ K : compactOperatorStarAlgebra Space,
      (operator a + K.1).IsPositive) ↔ RiemannHypothesis := by
  have h (a : Height) := paperModulationCommutant_exists_compact_positive_iff
    (commutant a) (operator_selfAdjoint a)
  simp only [commutant] at h
  simp_rw [h]
  exact forall_operator_positive_iff_rh

theorem norm_source_le_operator_norm (a : Height) (x : ℝ) :
    |current a x| ≤ ‖operator a‖ := by
  simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using
    norm_symbol_le_of_ae_mul_continuous
      (Complex.continuous_ofReal.comp (continuous_current a)) (operator_apply_ae a) x

theorem operator_norm_essSup (a : Height) :
    ENNReal.ofReal ‖operator a‖ =
      essSup (fun x => ENNReal.ofReal |current a x|) volume := by
  simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using
    ofReal_norm_eq_essSup_of_ae_mul_continuous
      (Complex.continuous_ofReal.comp (continuous_current a)) (operator_apply_ae a)

theorem operator_spectrum (a : Height) :
    spectrum ℂ (operator a) = closure (Set.range fun x => (current a x : ℂ)) :=
  spectrum_eq_closure_range_of_ae_mul_continuous
    (Complex.continuous_ofReal.comp (continuous_current a)) (operator_apply_ae a)

theorem operator_eq_zero_iff (a : Height) : operator a = 0 ↔ current a = 0 := by
  constructor
  · intro h
    funext x
    have hx := norm_source_le_operator_norm a x
    rw [h, norm_zero] at hx
    exact abs_eq_zero.mp (le_antisymm hx (abs_nonneg _))
  · intro h
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [operator_apply_ae a f] with x hx
    simpa [h] using hx

theorem operator_compactIdealDistance (a : Height) :
    compactIdealDistance (operator a) = ‖operator a‖ :=
  paperModulationCommutant_compactIdealDistance (commutant a)

theorem operator_compact_iff_zero (a : Height) :
    IsCompactOperator (operator a) ↔ operator a = 0 := by
  constructor
  · intro h
    exact congrArg Subtype.val
      ((paperModulationCommutant_compact_iff_zero (commutant a)).mp h)
  · intro h
    rw [h]
    exact isCompactOperator_zero

theorem operator_traceCost (a : Height) :
    compactOperatorTraceCost Space (operator a) = if current a = 0 then 0 else ∞ := by
  classical
  rw [compactOperatorTraceCost_eq, operator_compact_iff_zero, operator_eq_zero_iff]

theorem operator_traceCost_add_compact (a : Height) (K : compactOperatorStarAlgebra Space) :
    compactOperatorTraceCost Space (operator a + K.1) =
      if current a = 0 then 0 else ∞ := by
  rw [compactOperatorTraceCost_add_compact, operator_traceCost]

theorem source_le_norm_sub_compact (a : Height) (x : ℝ)
    (K : compactOperatorStarAlgebra Space) :
    |current a x| ≤ ‖operator a - K.1‖ :=
  (norm_source_le_operator_norm a x).trans
    (paperModulationCommutant_norm_le_sub_compact (commutant a) K)

end
end RHTower.PaperPrimeArch
