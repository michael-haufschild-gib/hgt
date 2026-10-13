import GaloisForLFunctions.RHTower.PaperPrimeArchExactObservation
import GaloisForLFunctions.RHTower.PaperPrimeArchCurrentRigidity
import GaloisForLFunctions.HTGeometry.L2PhysicalObservationModulus

/-! # Positive absolute current with identical full norm observations

The actual signed source and its absolute current have identical physical-hull
observations, operator norm and compact-ideal distance. The latter is positive
unconditionally. Both retain infinite proven paper ideal cost.
-/

namespace RHTower.PaperPrimeArch
noncomputable section
open MeasureTheory GaloisForLFunctions.HTGeometry
open scoped ENNReal

theorem norm_absoluteCurrent_le (a : Height) (t : ℝ) : ‖((|current a t| : ℝ) : ℂ)‖ ≤ decayBudget := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_abs] using norm_current_le a t

def absoluteOperator (a : Height) : Space →L[ℂ] Space :=
  lpBoundedMulCLM (Complex.continuous_ofReal.comp (continuous_current a).abs).measurable
    decayBudget_nonneg (norm_absoluteCurrent_le a)

theorem absoluteOperator_apply_ae (a : Height) (f : Space) :
    (absoluteOperator a f : ℝ → ℂ) =ᵐ[volume] fun t => ((|current a t| : ℝ) : ℂ) * f t :=
  lpBoundedMulCLM_coeFn _ _ _ f

theorem absoluteOperator_positive (a : Height) : (absoluteOperator a).IsPositive :=
  (lpBoundedRealMul_positive_iff (continuous_current a).abs decayBudget_nonneg
    (norm_absoluteCurrent_le a)).mpr (fun _ => abs_nonneg _)

theorem absoluteOperator_physicalObservation (a : Height) (x : Space) :
    l2PhysicalObservation (absoluteOperator a) x = l2PhysicalObservation (operator a) x := by
  apply l2PhysicalObservation_eq_of_ae_mul_norm_eq _ _ _ _
    (absoluteOperator_apply_ae a) (operator_apply_ae a)
  exact Filter.Eventually.of_forall (fun t => by simp only [Complex.norm_real, Real.norm_eq_abs, abs_abs])

theorem absoluteOperator_response_norm (a : Height) (x : Space) :
    ‖absoluteOperator a x‖ = ‖operator a x‖ := by
  calc
    ‖absoluteOperator a x‖ = l2PhysicalObservation (absoluteOperator a) x :=
      (l2PhysicalObservation_eq_norm_of_ae_mul _ _ (absoluteOperator_apply_ae a) x).symm
    _ = l2PhysicalObservation (operator a) x := absoluteOperator_physicalObservation a x
    _ = ‖operator a x‖ := operator_physicalObservation a x

theorem absoluteOperator_norm (a : Height) : ‖absoluteOperator a‖ = ‖operator a‖ := by
  apply le_antisymm
  · apply (absoluteOperator a).opNorm_le_bound (norm_nonneg _)
    intro x
    rw [absoluteOperator_response_norm]
    exact (operator a).le_opNorm x
  · apply (operator a).opNorm_le_bound (norm_nonneg _)
    intro x
    rw [← absoluteOperator_response_norm]
    exact (absoluteOperator a).le_opNorm x

def absoluteCommutant (a : Height) : paperModulationCommutant :=
  ⟨absoluteOperator a, mem_paperModulationCommutant_of_mul _ _ (absoluteOperator_apply_ae a)⟩

theorem absoluteOperator_compactIdealDistance (a : Height) :
    compactIdealDistance (absoluteOperator a) = ‖operator a‖ :=
  (paperModulationCommutant_compactIdealDistance (absoluteCommutant a)).trans (absoluteOperator_norm a)

theorem absoluteOperator_ne_zero (a : Height) : absoluteOperator a ≠ 0 := by
  intro h
  have hn := absoluteOperator_norm a
  rw [h, norm_zero] at hn
  exact operator_ne_zero a (norm_eq_zero.mp hn.symm)

theorem absoluteOperator_not_compact (a : Height) : ¬ IsCompactOperator (absoluteOperator a) := by
  intro h
  exact absoluteOperator_ne_zero a (congrArg Subtype.val
    ((paperModulationCommutant_compact_iff_zero (absoluteCommutant a)).mp h))

theorem absoluteOperator_traceCost (a : Height) :
    compactOperatorTraceCost Space (absoluteOperator a) = ∞ := by
  rw [compactOperatorTraceCost_eq, if_neg (absoluteOperator_not_compact a)]

theorem absoluteOperator_add_compact_traceCost (a : Height) (K : compactOperatorStarAlgebra Space) :
    compactOperatorTraceCost Space (absoluteOperator a + K.1) = ∞ := by
  rw [compactOperatorTraceCost_add_compact, absoluteOperator_traceCost]

theorem absoluteOperator_same_observations_positive (a : Height) :
    (absoluteOperator a).IsPositive ∧
    (∀ x, l2PhysicalObservation (absoluteOperator a) x = l2PhysicalObservation (operator a) x) ∧
    compactOperatorTraceCost Space (absoluteOperator a) = ∞ ∧
    compactOperatorTraceCost Space (operator a) = ∞ :=
  ⟨absoluteOperator_positive a, absoluteOperator_physicalObservation a,
    absoluteOperator_traceCost a, operator_traceCost_top a⟩

end
end RHTower.PaperPrimeArch
