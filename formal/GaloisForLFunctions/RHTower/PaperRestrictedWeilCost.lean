import GaloisForLFunctions.RHTower.PaperRestrictedWeilInertia
import GaloisForLFunctions.RHTower.PaperRestrictedWeilDimension
import GaloisForLFunctions.HTGeometry.PaperCompactIdentityDistance
import GaloisForLFunctions.HTGeometry.PaperCompactIdealTrace

/-! # Ideal cost forgets the finite negative index of the actual Weil source

The proven compact-ideal weight sees zero cost for the spectral pencil and the
canonical repair, but infinite cost and essential norm one for both the full
signed source and its repaired positive operator, at every aperture and energy.
-/

noncomputable section

open scoped ENNReal

namespace RHTower.PaperRestrictedWeil

open GaloisForLFunctions.HTGeometry

theorem birmanSchwinger_ideal_cost (a : SuzukiPositiveAperture) (E : ℝ) :
    compactOperatorTraceCost (Space a) (ccmRestrictedWeilFormBirmanSchwinger a E) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).2
    (isCompactOperator_ccmRestrictedWeilFormBirmanSchwinger a E)

theorem repair_ideal_cost (a : SuzukiPositiveAperture) (E : ℝ) :
    compactOperatorTraceCost (Space a) (repair a E) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).2 (repair_compact a E)

theorem operator_compactIdealDistance (a : SuzukiPositiveAperture) (E : ℝ) :
    compactIdealDistance (operator a E) = 1 :=
  compactIdealDistance_identity_sub (formDomain_not_finiteDimensional a) _
    (isCompactOperator_ccmRestrictedWeilFormBirmanSchwinger a E)

theorem operator_not_compact (a : SuzukiPositiveAperture) (E : ℝ) :
    ¬ IsCompactOperator (operator a E) := by
  intro h
  have hz := compactIdealDistance_eq_zero_of_isCompactOperator _ h
  rw [operator_compactIdealDistance] at hz
  exact one_ne_zero hz

theorem operator_ideal_cost (a : SuzukiPositiveAperture) (E : ℝ) :
    compactOperatorTraceCost (Space a) (operator a E) = ∞ :=
  (compactOperatorTraceCost_eq_top_iff _).2 (operator_not_compact a E)

theorem operator_add_compact_distance (a : SuzukiPositiveAperture) (E : ℝ)
    (K : compactOperatorStarAlgebra (Space a)) :
    compactIdealDistance (operator a E + K.val) = 1 := by
  rw [compactIdealDistance_add_compact _ _ K.property, operator_compactIdealDistance]

theorem operator_add_compact_cost (a : SuzukiPositiveAperture) (E : ℝ)
    (K : compactOperatorStarAlgebra (Space a)) :
    compactOperatorTraceCost (Space a) (operator a E + K.val) = ∞ := by
  rw [compactOperatorTraceCost_add_compact, operator_ideal_cost]

theorem repaired_compactIdealDistance (a : SuzukiPositiveAperture) (E : ℝ) :
    compactIdealDistance (operator a E + repair a E) = 1 :=
  operator_add_compact_distance a E ⟨_, repair_compact a E⟩

theorem repaired_ideal_cost (a : SuzukiPositiveAperture) (E : ℝ) :
    compactOperatorTraceCost (Space a) (operator a E + repair a E) = ∞ :=
  operator_add_compact_cost a E ⟨_, repair_compact a E⟩

theorem one_le_distance_from_compact (a : SuzukiPositiveAperture) (E : ℝ)
    (K : compactOperatorStarAlgebra (Space a)) :
    1 ≤ ‖operator a E - K.val‖ := by
  rw [← operator_compactIdealDistance a E]
  exact compactIdealDistance_le _ _ K.property

end RHTower.PaperRestrictedWeil
