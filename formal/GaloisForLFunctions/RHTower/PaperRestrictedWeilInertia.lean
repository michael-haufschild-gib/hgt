import GaloisForLFunctions.RHTower.PaperRestrictedWeilSource
import GaloisForLFunctions.HTGeometry.PaperNegativePartInertia
import GaloisForLFunctions.HTGeometry.PaperCompactThresholdSpectrum

/-! # Exact negative index and optimal repair of the full restricted-Weil form

Every energy has a finite negative index. This is exactly the minimum rank of
any bounded correction making the actual form positive, including corrections
which mix coordinates. The canonical positive correction attains that rank.
-/

noncomputable section

open scoped CStarAlgebra

namespace RHTower.PaperRestrictedWeil

open GaloisForLFunctions.HTGeometry

abbrev negativeSpace (a : SuzukiPositiveAperture) (E : ℝ) : Submodule ℂ (Space a) :=
  PaperNegativePart.negativeSpace (operator a E)

instance negativeSpace_finiteDimensional (a : SuzukiPositiveAperture) (E : ℝ) :
    FiniteDimensional ℂ (negativeSpace a E) :=
  PaperNegativePart.finiteDimensional_negativeSpace (operator a E) (operator_selfAdjoint a E)
    (one_sub_operator_compact a E)

def negativeRank (a : SuzukiPositiveAperture) (E : ℝ) : ℕ :=
  Module.finrank ℂ (negativeSpace a E)

def repair (a : SuzukiPositiveAperture) (E : ℝ) : Space a →L[ℂ] Space a :=
  PaperNegativePart.repair (operator a E)

theorem repair_positive (a : SuzukiPositiveAperture) (E : ℝ) :
    (repair a E).IsPositive := PaperNegativePart.repair_positive (operator a E)

theorem repaired_positive (a : SuzukiPositiveAperture) (E : ℝ) :
    (operator a E + repair a E).IsPositive :=
  PaperNegativePart.repaired_positive (operator a E) (operator_selfAdjoint a E)

theorem repair_rank (a : SuzukiPositiveAperture) (E : ℝ) :
    HasRankLE (repair a E) (negativeRank a E) :=
  PaperNegativePart.hasRankLE_repair (operator a E)

theorem repair_compact (a : SuzukiPositiveAperture) (E : ℝ) :
    IsCompactOperator (repair a E) := isCompactOperator_of_hasRankLE (repair_rank a E)

theorem repair_norm_le (a : SuzukiPositiveAperture) (E : ℝ) :
    ‖repair a E‖ ≤ 1 + |E| + ‖ccmRestrictedWeilBoundedRemainder a‖ :=
  (PaperNegativePart.norm_repair_le (operator a E)).trans (operator_norm_le a E)

theorem positive_repair_rank_iff (a : SuzukiPositiveAperture) (E : ℝ) (r : ℕ) :
    (∃ F : Space a →L[ℂ] Space a, HasRankLE F r ∧
      (operator a E + F).IsPositive) ↔ negativeRank a E ≤ r :=
  PaperNegativePart.positive_repair_rank_iff (operator a E) (operator_selfAdjoint a E) r

theorem repair_exact_rank (a : SuzukiPositiveAperture) (E : ℝ) (r : ℕ) :
    HasRankLE (repair a E) r ↔ negativeRank a E ≤ r :=
  PaperNegativePart.repair_exact_rank (operator a E) (operator_selfAdjoint a E) r

theorem exists_finite_positive_repair (a : SuzukiPositiveAperture) (E : ℝ) :
    ∃ r : ℕ, ∃ F : Space a →L[ℂ] Space a,
      F.IsPositive ∧ HasRankLE F r ∧ (operator a E + F).IsPositive :=
  ⟨negativeRank a E, repair a E, repair_positive a E, repair_rank a E,
    repaired_positive a E⟩

theorem negativeRank_eq_zero_iff (a : SuzukiPositiveAperture) (E : ℝ) :
    negativeRank a E = 0 ↔ (operator a E).IsPositive :=
  PaperNegativePart.negativeRank_eq_zero_iff (operator a E) (operator_selfAdjoint a E)

theorem negativeSpace_eq_aboveOneSpace (a : SuzukiPositiveAperture) (E : ℝ) :
    negativeSpace a E =
      PaperNegativePart.aboveOneSpace (ccmRestrictedWeilFormBirmanSchwinger a E) :=
  PaperNegativePart.negativeSpace_eq_aboveOneSpace (ccmRestrictedWeilFormBirmanSchwinger a E)
    (ccmRestrictedWeilFormBirmanSchwinger_isSelfAdjoint a E)
    (isCompactOperator_ccmRestrictedWeilFormBirmanSchwinger a E)

theorem negativeRank_eq_spectral_dimension (a : SuzukiPositiveAperture) (E : ℝ) :
    negativeRank a E = Module.finrank ℂ
      (PaperNegativePart.aboveOneSpace (ccmRestrictedWeilFormBirmanSchwinger a E)) := by
  rw [negativeRank, negativeSpace_eq_aboveOneSpace]

theorem exact_source_negative_index (a : SuzukiPositiveAperture) (E : ℝ) :
    (∀ W : Submodule ℂ (Space a),
      (∀ u ∈ W, u ≠ 0 → ccmRestrictedWeilSourceQuadratic a u -
        E * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 < 0) →
      FiniteDimensional ℂ W ∧ Module.finrank ℂ W ≤ negativeRank a E) ∧
    ∃ W : Submodule ℂ (Space a), Module.finrank ℂ W = negativeRank a E ∧
      ∀ u ∈ W, u ≠ 0 → ccmRestrictedWeilSourceQuadratic a u -
        E * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 < 0 := by
  simpa only [operator_quadratic, negativeRank, PaperNegativePart.negativeRank, negativeSpace] using
    PaperNegativePart.exact_negative_index (operator a E) (operator_selfAdjoint a E)

theorem negativeRank_monotone (a : SuzukiPositiveAperture) : Monotone (negativeRank a) := by
  intro E₁ E₂ hE
  apply PaperNegativePart.negativeRank_mono_of_form_le (operator a E₁) (operator a E₂)
    (operator_selfAdjoint a E₁) (operator_selfAdjoint a E₂)
  intro u
  rw [operator_quadratic, operator_quadratic]
  nlinarith [sq_nonneg ‖ccmArchimedeanFormToAperture a u‖]

end RHTower.PaperRestrictedWeil
