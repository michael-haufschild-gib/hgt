import GaloisForLFunctions.HTGeometry.QuadraticAdjoinSquareKernel
import GaloisForLFunctions.RHTower.XiLegendreHalvingCriterion
import GaloisForLFunctions.RHTower.XiGlobalKummerAugmentation

/-!
# Minimal halving fields of the actual source sections

Chosen roots in an algebraic closure of the infinite marked field define the
least intermediate fields admitting halves of the original and translated
sections. Their degrees are respectively two and four. The statements concern
actual affine-group halves, with source square-class assumptions discharged.
-/

noncomputable section
open GaloisForLFunctions.HTGeometry
open scoped IntermediateField
namespace RHTower.XiGlobalKummer
local instance : CharZero K := charZero_of_injective_algebraMap constPlane_injective
local instance (priority := high) (F : Type*) : DecidableEq F := Classical.decEq F

abbrev HalvingClosure := AlgebraicClosure Marked

def commonHalfRoot : HalvingClosure :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq
    (algebraMap Marked HalvingClosure xiMarked) (by decide : 0 < 2))

theorem commonHalfRoot_sq : commonHalfRoot * commonHalfRoot =
    algebraMap Marked HalvingClosure xiMarked := by
  simpa only [commonHalfRoot, pow_two] using
    (Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
      (algebraMap Marked HalvingClosure xiMarked) (by decide : 0 < 2)))

def labelledHalfRoot (n : ℕ) : HalvingClosure :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq
    (algebraMap Marked HalvingClosure (1 + sourceParameter n)) (by decide : 0 < 2))

theorem labelledHalfRoot_sq (n : ℕ) : labelledHalfRoot n * labelledHalfRoot n =
    algebraMap Marked HalvingClosure (1 + sourceParameter n) := by
  simpa only [labelledHalfRoot, pow_two] using
    (Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
      (algebraMap Marked HalvingClosure (1 + sourceParameter n)) (by decide : 0 < 2)))

def commonHalvingField : IntermediateField Marked HalvingClosure := Marked⟮commonHalfRoot⟯

def translatedHalvingField (n : ℕ) : IntermediateField Marked HalvingClosure :=
  IntermediateField.adjoin Marked ({commonHalfRoot, labelledHalfRoot n} : Set HalvingClosure)

/-- The same quadratic field is minimal for every original section. -/
theorem commonHalvingField_le_iff_has_half (E : IntermediateField Marked HalvingClosure) (n : ℕ) :
    commonHalvingField ≤ E ↔
      ∃ R : (sourceCurveOver E n).Point, R + R = sourceSectionOver E n := by
  exact (adjoin_root_le_iff_isSquare commonHalfRoot_sq E).trans
    (sourceSectionOver_has_half_iff E n).symm

/-- The common and the labelled radicals generate the minimal field for a translated half. -/
theorem translatedHalvingField_le_iff_has_half
    (E : IntermediateField Marked HalvingClosure) (n : ℕ) :
    translatedHalvingField n ≤ E ↔
      ∃ R : (sourceCurveOver E n).Point, R + R = translatedSectionOver E n := by
  have h : translatedHalvingField n ≤ E ↔
      IsSquare (algebraMap Marked E xiMarked) ∧
        IsSquare (algebraMap Marked E (1 + sourceParameter n)) := by
    unfold translatedHalvingField
    rw [IntermediateField.adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact and_congr (root_mem_iff_isSquare commonHalfRoot_sq E)
      (root_mem_iff_isSquare (labelledHalfRoot_sq n) E)
  exact h.trans (translatedSectionOver_has_half_iff E n).symm

theorem sourceSection_has_half_commonHalvingField (n : ℕ) :
    ∃ R : (sourceCurveOver commonHalvingField n).Point,
      R + R = sourceSectionOver commonHalvingField n :=
  (commonHalvingField_le_iff_has_half commonHalvingField n).mp le_rfl

theorem translatedSection_has_half_translatedHalvingField (n : ℕ) :
    ∃ R : (sourceCurveOver (translatedHalvingField n) n).Point,
      R + R = translatedSectionOver (translatedHalvingField n) n :=
  (translatedHalvingField_le_iff_has_half (translatedHalvingField n) n).mp le_rfl

theorem commonHalvingField_finrank : Module.finrank Marked commonHalvingField = 2 :=
  finrank_adjoin_eq_two commonHalfRoot_sq
    (root_not_mem_bot_of_not_isSquare commonHalfRoot_sq xi_not_isSquare_markedExtension)

theorem translatedHalvingField_finrank (n : ℕ) :
    Module.finrank Marked (translatedHalvingField n) = 4 :=
  finrank_adjoin_two_roots_eq_four (by norm_num) commonHalfRoot_sq (labelledHalfRoot_sq n)
    xi_not_isSquare_markedExtension (sourceLambda_not_isSquare n)
    (xiMarked_mul_sourceLambda_not_isSquare n)

end RHTower.XiGlobalKummer
