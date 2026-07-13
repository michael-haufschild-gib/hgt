import GaloisForLFunctions.HTGeometry.MeromorphicTranslation
import GaloisForLFunctions.HTGeometry.DifferenceDifferential

/-!
# Translation and constant-coefficient operators on the global meromorphic field

Additive translation commutes with every differential jet and hence with every
constant-coefficient differential operator on the global meromorphic fraction field.
-/

open Set
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance translationDifferentialOperatorDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance translationDifferentialOperatorComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance translationDifferentialOperatorComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance translationDifferentialOperatorDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

/-- Additive translation commutes with every differential jet in the meromorphic field. -/
theorem addTranslationMeroEquiv_differentialJet
    (q : ℂ) (n : ℕ) (x : meroField Set.univ) :
    addTranslationMeroEquiv q (differentialJet n x) =
      differentialJet n (addTranslationMeroEquiv q x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [differentialJet_succ, differentialJet_succ,
        addTranslationMeroEquiv_deriv, ih]

/-- Additive translation commutes with every constant-coefficient differential operator. -/
theorem addTranslationMeroEquiv_differentialOperatorApply
    (q : ℂ) (L : Polynomial ℂ) (x : meroField Set.univ) :
    addTranslationMeroEquiv q (differentialOperatorApply L x) =
      differentialOperatorApply L (addTranslationMeroEquiv q x) := by
  classical
  unfold differentialOperatorApply
  rw [Polynomial.sum_def, Polynomial.sum_def, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_mul, addTranslationMeroEquiv_differentialJet]
  change addTranslationMeroEquiv q
      (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ (L.coeff n))) * _ =
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ (L.coeff n)) * _
  rw [addTranslationMeroEquiv_algebraMap]
  congr 1

/-- Taking an additive translation defect commutes with every constant-coefficient operator. -/
theorem addTranslationMeroEquiv_defect_differentialOperatorApply
    (q : ℂ) (L : Polynomial ℂ) (x : meroField Set.univ) :
    addTranslationMeroEquiv q (differentialOperatorApply L x) -
        differentialOperatorApply L x =
      differentialOperatorApply L (addTranslationMeroEquiv q x - x) := by
  rw [addTranslationMeroEquiv_differentialOperatorApply]
  exact (differentialOperatorApply_sub L (addTranslationMeroEquiv q x) x).symm

end

end GaloisForLFunctions
