import GaloisForLFunctions.HTGeometry.JetAffineConnectionLevelTwo
import GaloisForLFunctions.HTGeometry.QuadOneNoAffineConnection
import GaloisForLFunctions.HTGeometry.QuadTwoNoAffineConnection
import GaloisForLFunctions.HTGeometry.QuadraticOrbifoldTail

/-!
# Neither quadratic coarse-graining admits an invariant affine structure at jet level two

A normalizing shift at jet level two solves the rational affine-connection equation of the map, and
neither `z² + 1` nor `(z − 1)²` admits a solution.  So for both maps the second branch of the
normalization dichotomy is empty at level two: an eigen-relation of jet order two already has jet
order at most one, where the fixed branch is closed.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **`z ↦ z² + 1` has no invariant affine structure at jet level two.** -/
theorem quadOne_not_hasNormalizingShift_two :
    ¬ HasNormalizingShift (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
      quadOne_substitutionDeriv_ne_zero (show (1 : ℕ) ≤ 2 by norm_num) := by
  intro h
  obtain ⟨a, ha⟩ :=
    exists_isAffineConnection_of_hasNormalizingShift_two quadOne_substitutionDeriv_ne_zero h
  exact quadOne_no_affine_connection a ha

/-- **`z ↦ (z − 1)²` has no invariant affine structure at jet level two.** -/
theorem quadTwo_not_hasNormalizingShift_two :
    ¬ HasNormalizingShift (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
      quadTwo_substitutionDeriv_ne_zero (show (1 : ℕ) ≤ 2 by norm_num) := by
  intro h
  obtain ⟨a, ha⟩ :=
    exists_isAffineConnection_of_hasNormalizingShift_two quadTwo_substitutionDeriv_ne_zero h
  exact quadTwo_no_affine_connection a ha

/-- **An eigen-relation of jet order two for `z ↦ z² + 1` already has jet order at most one.** -/
theorem quadOne_lowerOrder_of_substitutionEigen_two {κ : ℤ} {w : JetField ℂ Unit} {lam : ℂ}
    (hlam : lam ≠ 0)
    (h : SubstitutionEigen (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
      quadOne_substitutionDeriv_ne_zero 2 κ w lam) :
    ∀ j : ℕ, 1 < j → JetField.pd ((), j) w = 0 := by
  rcases lowerOrder_or_hasNormalizingShift _ quadOne_substitutionDeriv_ne_zero
    (show (1 : ℕ) ≤ 2 by norm_num) hlam h with hlow | hshift
  · exact hlow
  · exact absurd hshift quadOne_not_hasNormalizingShift_two

/-- **An eigen-relation of jet order two for `z ↦ (z − 1)²` already has jet order at most one.** -/
theorem quadTwo_lowerOrder_of_substitutionEigen_two {κ : ℤ} {w : JetField ℂ Unit} {lam : ℂ}
    (hlam : lam ≠ 0)
    (h : SubstitutionEigen (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
      quadTwo_substitutionDeriv_ne_zero 2 κ w lam) :
    ∀ j : ℕ, 1 < j → JetField.pd ((), j) w = 0 := by
  rcases lowerOrder_or_hasNormalizingShift _ quadTwo_substitutionDeriv_ne_zero
    (show (1 : ℕ) ≤ 2 by norm_num) hlam h with hlow | hshift
  · exact hlow
  · exact absurd hshift quadTwo_not_hasNormalizingShift_two

end

end GaloisForLFunctions.HTGeometry
