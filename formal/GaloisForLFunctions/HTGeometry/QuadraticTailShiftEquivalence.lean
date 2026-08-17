import GaloisForLFunctions.HTGeometry.JetFixedFieldShift
import GaloisForLFunctions.HTGeometry.QuadraticShiftDescentBranches

/-!
# The tail of the two quadratic maps, reduced to one condition

For `z ↦ z² + 1` and for `z ↦ (z − 1)²` a fixed element of jet order at most one is already
constant, so the equivalence between normalizing shifts and nonconstant fixed elements applies:
the whole stable observable field of either map is trivial exactly when no jet level of order at
least two carries a normalizing shift.

Level two is settled — neither map admits one — so what is left is a single family of statements,
one per level, and the descent of `QuadraticShiftDescentBranches` reduces each of them to the
polynomial branches of degree one and two.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The tail of `z ↦ z² + 1` is trivial exactly when no jet level of order at least two carries a
normalizing shift.** -/
theorem quadOne_forall_fixed_isConst_iff :
    (∀ (M : ℕ) (g : JetField ℂ Unit), (∀ j : ℕ, M < j → JetField.pd ((), j) g = 0) →
        jetSubstitution (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
          quadOne_substitutionDeriv_ne_zero g = g →
        ∃ e : ℂ, g = algebraMap ℂ (JetField ℂ Unit) e)
      ↔ ∀ M : ℕ, ∀ hM : 2 ≤ M,
          ¬ HasNormalizingShift (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
            quadOne_substitutionDeriv_ne_zero (le_trans one_le_two hM) :=
  forall_fixed_isConst_iff _ quadOne_substitutionDeriv_ne_zero
    (fun _ hu hfix => quadOne_fixed_of_order_one hu hfix)

/-- **The tail of `z ↦ (z − 1)²` is trivial exactly when no jet level of order at least two carries
a normalizing shift.** -/
theorem quadTwo_forall_fixed_isConst_iff :
    (∀ (M : ℕ) (g : JetField ℂ Unit), (∀ j : ℕ, M < j → JetField.pd ((), j) g = 0) →
        jetSubstitution (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
          quadTwo_substitutionDeriv_ne_zero g = g →
        ∃ e : ℂ, g = algebraMap ℂ (JetField ℂ Unit) e)
      ↔ ∀ M : ℕ, ∀ hM : 2 ≤ M,
          ¬ HasNormalizingShift (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
            quadTwo_substitutionDeriv_ne_zero (le_trans one_le_two hM) :=
  forall_fixed_isConst_iff _ quadTwo_substitutionDeriv_ne_zero
    (fun _ hu hfix => quadTwo_fixed_of_order_one hu hfix)

/-- **No nonconstant fixed element of jet order at most two**, for `z ↦ z² + 1`. -/
theorem quadOne_fixed_of_order_two {g : JetField ℂ Unit}
    (hg : ∀ j : ℕ, 2 < j → JetField.pd ((), j) g = 0)
    (hfix : jetSubstitution (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
      quadOne_substitutionDeriv_ne_zero g = g) :
    ∃ e : ℂ, g = algebraMap ℂ (JetField ℂ Unit) e := by
  by_cases hpd : JetField.pd ((), 2) g = 0
  · refine quadOne_fixed_of_order_one (fun j hj => ?_) hfix
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hj) with heq | hgt
    · rw [← heq]
      exact hpd
    · exact hg j (by omega)
  · exact absurd ((hasNormalizingShift_iff_exists_fixed _ quadOne_substitutionDeriv_ne_zero
      (le_refl 2)).mpr ⟨g, hg, hpd, hfix⟩) quadOne_not_hasNormalizingShift_two

/-- **No nonconstant fixed element of jet order at most two**, for `z ↦ (z − 1)²`. -/
theorem quadTwo_fixed_of_order_two {g : JetField ℂ Unit}
    (hg : ∀ j : ℕ, 2 < j → JetField.pd ((), j) g = 0)
    (hfix : jetSubstitution (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
      quadTwo_substitutionDeriv_ne_zero g = g) :
    ∃ e : ℂ, g = algebraMap ℂ (JetField ℂ Unit) e := by
  by_cases hpd : JetField.pd ((), 2) g = 0
  · refine quadTwo_fixed_of_order_one (fun j hj => ?_) hfix
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hj) with heq | hgt
    · rw [← heq]
      exact hpd
    · exact hg j (by omega)
  · exact absurd ((hasNormalizingShift_iff_exists_fixed _ quadTwo_substitutionDeriv_ne_zero
      (le_refl 2)).mpr ⟨g, hg, hpd, hfix⟩) quadTwo_not_hasNormalizingShift_two

end

end GaloisForLFunctions.HTGeometry
