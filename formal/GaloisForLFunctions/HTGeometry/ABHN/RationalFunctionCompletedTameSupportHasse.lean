import GaloisForLFunctions.HTGeometry.ABHN.FinsuppReciprocitySupportCardinality
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionCompletedTameContinuousH2Landing

/-!
# Support rigidity for completed tame reciprocity profiles

The completed norm-tame `ℚ/ℤ` profile of a rational-function Milnor `K₂` class has zero
global sum. Consequently every nonzero local invariant has a distinct nonzero partner. A nonzero
invariant at infinity forces a nonzero finite-place invariant, while a nonzero finite-place
invariant is balanced either at infinity or at another finite place.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain
open scoped Polynomial WithZero WithZeroMulInt ValuativeRel

universe u

noncomputable section

local instance {F : Type*} [Field F] : DecidableEq (Option (MonicIrred F)) :=
  Classical.decEq _

/-- A nonzero completed tame invariant profile occupies at least two projective-line places. -/
theorem rationalFunctionCompletedTameRatModIntAllPlaceProfile_two_le_support_card_of_ne_zero
    (F : Type u) [Field F] [Finite F] (y : MilnorKDeg (RatFunc F) 2)
    (hy : rationalFunctionCompletedTameRatModIntAllPlaceProfile F y ≠ 0) :
    2 ≤ (rationalFunctionCompletedTameRatModIntAllPlaceProfile F y).support.card :=
  finsupp_two_le_support_card_of_sum_eq_zero
    (rationalFunctionCompletedTameRatModIntAllPlaceProfile F y)
    (rationalFunctionCompletedTameRatModIntAllPlaceProfile_sum_eq_zero F y) hy

/-- A nonzero completed tame invariant profile has two distinct nonzero local coordinates. -/
theorem rationalFunctionCompletedTameRatModIntAllPlaceProfile_exists_two_nonzero_places_of_ne_zero
    (F : Type u) [Field F] [Finite F] (y : MilnorKDeg (RatFunc F) 2)
    (hy : rationalFunctionCompletedTameRatModIntAllPlaceProfile F y ≠ 0) :
    ∃ v w : Option (MonicIrred F), v ≠ w ∧
      rationalFunctionCompletedTameRatModIntAllPlaceProfile F y v ≠ 0 ∧
      rationalFunctionCompletedTameRatModIntAllPlaceProfile F y w ≠ 0 :=
  finsupp_exists_two_nonzero_places_of_sum_eq_zero
    (rationalFunctionCompletedTameRatModIntAllPlaceProfile F y)
    (rationalFunctionCompletedTameRatModIntAllPlaceProfile_sum_eq_zero F y) hy

/-- Every nonzero completed tame local invariant has a distinct nonzero local partner. -/
theorem rationalFunctionCompletedTameRatModIntAllPlaceProfile_exists_other_nonzero_place
    (F : Type u) [Field F] [Finite F] (y : MilnorKDeg (RatFunc F) 2)
    (v : Option (MonicIrred F))
    (hv : rationalFunctionCompletedTameRatModIntAllPlaceProfile F y v ≠ 0) :
    ∃ w, w ≠ v ∧
      rationalFunctionCompletedTameRatModIntAllPlaceProfile F y w ≠ 0 :=
  finsupp_exists_other_nonzero_place_of_sum_eq_zero
    (rationalFunctionCompletedTameRatModIntAllPlaceProfile F y)
    (rationalFunctionCompletedTameRatModIntAllPlaceProfile_sum_eq_zero F y) hv

/-- A nonzero invariant at infinity forces a nonzero finite-place invariant. -/
theorem rationalFunctionCompletedTame_exists_finite_place_of_infinity_invariant_ne_zero
    (F : Type u) [Field F] [Finite F] (y : MilnorKDeg (RatFunc F) 2)
    (hinfinity : finiteMilnorKOneStdRatModIntInvariant F (milnorResidueInfty 1 y) ≠ 0) :
    ∃ q : MonicIrred F,
      rationalFunctionCompletedTameRatModIntFiniteProfile F y q ≠ 0 := by
  have hnone : rationalFunctionCompletedTameRatModIntAllPlaceProfile F y none ≠ 0 := by
    simpa using hinfinity
  obtain ⟨v, hvnone, hv⟩ :=
    rationalFunctionCompletedTameRatModIntAllPlaceProfile_exists_other_nonzero_place
      F y none hnone
  cases v with
  | none => exact (hvnone rfl).elim
  | some q => exact ⟨q, by simpa using hv⟩

/-- A nonzero finite-place invariant is balanced at infinity or at another finite place. -/
theorem rationalFunctionCompletedTame_finite_place_has_infinity_or_other_finite_partner
    (F : Type u) [Field F] [Finite F] (y : MilnorKDeg (RatFunc F) 2)
    (q : MonicIrred F)
    (hq : rationalFunctionCompletedTameRatModIntFiniteProfile F y q ≠ 0) :
    finiteMilnorKOneStdRatModIntInvariant F (milnorResidueInfty 1 y) ≠ 0 ∨
      ∃ r : MonicIrred F, r ≠ q ∧
        rationalFunctionCompletedTameRatModIntFiniteProfile F y r ≠ 0 := by
  have hsome : rationalFunctionCompletedTameRatModIntAllPlaceProfile F y (some q) ≠ 0 := by
    simpa using hq
  obtain ⟨v, hvq, hv⟩ :=
    rationalFunctionCompletedTameRatModIntAllPlaceProfile_exists_other_nonzero_place
      F y (some q) hsome
  cases v with
  | none => exact Or.inl (by simpa using hv)
  | some r =>
      refine Or.inr ⟨r, ?_, by simpa using hv⟩
      intro hrq
      subst r
      exact hvq rfl

/-- A nonzero raw residue at infinity forces a finite place with nonzero normed tame residue. -/
theorem rationalFunctionCompletedTame_exists_finite_norm_residue_ne_zero_of_infinity_residue_ne_zero
    (F : Type u) [Field F] [Finite F] (y : MilnorKDeg (RatFunc F) 2)
    (hinfinity : milnorResidueInfty 1 y ≠ 0) :
    ∃ q : MonicIrred F,
      milnorNormAt q 1 (milnorPolynomialTotalResidue (F := F) 1 y q) ≠ 0 := by
  have hinvariant :
      finiteMilnorKOneStdRatModIntInvariant F (milnorResidueInfty 1 y) ≠ 0 := by
    simpa [finiteMilnorKOneStdRatModIntInvariant_eq_zero_iff] using hinfinity
  obtain ⟨q, hq⟩ :=
    rationalFunctionCompletedTame_exists_finite_place_of_infinity_invariant_ne_zero
      F y hinvariant
  refine ⟨q, ?_⟩
  simpa [rationalFunctionCompletedTameRatModIntFiniteProfile_apply,
    finiteMilnorKOneStdRatModIntInvariant_eq_zero_iff] using hq

end

end GaloisForLFunctions.HTGeometry.ABHN
