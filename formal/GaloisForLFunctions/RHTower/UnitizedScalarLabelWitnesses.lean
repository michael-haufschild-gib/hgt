import GaloisForLFunctions.RHTower.CCMRationalAdelicUnitizedCyclicRestrictionFormula

/-!
# The all-scalar branch of the unitized cyclic restriction is inhabited, and so is its complement

The branching law of the unitized cyclic restriction splits on whether every position carries the
scalar-unit label.  Both sides are occupied: the constant scalar labelling is all-scalar, and any
labelling with a single crossed position is not, so neither branch of the restriction is vacuous.
-/

namespace GaloisForLFunctions
namespace RHTower

/-- The constant scalar labelling is all-scalar. -/
theorem ccmRationalAdelicUnitizedAllScalar_const {n : ℕ} :
    ccmRationalAdelicUnitizedAllScalar
      (fun _ : Fin (n + 1) => CCMRationalAdelicUnitizedLabel.scalar) :=
  fun _ => rfl

/-- All-scalar labellings are exactly the constant scalar labelling. -/
theorem ccmRationalAdelicUnitizedAllScalar_iff {n : ℕ}
    (label : Fin (n + 1) → CCMRationalAdelicUnitizedLabel) :
    ccmRationalAdelicUnitizedAllScalar label ↔
      label = fun _ => CCMRationalAdelicUnitizedLabel.scalar := by
  constructor
  · intro h
    funext j
    exact h j
  · intro h j
    rw [h]

/-- A labelling with one crossed position is not all-scalar, so the complementary branch is
occupied as well. -/
theorem not_ccmRationalAdelicUnitizedAllScalar_of_crossed {n : ℕ}
    (label : Fin (n + 1) → CCMRationalAdelicUnitizedLabel) {j : Fin (n + 1)} {k : CCMRationalAdelicScaling}
    (hj : label j = CCMRationalAdelicUnitizedLabel.crossed k) :
    ¬ ccmRationalAdelicUnitizedAllScalar label := by
  intro h
  rw [h j] at hj
  exact CCMRationalAdelicUnitizedLabel.noConfusion hj

/-- Both branches of the unitized restriction are occupied. -/
theorem exists_and_not_ccmRationalAdelicUnitizedAllScalar {n : ℕ}
    (k : CCMRationalAdelicScaling) :
    (∃ label : Fin (n + 1) → CCMRationalAdelicUnitizedLabel,
        ccmRationalAdelicUnitizedAllScalar label) ∧
      (∃ label : Fin (n + 1) → CCMRationalAdelicUnitizedLabel,
        ¬ ccmRationalAdelicUnitizedAllScalar label) := by
  refine ⟨⟨_, ccmRationalAdelicUnitizedAllScalar_const⟩,
    ⟨fun _ => CCMRationalAdelicUnitizedLabel.crossed k, ?_⟩⟩
  exact not_ccmRationalAdelicUnitizedAllScalar_of_crossed _ (j := 0) rfl

end RHTower
end GaloisForLFunctions
