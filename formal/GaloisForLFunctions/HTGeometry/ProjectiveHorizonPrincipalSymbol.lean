import GaloisForLFunctions.HTGeometry.ProjectiveHorizonSchwarzianJetDerivatives

/-!
# Principal symbols are invariant under the jet shift

The jet shift lowers a coordinate derivation by one.  So differentiating a jet observable raises its
order by exactly one, and the derivative along the new top coordinate is unchanged: the principal
symbol of an observable of order `m` is the same as the principal symbol of its `k`-th derivative,
read at order `m+k`.

This is what lets the leading coefficient of a differential rational expression be extracted inside
the field it generates, without differentiating along a coordinate that the field does not see.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

variable {C : Type*} [Field C] [CharZero C]

omit [CharZero C] in
/-- Differentiating raises the order by at most one. -/
theorem freeCoordinateDerivation_shift_iterate_of_gt {u : FreeScalarJetField C} {m : ℕ}
    (hu : ∀ j : ℕ, m < j → freeCoordinateDerivation C ℕ j u = 0) :
    ∀ (k j : ℕ), m + k < j →
      freeCoordinateDerivation C ℕ j ((freeJetShift C)^[k] u) = 0 := by
  intro k
  induction k with
  | zero =>
      intro j hj
      rw [Function.iterate_zero_apply]
      exact hu j (by omega)
  | succ k ih =>
      intro j hj
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [Function.iterate_succ_apply', freeCoordinateDerivation_shift_apply,
        ih j' (by omega), ih (j' + 1) (by omega), map_zero, add_zero]

omit [CharZero C] in
/-- **Principal symbols are invariant under the jet shift.** -/
theorem freeCoordinateDerivation_shift_iterate_top {u : FreeScalarJetField C} {m : ℕ}
    (hu : ∀ j : ℕ, m < j → freeCoordinateDerivation C ℕ j u = 0) (k : ℕ) :
    freeCoordinateDerivation C ℕ (m + k) ((freeJetShift C)^[k] u) =
      freeCoordinateDerivation C ℕ m u := by
  induction k with
  | zero =>
      rw [Function.iterate_zero_apply, Nat.add_zero]
  | succ k ih =>
      rw [show m + (k + 1) = (m + k) + 1 from by omega, Function.iterate_succ_apply',
        freeCoordinateDerivation_shift_apply,
        freeCoordinateDerivation_shift_iterate_of_gt hu k (m + k + 1) (by omega),
        map_zero, zero_add, ih]

omit [CharZero C] in
/-- The differential-jet form: the principal symbol of the `k`-th jet of an observable of order `m`
is the principal symbol of the observable. -/
theorem freeCoordinateDerivation_differentialJet_top {u : FreeScalarJetField C} {m : ℕ}
    (hu : ∀ j : ℕ, m < j → freeCoordinateDerivation C ℕ j u = 0) (k : ℕ) :
    freeCoordinateDerivation C ℕ (m + k) (differentialJet k u) =
      freeCoordinateDerivation C ℕ m u := by
  have hiter : ∀ l : ℕ, differentialJet l u = (freeJetShift C)^[l] u := by
    intro l
    induction l with
    | zero => rw [differentialJet_zero, Function.iterate_zero_apply]
    | succ l ih =>
        rw [differentialJet_succ, ih, freeScalarJetField_deriv_apply,
          Function.iterate_succ_apply']
  rw [hiter k]
  exact freeCoordinateDerivation_shift_iterate_top hu k

end

end GaloisForLFunctions.HTGeometry
