import GaloisForLFunctions.HTGeometry.JetOrderTuple

/-!
# Reading a jet monomial at a fixed length

The monomials of a differential relation have jet parts of different total degrees, while the graded
form of the frequency argument wants, for each degree, a set of tuples of exactly that length.

Padding the order tuple by zero gives, for each length, a total map from multiplicity functions to
tuples of that length.  On the multiplicity functions of the right total degree it changes nothing:
the product over the slots and the multiset of the tuple are the same as before, and the map is
injective there.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The orders of a jet monomial, laid out one per factor and padded by zero to a fixed length. -/
def padOrderTuple {n : ℕ} (mj : Fin n → ℕ) (M : ℕ) : Fin M → ℕ :=
  fun l => if h : (l : ℕ) < ∑ j, mj j then orderTuple mj ⟨l, h⟩ else 0

theorem padOrderTuple_apply_of_eq {n M : ℕ} {mj : Fin n → ℕ} (hM : ∑ j, mj j = M) (l : Fin M) :
    padOrderTuple mj M l = orderTuple mj (Fin.cast hM.symm l) := by
  have hlt : (l : ℕ) < ∑ j, mj j := by
    rw [hM]
    exact l.isLt
  rw [padOrderTuple, dif_pos hlt]
  rfl

/-- **The product over the padded slots is the monomial.** -/
theorem prod_padOrderTuple {n M : ℕ} {mj : Fin n → ℕ} (hM : ∑ j, mj j = M) {A : Type*}
    [CommMonoid A] (g : ℕ → A) :
    ∏ l : Fin M, g (padOrderTuple mj M l) = ∏ j : Fin n, g (j : ℕ) ^ mj j := by
  rw [← prod_orderTuple mj g]
  refine (Fintype.prod_equiv (finCongr hM) (fun l => g (orderTuple mj l))
    (fun l => g (padOrderTuple mj M l)) fun l => ?_).symm
  rw [padOrderTuple_apply_of_eq hM (finCongr hM l)]
  rfl

/-- **Padding does not change the multiset of the tuple.** -/
theorem tupleCount_padOrderTuple {n M : ℕ} {mj : Fin n → ℕ} (hM : ∑ j, mj j = M) :
    tupleCount (padOrderTuple mj M) = tupleCount (orderTuple mj) := by
  classical
  rw [tupleCount, tupleCount]
  refine Fintype.sum_equiv (finCongr hM).symm _ _ fun l => ?_
  rw [padOrderTuple_apply_of_eq hM l]
  rfl

/-- **A jet monomial of the right total degree is determined by its padded tuple.** -/
theorem padOrderTuple_injOn {n M : ℕ} {mj mj' : Fin n → ℕ} (hM : ∑ j, mj j = M)
    (hM' : ∑ j, mj' j = M)
    (h : tupleCount (padOrderTuple mj M) = tupleCount (padOrderTuple mj' M)) : mj = mj' := by
  refine orderTuple_tupleCount_injective ?_
  rw [← tupleCount_padOrderTuple hM, ← tupleCount_padOrderTuple hM', h]

end

end GaloisForLFunctions.HTGeometry
