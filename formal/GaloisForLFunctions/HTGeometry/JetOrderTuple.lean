import GaloisForLFunctions.HTGeometry.PermutationSumIndependence

/-!
# Listing a jet monomial as a tuple of orders

A monomial in the jets records, for each order, how many times that jet occurs.  The frequency
argument needs the same data laid out as a tuple: one slot per factor, carrying that factor's order.

The two presentations are related by the equivalence between a sigma of `Fin`s and a single `Fin`:
the product over the slots is the monomial, and the multiset of the tuple is the multiplicity
function.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The orders of a jet monomial, laid out one per factor. -/
def orderTuple {n : ℕ} (mj : Fin n → ℕ) : Fin (∑ j, mj j) → ℕ :=
  fun l => ((finSigmaFinEquiv.symm l).1 : ℕ)

/-- **The product over the slots is the monomial.** -/
theorem prod_orderTuple {n : ℕ} (mj : Fin n → ℕ) {M : Type*} [CommMonoid M] (g : ℕ → M) :
    ∏ l, g (orderTuple mj l) = ∏ j : Fin n, g (j : ℕ) ^ mj j := by
  classical
  have hreindex : ∏ l, g (orderTuple mj l)
      = ∏ p : (j : Fin n) × Fin (mj j), g ((p.1 : ℕ)) := by
    refine (Fintype.prod_equiv finSigmaFinEquiv _ _ fun p => ?_).symm
    rw [orderTuple, Equiv.symm_apply_apply]
  rw [hreindex, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [Finset.prod_const, Finset.card_univ]

/-- **The multiset of the tuple is the multiplicity function.** -/
theorem tupleCount_orderTuple {n : ℕ} (mj : Fin n → ℕ) (k : ℕ) :
    tupleCount (orderTuple mj) k
      = ∑ j : Fin n, if (j : ℕ) = k then mj j else 0 := by
  classical
  rw [tupleCount_apply]
  have hcard : ({l : Fin (∑ j, mj j) | orderTuple mj l = k} : Finset (Fin (∑ j, mj j))).card
      = ({p : (j : Fin n) × Fin (mj j) | ((p.1 : ℕ)) = k} :
        Finset ((j : Fin n) × Fin (mj j))).card := by
    refine Finset.card_bij (fun p _ => finSigmaFinEquiv p) ?_ ?_ ?_ |>.symm
    · intro p hp
      rw [Finset.mem_filter] at hp ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [orderTuple, Equiv.symm_apply_apply]
      exact hp.2
    · intro p _ q _ hpq
      exact finSigmaFinEquiv.injective hpq
    · intro l hl
      rw [Finset.mem_filter] at hl
      refine ⟨finSigmaFinEquiv.symm l, ?_, by rw [Equiv.apply_symm_apply]⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hl.2⟩
  rw [hcard]
  rw [Finset.card_filter]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : (j : ℕ) = k
  · simp [hj]
  · simp [hj]

theorem tupleCount_orderTuple_apply {n : ℕ} (mj : Fin n → ℕ) (k : Fin n) :
    tupleCount (orderTuple mj) (k : ℕ) = mj k := by
  classical
  rw [tupleCount_orderTuple]
  have hcond : ∀ j : Fin n, (if (j : ℕ) = (k : ℕ) then mj j else 0)
      = (if j = k then mj j else 0) := by
    intro j
    by_cases hj : j = k
    · subst hj
      simp
    · rw [if_neg hj, if_neg fun hcon => hj (Fin.ext hcon)]
  rw [Finset.sum_congr rfl fun j _ => hcond j, Finset.sum_ite_eq' Finset.univ k mj,
    if_pos (Finset.mem_univ k)]

/-- **A jet monomial is determined by the multiset of its tuple.** -/
theorem orderTuple_tupleCount_injective {n : ℕ} {mj mj' : Fin n → ℕ}
    (h : tupleCount (orderTuple mj) = tupleCount (orderTuple mj')) : mj = mj' := by
  funext k
  rw [← tupleCount_orderTuple_apply mj k, ← tupleCount_orderTuple_apply mj' k, h]

end

end GaloisForLFunctions.HTGeometry
