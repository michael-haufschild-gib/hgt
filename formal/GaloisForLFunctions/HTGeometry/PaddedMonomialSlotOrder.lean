import GaloisForLFunctions.HTGeometry.PaddedOrderTuple
import GaloisForLFunctions.HTGeometry.MonomialSlotOrder

/-!
# Listing a palette monomial at a fixed multi-degree

The monomials of a relation among the jets of a palette carry different multi-degrees, while the
graded form of the frequency argument wants, for each multi-degree, a set of slot tuples of exactly
that shape.  A monomial has to be laid out as a tuple whose length is the *ambient* multi-degree, not
its own, or the two lengths differ by an equation and the layout is a cast.

Padding each carrier's order tuple by zero makes the layout total: for every multi-degree there is a
map from exponent functions to slot tuples of that shape, defined without any hypothesis.  On the
exponent functions of the matching multi-degree it changes nothing — the product over the slots is
the monomial and the blockwise multiset is the exponent function — so the layout is faithful exactly
where it is used.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The carrier a slot belongs to is the first component of its sigma decomposition. -/
theorem profileBlk_finSigmaFinEquiv {n : ℕ} (len : Fin n → ℕ)
    (p : (k : Fin n) × Fin (len k)) : profileBlk len (finSigmaFinEquiv p) = p.1 := by
  show (finSigmaFinEquiv.symm (finSigmaFinEquiv p)).1 = p.1
  rw [Equiv.symm_apply_apply]

/-- The orders of a palette monomial, laid out one per factor, grouped by carrier and padded by zero
to a fixed multi-degree. -/
def padSlotOrder {n N : ℕ} (e : Fin n → Fin (N + 1) → ℕ) (len : Fin n → ℕ) :
    Fin (∑ k, len k) → ℕ :=
  fun l => padOrderTuple (e (finSigmaFinEquiv.symm l).1) (len (finSigmaFinEquiv.symm l).1)
    (finSigmaFinEquiv.symm l).2

/-- The order at the slot of a sigma pair is that carrier's padded order tuple there. -/
theorem padSlotOrder_apply {n N : ℕ} (e : Fin n → Fin (N + 1) → ℕ) (len : Fin n → ℕ)
    (p : (k : Fin n) × Fin (len k)) :
    padSlotOrder e len (finSigmaFinEquiv p) = padOrderTuple (e p.1) (len p.1) p.2 := by
  rw [padSlotOrder, Equiv.symm_apply_apply]

/-- **The product over the padded slots is the monomial.** -/
theorem prod_padSlotOrder {n N : ℕ} (e : Fin n → Fin (N + 1) → ℕ) (len : Fin n → ℕ)
    (hlen : ∀ k, ∑ j, e k j = len k) {M : Type*} [CommMonoid M] (g : Fin n → ℕ → M) :
    (∏ l, g (profileBlk len l) (padSlotOrder e len l))
      = ∏ k, ∏ j : Fin (N + 1), g k (j : ℕ) ^ e k j := by
  classical
  have hreindex : (∏ l, g (profileBlk len l) (padSlotOrder e len l))
      = ∏ p : (k : Fin n) × Fin (len k), g p.1 (padOrderTuple (e p.1) (len p.1) p.2) := by
    refine (Fintype.prod_equiv finSigmaFinEquiv _ _ fun p => ?_).symm
    rw [profileBlk_finSigmaFinEquiv, padSlotOrder_apply]
  rw [hreindex, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  exact prod_padOrderTuple (hlen k) (g k)

/-- **The padded slot tuple remembers the monomial.**  The multiset of orders in a carrier's slots is
that carrier's own exponent function. -/
theorem slotCount_padSlotOrder {n N : ℕ} (e : Fin n → Fin (N + 1) → ℕ) (len : Fin n → ℕ)
    (hlen : ∀ k, ∑ j, e k j = len k) (k : Fin n) (j : Fin (N + 1)) :
    slotCount (profileBlk len) (padSlotOrder e len) k (j : ℕ) = e k j := by
  classical
  have hEq : tupleCount (fun bb : {l : Fin (∑ k, len k) // profileBlk len l = k} =>
        padSlotOrder e len (bb : Fin (∑ k, len k)))
      = tupleCount (padOrderTuple (e k) (len k)) := by
    rw [tupleCount, tupleCount]
    refine (Fintype.sum_bijective _ (slotBlock_bijective len k) _ _ fun i => ?_).symm
    exact (padSlotOrder_apply e len ⟨k, i⟩).symm ▸ rfl
  rw [slotCount, hEq, tupleCount_padOrderTuple (hlen k), tupleCount_orderTuple_apply]

/-- **A palette monomial of the right multi-degree is determined by its padded slot tuple.**  This is
the distinctness hypothesis of the graded several-carrier theorem. -/
theorem padSlotOrder_injOn {n N : ℕ} {e e' : Fin n → Fin (N + 1) → ℕ} {len : Fin n → ℕ}
    (hlen : ∀ k, ∑ j, e k j = len k) (hlen' : ∀ k, ∑ j, e' k j = len k)
    (h : ∀ k, slotCount (profileBlk len) (padSlotOrder e len) k
      = slotCount (profileBlk len) (padSlotOrder e' len) k) : e = e' := by
  funext k j
  rw [← slotCount_padSlotOrder e len hlen k j, ← slotCount_padSlotOrder e' len hlen' k j, h k]

end

end GaloisForLFunctions.HTGeometry
