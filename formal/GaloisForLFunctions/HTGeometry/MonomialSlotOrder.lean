import GaloisForLFunctions.HTGeometry.JetOrderTuple
import GaloisForLFunctions.HTGeometry.BlockFrequencyProfile
import GaloisForLFunctions.HTGeometry.BlockOstrowskiFiber

/-!
# Listing a jet monomial of a palette as a slot tuple

A monomial in the jets of an `n`-element palette records, for each carrier and each order, how many
times that jet occurs.  The graded several-carrier theorem needs the same data laid out as a tuple:
one slot per factor, carrying that factor's order, with the slots grouped by carrier.

The two presentations are related by the equivalence between a sigma of `Fin`s and a single `Fin`,
exactly as in the one-carrier case: the slot's carrier is the first component and its order is read
off that carrier's own order tuple.  The product over the slots is the monomial.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The order carried by each slot of a jet monomial of a palette. -/
def monoSlotOrder {n N : ℕ} (e : Fin n → Fin (N + 1) → ℕ) :
    Fin (∑ k, ∑ j, e k j) → ℕ :=
  fun l => orderTuple (e (finSigmaFinEquiv.symm l).1) (finSigmaFinEquiv.symm l).2

/-- The order at the slot of a sigma pair is that carrier's order tuple there. -/
theorem monoSlotOrder_apply {n N : ℕ} (e : Fin n → Fin (N + 1) → ℕ)
    (p : (k : Fin n) × Fin (∑ j, e k j)) :
    monoSlotOrder e (finSigmaFinEquiv p) = orderTuple (e p.1) p.2 := by
  rw [monoSlotOrder, Equiv.symm_apply_apply]

/-- The carrier a slot belongs to is the block of the canonical assignment. -/
theorem profileBlk_eq_slotBlock {n N : ℕ} (e : Fin n → Fin (N + 1) → ℕ)
    (l : Fin (∑ k, ∑ j, e k j)) :
    profileBlk (fun k => ∑ j, e k j) l = (finSigmaFinEquiv.symm l).1 := rfl

/-- **The product over the slots is the monomial.**  Each carrier contributes the product over its
own order tuple, and the slots are the disjoint union of the carriers' slots. -/
theorem prod_monoSlotOrder {n N : ℕ} (e : Fin n → Fin (N + 1) → ℕ) {M : Type*} [CommMonoid M]
    (g : Fin n → ℕ → M) :
    (∏ l, g (profileBlk (fun k => ∑ j, e k j) l) (monoSlotOrder e l))
      = ∏ k, ∏ j : Fin (N + 1), g k (j : ℕ) ^ e k j := by
  classical
  have hreindex : (∏ l, g (profileBlk (fun k => ∑ j, e k j) l) (monoSlotOrder e l))
      = ∏ p : (k : Fin n) × Fin (∑ j, e k j), g p.1 (orderTuple (e p.1) p.2) := by
    refine (Fintype.prod_equiv finSigmaFinEquiv _ _ fun p => ?_).symm
    rw [profileBlk_eq_slotBlock, monoSlotOrder, Equiv.symm_apply_apply]
  rw [hreindex, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  exact prod_orderTuple (e k) (g k)

/-! ### The slot tuple remembers the monomial -/

/-- **A carrier's slots are that carrier's own slots.**  Injectivity is immediate and surjectivity is
a count: the canonical assignment gives block `k` exactly `∑ j, e k j` slots. -/
theorem slotBlock_bijective {n : ℕ} (len : Fin n → ℕ) (k : Fin n) :
    Function.Bijective
      (fun i : Fin (len k) =>
        (⟨finSigmaFinEquiv ⟨k, i⟩, by
            show (finSigmaFinEquiv.symm (finSigmaFinEquiv (⟨k, i⟩ :
              (k : Fin n) × Fin (len k)))).1 = k
            rw [Equiv.symm_apply_apply]⟩ :
          {l : Fin (∑ k, len k) // profileBlk len l = k})) := by
  classical
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, ?_⟩
  · intro i i' hii
    have h := finSigmaFinEquiv.injective (congrArg Subtype.val hii)
    simpa using h
  · rw [Fintype.card_subtype, card_profileBlk, Fintype.card_fin]

/-- **The slot tuple remembers the monomial.**  The multiset of orders in a carrier's slots is that
carrier's own exponent function. -/
theorem slotCount_monoSlotOrder {n N : ℕ} (e : Fin n → Fin (N + 1) → ℕ) (k : Fin n)
    (j : Fin (N + 1)) :
    slotCount (profileBlk fun k => ∑ j, e k j) (monoSlotOrder e) k (j : ℕ) = e k j := by
  classical
  have hEq : tupleCount (fun bb : {l : Fin (∑ k, ∑ j, e k j) //
        profileBlk (fun k => ∑ j, e k j) l = k} => monoSlotOrder e (bb : Fin (∑ k, ∑ j, e k j)))
      = tupleCount (orderTuple (e k)) := by
    rw [tupleCount, tupleCount]
    refine (Fintype.sum_bijective _ (slotBlock_bijective (fun k => ∑ j, e k j) k) _ _
      fun i => ?_).symm
    exact (monoSlotOrder_apply e ⟨k, i⟩).symm ▸ rfl
  rw [slotCount, hEq, tupleCount_orderTuple_apply]

end

end GaloisForLFunctions.HTGeometry
