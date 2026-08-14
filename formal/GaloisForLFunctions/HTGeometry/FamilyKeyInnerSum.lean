import GaloisForLFunctions.HTGeometry.FamilySlotSequence
import GaloisForLFunctions.HTGeometry.FamilySquareFreeNodeForm

/-!
# The inner split sum at a square-free key, indexed by orderings

Fix a jet monomial whose slot count is `D` and a square-free key given by an injective tuple `k` of
`D` parameters above the jet order.  The splits of the monomial realizing that key are the
permutations of its slots, so the total weight they contribute is the sum, over all orderings of the
monomial's slot sequence, of the slot-sequence contribution at `k`:

```text
∑_{splits with key k} famWeight = ∑_{σ : Perm (Fin D)} slotTerm q (slotSeqOf n D m σ) k .
```

Both the index set and the slot sequences are independent of `k`; only the contribution depends on
it.  That is what lets a single separation theorem see every key at once.
-/

open Finset

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The total jet order of a monomial, read on its flattened slots. -/
def slotOrderSum (n : ℕ) (m : Option (ι × Fin (n + 1)) →₀ ℕ) : ℕ :=
  ∑ t : Fin (∑ p : ι × Fin (n + 1), m (some p)), ((famSlot n m t).2 : ℕ)

/-- The slot sequence of a monomial, listed in the order prescribed by a permutation. -/
def slotSeqOf (n D : ℕ) (m : Option (ι × Fin (n + 1)) →₀ ℕ) (σ : Equiv.Perm (Fin D)) :
    Fin D → ι × ℕ :=
  if h : (∑ p : ι × Fin (n + 1), m (some p)) = D then
    fun s => slotLabel (famSlot n m ((finCongr h).symm (σ s)))
  else Classical.arbitrary _

omit [DecidableEq ι] in
theorem slotSeqOf_apply {n D : ℕ} {m : Option (ι × Fin (n + 1)) →₀ ℕ}
    (h : (∑ p : ι × Fin (n + 1), m (some p)) = D) (σ : Equiv.Perm (Fin D)) (s : Fin D) :
    slotSeqOf n D m σ s = slotLabel (famSlot n m ((finCongr h).symm (σ s))) := by
  rw [slotSeqOf, dif_pos h]

omit [DecidableEq ι] in
/-- **The inner split sum at a square-free key.**  The splits realizing the key of an injective
tuple above the jet order contribute the sum of the slot-sequence terms over all orderings. -/
theorem sum_famWeight_key_eq_slotSeq (q : ι → ℂ) {n D : ℕ}
    (m : Option (ι × Fin (n + 1)) →₀ ℕ) (hcnt : (∑ p : ι × Fin (n + 1), m (some p)) = D)
    {k : Fin D → ℕ} (hkinj : Function.Injective k) (hkn : ∀ s, n < k s) :
    ∑ l ∈ (((Finset.univ : Finset (Fin (∑ p : ι × Fin (n + 1), m (some p)))).finsuppAntidiag
        ((∑ s, k s) - slotOrderSum n m)).filter
        (fun l => key (famOrder n m l) = key k)),
      famWeight q n m l
      = ∑ σ : Equiv.Perm (Fin D), HTGeometry.slotTerm q (slotSeqOf n D m σ) k := by
  classical
  set e : Fin (∑ p : ι × Fin (n + 1), m (some p)) ≃ Fin D := finCongr hcnt with he
  set k' : Fin (∑ p : ι × Fin (n + 1), m (some p)) → ℕ := fun t => k (e t) with hk'
  have hk'inj : Function.Injective k' := by
    intro t t' htt
    exact e.injective (hkinj htt)
  have hk'n : ∀ t, n < k' t := fun t => hkn (e t)
  have hkeyeq : key k' = key k := key_comp_equiv e k
  have hsumeq : (∑ t, k' t) = ∑ s, k s := Equiv.sum_comp e k
  have hbase := sum_famWeight_squareFreeKey_node_form q n m hk'inj hk'n
  rw [hsumeq] at hbase
  have hfilter : (((Finset.univ : Finset (Fin (∑ p : ι × Fin (n + 1), m (some p)))).finsuppAntidiag
        ((∑ s, k s) - slotOrderSum n m)).filter
        (fun l => key (famOrder n m l) = key k))
      = (((Finset.univ : Finset (Fin (∑ p : ι × Fin (n + 1), m (some p)))).finsuppAntidiag
        ((∑ s, k s) - (∑ t, ((famSlot n m t).2 : ℕ)))).filter
        (fun l => key (famOrder n m l) = key k')) := by
    rw [hkeyeq, slotOrderSum]
  rw [hfilter, hbase]
  refine Eq.trans (Finset.sum_congr rfl fun σ' _ => ?_)
    (Equiv.sum_comp (Equiv.permCongr e) (fun σ => HTGeometry.slotTerm q (slotSeqOf n D m σ) k))
  have hperm : ∀ s : Fin D, e.symm ((Equiv.permCongr e σ') s) = σ' (e.symm s) := by
    intro s
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rw [famNodeTerm, HTGeometry.slotTerm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine (Equiv.prod_comp e.symm (fun t =>
    ((descPochhammer ℂ (famJetOrder n m (σ' t))).eval ((k' t : ℕ) : ℂ))
      * (q (famNode n m (σ' t))) ^ (k' t))).symm.trans ?_
  refine Finset.prod_congr rfl fun s _ => ?_
  have hks : k' (e.symm s) = k s := by
    rw [hk']
    simp
  rw [hks, slotSeqOf_apply hcnt, hperm s, descPochhammer_eval_eq_descFactorial,
    famJetOrder, famNode, slotLabel]

end

end GaloisForLFunctions
