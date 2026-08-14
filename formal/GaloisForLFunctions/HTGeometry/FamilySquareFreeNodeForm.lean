import GaloisForLFunctions.HTGeometry.SquareFreeAtomKey
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# The square-free key weight as a node-indexed exponential polynomial

The splits realizing a square-free atom key are the permutations of the slot order, so the total
weight of that key is a permanent.  Reading the falling factorial as the evaluation of
`descPochhammer` and separating it from the dilation powers exhibits that permanent as an
exponential polynomial in the key parameters `k`:

```text
∑_{splits with key k} famWeight = ∑_σ (∏_s desc_{j(σ s)}(k_s)) · ∏_s q_{i(σ s)}^{k_s} ,
```

the node tuple of the term `σ` being `s ↦ q_{i(σ s)}` and its polynomial part a product of falling
factorials of the slot orders.  This is the shape a multi-node separation theorem consumes: the
dilations enter only through the nodes, the jet orders only through the polynomial part.
-/

open Finset

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The dilation index of slot `t`. -/
def famNode (n : ℕ) (m : Option (ι × Fin (n + 1)) →₀ ℕ)
    (t : Fin (∑ p : ι × Fin (n + 1), m (some p))) : ι :=
  (famSlot n m t).1

/-- The jet order of slot `t`. -/
def famJetOrder (n : ℕ) (m : Option (ι × Fin (n + 1)) →₀ ℕ)
    (t : Fin (∑ p : ι × Fin (n + 1), m (some p))) : ℕ :=
  ((famSlot n m t).2 : ℕ)

omit [DecidableEq ι] in
theorem famJetOrder_le (n : ℕ) (m : Option (ι × Fin (n + 1)) →₀ ℕ)
    (t : Fin (∑ p : ι × Fin (n + 1), m (some p))) : famJetOrder n m t ≤ n :=
  famSlot_snd_le n m t

/-- One permutation's contribution to the square-free key weight, in node form. -/
noncomputable def famNodeTerm (q : ι → ℂ) (n : ℕ) (m : Option (ι × Fin (n + 1)) →₀ ℕ)
    (k : Fin (∑ p : ι × Fin (n + 1), m (some p)) → ℕ)
    (σ : Equiv.Perm (Fin (∑ p : ι × Fin (n + 1), m (some p)))) : ℂ :=
  (∏ s, (descPochhammer ℂ (famJetOrder n m (σ s))).eval ((k s : ℕ) : ℂ))
    * ∏ s, (q (famNode n m (σ s))) ^ (k s)

omit [DecidableEq ι] in
/-- **The square-free key weight in node form.**  The splits realizing the key of an injective
tuple `k` of parameters above the jet order contribute a permanent whose `σ`-term is a product of
falling factorials of the slot orders times the `k`-powers of the slot dilations. -/
theorem sum_famWeight_squareFreeKey_node_form (q : ι → ℂ) (n : ℕ)
    (m : Option (ι × Fin (n + 1)) →₀ ℕ)
    {k : Fin (∑ p : ι × Fin (n + 1), m (some p)) → ℕ}
    (hkinj : Function.Injective k) (hkn : ∀ s, n < k s) :
    ∑ l ∈ (((Finset.univ : Finset (Fin (∑ p : ι × Fin (n + 1), m (some p)))).finsuppAntidiag
        ((∑ s, k s) - (∑ t, ((famSlot n m t).2 : ℕ)))).filter
        (fun l => key (famOrder n m l) = key k)),
      famWeight q n m l
      = ∑ σ : Equiv.Perm (Fin (∑ p : ι × Fin (n + 1), m (some p))),
          famNodeTerm q n m k σ := by
  classical
  rw [← sum_famWeight_over_squareFreeKey q n m hkinj hkn]
  have hterm : ∀ σ : Equiv.Perm (Fin (∑ p : ι × Fin (n + 1), m (some p))),
      famWeight q n m (keySplit n m k σ) = famNodeTerm q n m k σ.symm := by
    intro σ
    rw [famWeight_keySplit q n m hkn σ, famNodeTerm, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [descPochhammer_eval_eq_descFactorial, famJetOrder, famNode]
  rw [Finset.sum_congr rfl (fun σ (_ : σ ∈ Finset.univ) => hterm σ)]
  exact Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin (∑ p : ι × Fin (n + 1), m (some p)))))
    _ _ (fun σ => rfl)

end

end GaloisForLFunctions
