import GaloisForLFunctions.HTGeometry.ReplicaCollisionExtremality
import GaloisForLFunctions.HTGeometry.LinearSpectralRelationOrbitPolynomial
import Mathlib.Data.Sym.Card

/-! # Unequal pairs of replica occupation multisets -/
open Finset
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] {q : ℕ}

/-- Each distinct replica occupancy is counted once, independently of
how its q slots were ordered. -/
abbrev Pair (I : Type*) (q : ℕ) := {p : Sym I q × Sym I q // p.1≠p.2}

theorem card_pairs_choose (I : Type*) [Fintype I] [DecidableEq I] (q : ℕ) :
    Fintype.card (Pair I q) ≤ ((Fintype.card I+q-1).choose q)^2 := by
  have h := Fintype.card_le_of_injective (Subtype.val : Pair I q→_) Subtype.val_injective
  simpa only [Fintype.card_prod,Sym.card_sym_eq_choose,pow_two] using h

/-- Ordered words give the alternative bound D²ᑫ, useful at fixed order. -/
theorem card_pairs (I : Type*) [Fintype I] [DecidableEq I] (q : ℕ) :
    Fintype.card (Pair I q) ≤ (Fintype.card I)^(2*q) := by
  classical
  have hs : Function.Surjective (Sym.ofVector : List.Vector I q→Sym I q) := by
    intro p
    exact ⟨⟨p.val.toList,(Multiset.length_toList _).trans p.property⟩,Subtype.ext (Multiset.coe_toList _)⟩
  have h := Fintype.card_le_of_surjective _ hs
  rw [Fintype.card_congr (Equiv.vectorEquivFin I q),Fintype.card_fun,Fintype.card_fin] at h
  have hh := Fintype.card_le_of_injective (Subtype.val : Pair I q→_) Subtype.val_injective
  rw [Fintype.card_prod] at hh
  exact hh.trans ((Nat.mul_le_mul h h).trans_eq (by rw [two_mul,pow_add]))

/-- Two elementary upper bounds on the number of different frequency factors. -/
def degreeBound (D q : ℕ) := min (D^(2*q)) (((D+q-1).choose q)^2)

theorem card_pairs_le_bound (I : Type*) [Fintype I] [DecidableEq I] (q : ℕ) :
    Fintype.card (Pair I q) ≤ degreeBound (Fintype.card I) q :=
  le_min (card_pairs I q) (card_pairs_choose I q)

/-- Relabeling levels permutes occupation multisets and preserves inequality. -/
def relabel (s : Equiv.Perm I) : Equiv.Perm (Pair I q) :=
  let e := Sym.equivCongr (n:=q) s
  { toFun := fun p => ⟨(e p.val.1,e p.val.2),e.injective.ne p.property⟩
    invFun := fun p => ⟨(e.symm p.val.1,e.symm p.val.2),e.symm.injective.ne p.property⟩
    left_inv := fun p => Subtype.ext (Prod.ext (e.symm_apply_apply p.val.1) (e.symm_apply_apply p.val.2))
    right_inv := fun p => Subtype.ext (Prod.ext (e.apply_symm_apply p.val.1) (e.apply_symm_apply p.val.2)) }

def mode (p : Pair I q) (i : I) : ℤ :=
  (p.val.1.val.count i:ℤ)-(p.val.2.val.count i:ℤ)

theorem count_sum (u : Sym I q) : ∑ i, u.val.count i=q :=
  (Multiset.sum_count_eq_card (fun i _ => Finset.mem_univ i)).trans u.property

omit [Fintype I] in
theorem mode_relabel (s : Equiv.Perm I) (p : Pair I q) (i : I) : mode (relabel s p) (s i)=mode p i := by
  change (((p.val.1.val.map s).count (s i):ℕ):ℤ)-((p.val.2.val.map s).count (s i):ℤ)=_
  rw [Multiset.count_map_eq_count' _ _ s.injective,Multiset.count_map_eq_count' _ _ s.injective]
  rfl

def gap (E : I→ℝ) (p : Pair I q) := ∑ i, (mode p i:ℝ)*E i

theorem gap_relabel (s : Equiv.Perm I) (E : I→ℝ) (p : Pair I q) : gap (E ∘ s) p=gap E (relabel s p) :=
  Fintype.sum_equiv s _ _ fun i => by rw [mode_relabel]; rfl

theorem gap_ne_zero {E : I→ℝ} (h : MaximallyProjectiveEnergy E) (p : Pair I q) : gap E p≠0 := by
  intro he
  have hb : SpectralCharacterBalanced (mode p) := by
    change (∑ i, ((p.val.1.val.count i:ℤ)-(p.val.2.val.count i:ℤ)))=0
    rw [Finset.sum_sub_distrib,←Nat.cast_sum,←Nat.cast_sum,count_sum,count_sum,sub_self]
  have hz := h (mode p) hb he
  apply p.property
  apply Subtype.ext
  apply Multiset.ext'
  intro i
  have hi := congrFun hz i
  change (p.val.1.val.count i:ℤ)-(p.val.2.val.count i:ℤ)=0 at hi
  exact_mod_cast sub_eq_zero.mp hi

#print axioms gap_ne_zero
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
