import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

/-! # Singleton cancellation in ordered matrix moments -/

open Finset
namespace GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Sampling
noncomputable section
variable {J X R : Type*} [Fintype J] [DecidableEq J] [Fintype X] [Ring R]

private theorem one_slot (A : X → R) (hA : ∑ x, A x=0) {n : ℕ}
    (p : Fin n) (B : Fin n → R) :
    (∑ x, (List.ofFn (fun j => if j=p then A x else B j)).prod)=0 := by
  induction n with
  | zero => exact Fin.elim0 p
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) p
    · simp only [List.ofFn_succ,List.prod_cons,eq_self,if_true,Fin.succ_ne_zero,if_false]
      rw [←Finset.sum_mul,hA,zero_mul]
    · simp only [List.ofFn_succ,List.prod_cons,if_neg (Ne.symm (Fin.succ_ne_zero i)),Fin.succ_inj]
      rw [←Finset.mul_sum,ih i (fun j => B j.succ),mul_zero]

/-- Summing over independent finite samples kills an ordered product as
soon as one centered sample occurs once. The ring may be noncommutative. -/
theorem singleton_word_zero (A : X → R) (hA : ∑ x, A x=0)
    {n : ℕ} (v : Fin n → J) (i : J)
    (hi : (univ.filter fun j => v j=i).card=1) :
    (∑ a : J → X, (List.ofFn (fun j => A (a (v j)))).prod)=0 := by
  classical
  obtain ⟨p,hp⟩ := card_eq_one.mp hi
  have he (j : Fin n) : v j=i ↔ j=p := by
    simpa only [mem_filter,mem_univ,true_and,mem_singleton] using
      (show j∈univ.filter (fun j => v j=i) ↔ j∈({p}:Finset (Fin n)) by rw [hp])
  let E := Equiv.piSplitAt i (fun _ : J => X)
  rw [←Equiv.sum_comp E.symm (fun a => (List.ofFn (fun j => A (a (v j)))).prod),
    Fintype.sum_prod_type,Finset.sum_comm]
  apply sum_eq_zero
  intro b _
  let B (j : Fin n) : R := if h : v j=i then 0 else A (b ⟨v j,h⟩)
  have ht (x : X) (j : Fin n) :
      A (E.symm (x,b) (v j))=(if j=p then A x else B j) := by
    have h := E.apply_symm_apply (x,b)
    by_cases hj : j=p
    · rw [(he j).2 hj,if_pos hj]
      change A (E (E.symm (x,b))).1=A x
      exact congrArg (fun z => A z.1) h
    · have hn := mt (he j).1 hj
      simp only [if_neg hj,B,dif_neg hn]
      change A ((E (E.symm (x,b))).2 ⟨v j,hn⟩)=_
      exact congrArg (fun z => A (z.2 ⟨v j,hn⟩)) h
  simp_rw [ht]
  exact one_slot A hA p B

#print axioms singleton_word_zero
end
end GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Sampling
