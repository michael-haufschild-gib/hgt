import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.DisconnectedReturns.CutProjection
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.DisconnectedReturns.GaussianCommutant
import GaloisForLFunctions.HTGeometry.FiniteQubitPauliBasisLaw

/-! # The mixed projection selects exactly the physical bonds crossing the bipartition -/
open Matrix
open scoped Kronecker
namespace GaloisForLFunctions.HTGeometry.DisconnectedReturns
noncomputable section
open _root_.HTGeometry.ConstraintRelativity
variable {N : ℕ}

private theorem split_word (S : Finset (Fin N)) (p : Fin N→Option (Fin 3)) :
    let e := configurationSplitEquiv (fun _ : Fin N => Bool) S
    Matrix.reindex e e (finitePauliMatrix p) =
      finitePauliMatrix (fun i : S => p i.val) ⊗ₖ finitePauliMatrix (fun i : {v // v∉S} => p i.val) := by
  intro e
  ext u v
  obtain ⟨x,rfl⟩ := e.surjective u
  obtain ⟨y,rfl⟩ := e.surjective v
  change finitePauliMatrix p (e.symm (e x)) (e.symm (e y))=_
  rw [e.symm_apply_apply,e.symm_apply_apply]
  let f (i : Fin N) := boolPauliOptionEntry (p i) (x i,y i)
  change (∏ i, f i)=(∏ i : S, f i.val)*∏ i : {v // v∉S}, f i.val
  symm
  convert! Fintype.prod_subtype_mul_prod_subtype (fun i => i∈S) f using 3
  exact congrArg (fun i : Fintype S => @Finset.univ S i) (Subsingleton.elim _ _)

private theorem center_word {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι→Option (Fin 3)) :
    traceCenter (finitePauliMatrix p)=if p=(fun _ => none) then 0 else finitePauliMatrix p := by
  classical
  by_cases h : p=fun _ => none
  · subst p
    rw [if_pos rfl,finitePauliMatrix_const_none]
    simp [traceCenter]
  · simp [h,traceCenter,finitePauliMatrix_trace_eq_zero_of_ne_identity p h]

private def bothSides (S : Finset (Fin N)) (p : Fin N→Option (Fin 3)) : Prop :=
  (∃ v∈S, p v≠none) ∧ (∃ v∉S, p v≠none)

open Classical in
private theorem projection_word (S : Finset (Fin N)) (p : Fin N→Option (Fin 3)) :
    cutProjection S (finitePauliMatrix p) =
      if bothSides S p then finitePauliMatrix p else 0 := by
  classical
  let e := configurationSplitEquiv (fun _ : Fin N => Bool) S
  let Φ := Matrix.reindexAlgEquiv ℂ ℂ e
  let a (i : S) := p i.val
  let b (i : {v // v∉S}) := p i.val
  have h : Φ (finitePauliMatrix p)=finitePauliMatrix a ⊗ₖ finitePauliMatrix b := split_word S p
  have hs : bothSides S p ↔ a≠(fun _ => none) ∧ b≠(fun _ => none) := by
    simp only [bothSides,Function.ne_iff,a,b]
    constructor
    · rintro ⟨⟨v,hv,ha⟩,⟨w,hw,hb⟩⟩
      exact ⟨⟨⟨v,hv⟩,ha⟩,⟨⟨w,hw⟩,hb⟩⟩
    · rintro ⟨⟨⟨v,hv⟩,ha⟩,⟨⟨w,hw⟩,hb⟩⟩
      exact ⟨⟨v,hv,ha⟩,⟨w,hw,hb⟩⟩
  apply Φ.injective
  rw [show Φ (cutProjection S (finitePauliMatrix p))=crossMatrixPart (Φ (finitePauliMatrix p)) from
    Φ.apply_symm_apply _,h,crossMatrixPart_kronecker,center_word,center_word]
  by_cases ha : a=fun _ => none <;> by_cases hb : b=fun _ => none <;>
    simp [hs,ha,hb,h]

def crossingEdges {n : ℕ} (S : Finset (Fin (n+2))) : Finset (Fin (n+1)) :=
  Finset.univ.filter fun e => ¬(e.castSucc∈S ↔ e.succ∈S)

private theorem bothSides_iff {n : ℕ} (S : Finset (Fin (n+2))) (l : PathLabel n) :
    bothSides S (pathWord l) ↔ selected (crossingEdges S) l=true := by
  rcases l with ⟨v,a⟩ | ⟨e,a,b⟩
  · have hv (i : Fin (n+2)) : pathWord (.inl (v,a)) i≠none ↔ i=v := by
      by_cases h : i=v <;> simp [pathWord,onsiteWord,h]
    simp only [bothSides,hv,exists_eq_right,selected,Bool.false_eq_true,iff_false,not_and]
    exact fun h hn => hn h
  · have hv (i : Fin (n+2)) : pathWord (.inr (e,a,b)) i≠none ↔ i=e.castSucc ∨ i=e.succ := by
      by_cases hl : i=e.castSucc
      · simp [pathWord,couplingWord,hl]
      · simp only [pathWord,couplingWord,hl,false_or]
        by_cases hr : i=e.succ <;> simp [hr]
    have exists_end (P : Fin (n+2)→Prop) :
        (∃ i, P i ∧ pathWord (.inr (e,a,b)) i≠none) ↔ P e.castSucc ∨ P e.succ := by
      simp only [hv,and_or_left,exists_or,exists_eq_right]
    simp only [bothSides,exists_end,selected,decide_eq_true_eq,crossingEdges,Finset.mem_filter,
      Finset.mem_univ,true_and]
    tauto

/-- Projection before or after summing the Hamiltonian gives precisely
its crossing interactions, with no contribution from onsite terms. -/
theorem projection_hamiltonian {n : ℕ} (S : Finset (Fin (n+2))) (u : PathShell n) :
    cutProjection S (pathHamiltonian u)=bondPart u (crossingEdges S) := by
  classical
  rw [pathHamiltonian_eq_sum,map_sum,bondPart_eq_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [map_smul,projection_word]
  simp only [bothSides_iff]

theorem crossing_nonempty {n : ℕ} (S : Finset (Fin (n+2))) (hs : S.Nonempty)
    (ht : Sᶜ.Nonempty) : (crossingEdges S).Nonempty := by
  classical
  by_contra h
  have step (e : Fin (n+1)) : e.castSucc∈S ↔ e.succ∈S := by
    by_contra hh
    exact h ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩⟩
  have conn (v : Fin (n+2)) : 0∈S ↔ v∈S := by
    induction v using Fin.induction with
    | zero => rfl
    | succ e ih => exact ih.trans (step e)
  obtain ⟨i,hi⟩ := hs
  obtain ⟨j,hj⟩ := ht
  exact (Finset.mem_compl.mp hj) ((conn j).mp ((conn i).mpr hi))

#print axioms projection_hamiltonian
end
end GaloisForLFunctions.HTGeometry.DisconnectedReturns
