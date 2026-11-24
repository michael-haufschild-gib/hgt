import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Rank.NecessaryOrder.Symmetry
import Mathlib.Data.Sym.Card

/-! # Counting independent spectral responses at a given derivative order -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.NecessaryOrder
noncomputable section
variable {m D L : ℕ}

private def padded (w : List (Fin m)) (hw : w.length≤L) : Sym (Option (Fin m)) L :=
  Sym.mk ((List.replicate (L-w.length) none ++ w.map some : List (Option (Fin m))) : Multiset _) (by
    change (List.replicate (L-w.length) (none : Option (Fin m)) ++ w.map some).length=L
    simp only [List.length_append,List.length_replicate,List.length_map,Nat.sub_add_cancel hw])

private theorem unpad (w : List (Fin m)) (b : ℕ) :
    (List.replicate b (none : Option (Fin m)) ++ w.map some).filterMap id=w := by
  have h (u : List (Fin m)) : (u.map some).filterMap id=u := by simp
  induction b with
  | zero => simpa only [List.replicate_zero,List.nil_append] using h w
  | succ b ih =>
    rw [List.replicate_succ]
    exact ih

private theorem perm_of_pad {u v : List (Fin m)} {hu : u.length≤L} {hv : v.length≤L}
    (h : padded u hu=padded v hv) : u.Perm v := by
  have h' : (List.replicate (L-u.length) none ++ u.map some).Perm
      (List.replicate (L-v.length) none ++ v.map some) :=
    Multiset.coe_eq_coe.mp (congrArg Sym.toMultiset h)
  simpa only [unpad] using h'.filterMap id

/-- Even when every physical coordinate is available, the constant row
and derivatives through order L occupy at most one plus the number of
multisets of length at most L on m letters. -/
theorem ambient_order_bound (k : Fin D) (w : Fin D→List (Fin m)) (hw : ∀ i, (w i).length≤L)
    (E : Fin D→(Fin m→ℝ)→ℝ) (x : Fin m→ℝ) (hE : ∀ j, AnalyticAt ℝ (E j) x)
    (hd : (of fun i j => if i=k then (1:ℝ) else realMixed (w i) (E j) x).det≠0) :
    D≤(m+L).choose L+1 := by
  classical
  let f (i : Fin D) : Option (Sym (Option (Fin m)) L) := if i=k then none else some (padded (w i) (hw i))
  have hin : Function.Injective f := by
    intro i l hil
    by_contra hne
    apply hd (Matrix.det_zero_of_row_eq hne (funext fun j => ?_))
    by_cases hi : i=k <;> by_cases hl : l=k
    · exact (hne (hi.trans hl.symm)).elim
    · simp [f,hi,hl] at hil
    · simp [f,hi,hl] at hil
    · have h := Option.some.inj (show some (padded (w i) (hw i))=some (padded (w l) (hw l)) by
        simpa only [f,if_neg hi,if_neg hl] using hil)
      simpa only [of_apply,if_neg hi,if_neg hl] using realMixed_perm (perm_of_pad h) (hE j)
  have h := Fintype.card_le_of_injective f hin
  simpa only [Fintype.card_fin,Fintype.card_option,Sym.card_sym_eq_choose,
    show m+1+L-1=m+L by omega] using h

#print axioms ambient_order_bound
end
end GaloisForLFunctions.HTGeometry.SpectralJets.NecessaryOrder
