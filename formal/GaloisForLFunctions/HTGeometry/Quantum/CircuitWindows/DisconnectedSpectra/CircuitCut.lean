import GaloisForLFunctions.HTGeometry.HaferkampExactCircuitComplexity

/-! # A separated bipartition for every circuit with fewer than N−1 gates -/
namespace GaloisForLFunctions.HTGeometry.DisconnectedSpectra
noncomputable section

/-- Record one reference bit and the parity across every gate. When the
record has fewer than N bits, two configurations have the same record.
Their disagreement set is nonempty, proper, and crossed by no gate. -/
theorem circuit_cut {N : ℕ} (C : TwoQubitCircuit N) (hs : C.gateCount+1<N) :
    ∃ S : Finset (Fin N), S.Nonempty ∧ Sᶜ.Nonempty ∧ ∀ i : Fin C.gateCount,
      (C.architecture.sites i).1∈S ↔ (C.architecture.sites i).2∈S := by
  classical
  let ref : Fin N := ⟨0,by omega⟩
  let code (x : Fin N→Bool) : Bool × (Fin C.gateCount→Bool) :=
    (x ref,fun i => xor (x (C.architecture.sites i).1) (x (C.architecture.sites i).2))
  have hn : ¬Function.Injective code := by
    intro h
    have hc := Fintype.card_le_of_injective code h
    simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_prod,Fintype.card_bool] at hc
    exact (Nat.pow_lt_pow_right (by decide : 1<2) hs).not_ge
      (by simpa only [pow_succ,Nat.mul_comm] using hc)
  unfold Function.Injective at hn
  push_neg at hn
  obtain ⟨x,y,hxy,hn⟩ := hn
  let S := Finset.univ.filter fun i => x i≠y i
  have hne : ∃ i, x i≠y i := by
    by_contra! he
    exact hn (funext he)
  obtain ⟨j,hj⟩ := hne
  have href : x ref=y ref := congrArg Prod.fst hxy
  refine ⟨S,⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩,⟨ref,?_⟩,?_⟩
  · exact Finset.mem_compl.mpr fun h => (Finset.mem_filter.mp h).2 href
  · intro i
    have he := congrFun (congrArg Prod.snd hxy) i
    let a := (C.architecture.sites i).1
    let b := (C.architecture.sites i).2
    change xor (x a) (x b)=xor (y a) (y b) at he
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
    change (x a≠y a) ↔ (x b≠y b)
    cases x a <;> cases x b <;> cases y a <;> cases y b <;> simp_all

#print axioms circuit_cut
end
end GaloisForLFunctions.HTGeometry.DisconnectedSpectra
