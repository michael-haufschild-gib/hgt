import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.DisconnectedSpectra.CircuitCut
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitDeletionBound
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.OneGate
import GaloisForLFunctions.HTGeometry.LocalMatrixTensorFactorization

/-! # Physical matrix factorization across a cut of the gate architecture -/
open Matrix
open scoped Kronecker
namespace GaloisForLFunctions.HTGeometry.DisconnectedSpectra
noncomputable section

private theorem supported_gate {N : ℕ} (a b : Fin N) (hab : a≠b)
    (U : Matrix.specialUnitaryGroup (Bool×Bool) ℂ) (S : Finset (Fin N)) (ha : a∈S) (hb : b∈S) :
    IsSiteSupported (A:=fun _ : Fin N => Bool) S (twoQubitLift a b hab U).val := by
  let C := TwoQubitCircuit.singleOn a b hab U
  have h : C.touchedSites ⊆ S := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
      exact ha
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
      exact hb
  simpa only [C,TwoQubitCircuit.singleOn_eval] using C.isSiteSupported_touchedSites.mono h

/-- Gates entirely on either side become tensor factors after splitting
the register. Ordered multiplication preserves the factorization. -/
theorem factor_on_cut {N : ℕ} (C : TwoQubitCircuit N) (S : Finset (Fin N))
    (hcut : ∀ i : Fin C.gateCount, (C.architecture.sites i).1∈S ↔ (C.architecture.sites i).2∈S) :
    let e := configurationSplitEquiv (fun _ : Fin N => Bool) S
    ∃ A B, Matrix.reindex e e C.eval.val=A ⊗ₖ B := by
  classical
  intro e
  let Φ := Matrix.reindexAlgEquiv ℂ ℂ e
  let P (U : Matrix.unitaryGroup (Fin N→Bool) ℂ) := ∃ A B, Φ U.val=A ⊗ₖ B
  have hprod (l : List (Matrix.unitaryGroup (Fin N→Bool) ℂ)) (hl : ∀ U∈l, P U) : P l.prod := by
    induction l with
    | nil => exact ⟨1,1,(map_one Φ).trans one_kronecker_one.symm⟩
    | cons U l ih =>
      obtain ⟨A,B,h⟩ := hl U List.mem_cons_self
      obtain ⟨F,G,h'⟩ := ih fun W hW => hl W (List.mem_cons_of_mem _ hW)
      exact ⟨A*F,B*G,by change Φ (U.val*l.prod.val)=_; rw [map_mul,h,h',mul_kronecker_mul]⟩
  apply hprod (List.ofFn (fun i => C.architecture.gateLift i (C.gates i))).reverse
  intro U hU
  rw [List.mem_reverse,List.mem_ofFn] at hU
  obtain ⟨i,rfl⟩ := hU
  let a := (C.architecture.sites i).1
  let b := (C.architecture.sites i).2
  let u := twoQubitLift a b (C.architecture.distinct i) (C.gates i)
  by_cases ha : a∈S
  · obtain ⟨M,hM⟩ := exists_liftLocalMatrix_of_isSiteSupported (supported_gate a b _ _ S ha ((hcut i).mp ha))
    refine ⟨M,1,?_⟩
    change Φ u.val=_
    rw [hM]
    exact reindex_liftLocalMatrix_eq_kronecker_one S M
  · have h₁ : a∈Sᶜ := Finset.mem_compl.mpr ha
    have h₂ : b∈Sᶜ := Finset.mem_compl.mpr (fun hb => ha ((hcut i).mpr hb))
    obtain ⟨M,hM⟩ := exists_liftLocalMatrix_of_isSiteSupported (supported_gate a b _ _ Sᶜ h₁ h₂)
    refine ⟨1,_,?_⟩
    change Φ u.val=_
    rw [hM]
    exact reindex_liftLocalMatrix_disjoint_eq_one_kronecker disjoint_compl_right M

/-- Every circuit below N−1 gates on at least three qubits has a tensor
factorization with at least one qubit on the left and two on the right. -/
theorem disconnected_factor {N : ℕ} (hN : 3≤N) (C : TwoQubitCircuit N) (hc : C.gateCount+1<N) :
    ∃ S : Finset (Fin N), 1 ≤ S.card ∧ 2 ≤ Sᶜ.card ∧
      let e := configurationSplitEquiv (fun _ : Fin N => Bool) S
      ∃ A B, Matrix.reindex e e C.eval.val=A ⊗ₖ B := by
  obtain ⟨S,hs,ht,hcut⟩ := circuit_cut C hc
  by_cases h : 2 ≤ Sᶜ.card
  · exact ⟨S,Finset.card_pos.mpr hs,h,factor_on_cut C S hcut⟩
  · have hS : 2 ≤ S.card := by
      rw [Finset.card_compl,Fintype.card_fin] at h
      omega
    refine ⟨Sᶜ,Finset.card_pos.mpr ht,by simpa using hS,factor_on_cut C Sᶜ ?_⟩
    intro i
    simpa only [Finset.mem_compl] using (hcut i).not

#print axioms disconnected_factor
end
end GaloisForLFunctions.HTGeometry.DisconnectedSpectra
