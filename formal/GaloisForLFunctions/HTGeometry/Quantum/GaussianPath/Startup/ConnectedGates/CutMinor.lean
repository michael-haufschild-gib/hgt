import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.ConnectedGates.StateMinor
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.DisconnectedSpectra.Factorization

/-! # Every disconnected circuit annihilates a bond amplitude minor -/
open Matrix
open scoped Kronecker
namespace GaloisForLFunctions.HTGeometry.ConnectedGates
noncomputable section

private theorem crossing_edge {n : ℕ} (S : Finset (Fin (n+2)))
    (hS : S.Nonempty) (hB : Sᶜ.Nonempty) :
    ∃ e : Fin (n+1), ¬(e.castSucc∈S ↔ e.succ∈S) := by
  by_contra! h
  have hall (j : Fin (n+2)) : 0∈S ↔ j∈S := by
    induction j using Fin.induction with
    | zero => rfl
    | succ j ih => exact ih.trans (h j)
  obtain ⟨a,ha⟩ := hS
  obtain ⟨b,hb⟩ := hB
  exact (Finset.mem_compl.mp hb) ((hall b).mp ((hall a).mpr ha))

private theorem split_minor {N : ℕ} (i j : Fin N) (S : Finset (Fin N)) (hi : i∈S) (hj : j∉S)
    (U : Register N) (z : ℂ)
    (hf : let e := configurationSplitEquiv (fun _ : Fin N => Bool) S
          ∃ A B, Matrix.reindex e e U = A ⊗ₖ B) :
    amplitudeMinor i j (z • U)=0 := by
  obtain ⟨A,B,hAB⟩ := hf
  let r : Bits N := fun _ => false
  let e := configurationSplitEquiv (fun _ : Fin N => Bool) S
  let l (p : Bool) : LocalConfiguration (fun _ : Fin N => Bool) S :=
    fun k => if k.val=i then p else false
  let b (q : Bool) : OutsideConfiguration (fun _ : Fin N => Bool) S :=
    fun k => if k.val=j then q else false
  have hs (p q : Bool) : e (corner i j p q)=(l p,b q) := by
    apply Prod.ext
    · funext k
      have hk : k.val≠j := fun h => hj (by rw [←h]; exact k.property)
      simp [e,l,configurationSplitEquiv,restrictLocalConfiguration,corner,hk]
    · funext k
      have hk : k.val≠i := fun h => k.property (by rw [h]; exact hi)
      simp [e,b,configurationSplitEquiv,restrictOutsideConfiguration,corner,hk]
  have h (p q : Bool) : U (corner i j p q) r=A (l p) (e r).1*B (b q) (e r).2 := by
    have hx := congrArg (fun V => V (e (corner i j p q)) (e r)) hAB
    change U (e.symm (e (corner i j p q))) (e.symm (e r))=
      A (e (corner i j p q)).1 (e r).1*B (e (corner i j p q)).2 (e r).2 at hx
    rwa [Equiv.symm_apply_apply,Equiv.symm_apply_apply,hs] at hx
  simp only [amplitudeMinor,Matrix.smul_apply,smul_eq_mul]
  change z*U _ r*(z*U _ r)-z*U _ r*(z*U _ r)=0
  rw [h,h,h,h]
  ring

/-- A circuit with fewer than N−1 gates prepares an all-zero column
with a vanished two-spin minor on some physical path edge. All-to-all
circuit gates and arbitrary projective phases are allowed. -/
theorem disconnected_minor {n : ℕ} (C : TwoQubitCircuit (n+2)) (hs : C.gateCount<n+1) (z : ℂ) :
    ∃ e : Fin (n+1), amplitudeMinor e.castSucc e.succ (z • C.eval.val)=0 := by
  obtain ⟨S,hS,hB,hcut⟩ := DisconnectedSpectra.circuit_cut C (by omega)
  obtain ⟨e,he⟩ := crossing_edge S hS hB
  refine ⟨e,?_⟩
  by_cases h : e.castSucc∈S
  · exact split_minor _ _ S h (fun hh => he ⟨fun _ => hh,fun _ => h⟩) _ z
      (DisconnectedSpectra.factor_on_cut C S hcut)
  · have h' : e.succ∈S := by by_contra hn; exact he (iff_of_false h hn)
    apply split_minor _ _ Sᶜ (Finset.mem_compl.mpr h) (fun hh => Finset.mem_compl.mp hh h') _ z
    apply DisconnectedSpectra.factor_on_cut
    intro k
    simpa only [Finset.mem_compl] using (hcut k).not

#print axioms disconnected_minor
end
end GaloisForLFunctions.HTGeometry.ConnectedGates
