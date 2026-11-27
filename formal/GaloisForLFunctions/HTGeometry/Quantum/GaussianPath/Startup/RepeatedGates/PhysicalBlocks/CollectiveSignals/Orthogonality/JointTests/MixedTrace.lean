import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.ForestOrder.Directed.Feedback
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.Orthogonality.PacketFamily

/-! # All mixed moments vanish within an ordered class of Choi tests -/
open Matrix Finset
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
open Temporal Feedback ForestOrder
open private probe_supported from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.RequiredPairs
noncomputable section
variable {J A : Type*} [Ring A]

private theorem commute_product (B : J→A) (Q : A) (l : List J) (h : ∀ i∈l, Commute (B i) Q) :
    Commute (l.map B).prod Q := by
  induction l with
  | nil => exact Commute.one_left _
  | cons i l ih => exact (h i List.mem_cons_self).mul_left (ih fun j hj => h j (List.mem_cons_of_mem _ hj))

private theorem flip_product (B : J→A) (Q : A) (l : List J) {j : J} (hj : j∈l)
    (hn : l.Nodup) (ha : Q*B j=-(B j*Q)) (hc : ∀ i∈l, i≠j → Commute (B i) Q) :
    Q*(l.map B).prod= -((l.map B).prod*Q) := by
  induction l with
  | nil => cases hj
  | cons i l ih =>
    obtain ⟨hnot,hnd⟩ := List.nodup_cons.mp hn
    simp only [List.map_cons,List.prod_cons]
    by_cases he : i=j
    · subst i
      have hrest := commute_product B Q l (fun k hk => hc k (List.mem_cons_of_mem _ hk) (fun he => hnot (he ▸ hk)))
      rw [←mul_assoc,ha,neg_mul,mul_assoc,hrest.symm.eq,mul_assoc]
    · have hh := ih ((List.mem_cons.mp hj).resolve_left he.symm) hnd
        (fun k hk => hc k (List.mem_cons_of_mem _ hk))
      rw [←mul_assoc,(hc i List.mem_cons_self he).symm.eq,mul_assoc,hh,mul_neg,mul_assoc]

/-- For every nonempty list of distinct tests whose cross-connections
have increasing rank, the trace of the product of the associated Choi
observables on the circuit vanishes. List order may be arbitrary. -/
theorem ordered_packet_mixed_trace {n : ℕ} (C : TwoQubitCircuit (n+2))
    (e f : J→Fin (n+1)) (x y : J→Fin (n+2)) (ha : ∀ i, (e i).succ=(f i).castSucc)
    (hx : ∀ i, x i∈tripleSites (e i) (f i)) (hy : ∀ i, y i∈tripleSites (e i) (f i))
    (hd : ∀ i j, i≠j → Disjoint (tripleSites (e i) (f i)) (tripleSites (e j) (f j)))
    (z : J→ℤ) (l : List J) (hn : l.Nodup) (hne : l≠[])
    (hz : ∀ i∈l, ∀ j∈l, x i∈inputs (circuitWord C) (y j) → z i<z j) :
    let P i := star C.eval.val*packetProbe (e i) (x i)*C.eval.val
    let B i := packetImage (e i) (f i) (x i)
    ((l.map P).prod*(l.map B).prod).trace=0 := by
  classical
  intro P B
  have hnon : l.toFinset.Nonempty := by
    cases l with
    | nil => exact (hne rfl).elim
    | cons i l => exact ⟨i,List.mem_toFinset.mpr List.mem_cons_self⟩
  obtain ⟨j,hj,hm⟩ := least_sink z (fun i j => x i∈inputs (circuitWord C) (y j)) l.toFinset hnon
    (fun i hi j hj => hz i (List.mem_toFinset.mp hi) j (List.mem_toFinset.mp hj))
  let Q := packetProbe (e j) (y j)
  have hQ := probe_supported (y j) (tripleAxis (e j) (y j))
  have hPP (i) (hi : i∈l) : Commute (P i) Q := commute_of_absent C _ _ (hm i (List.mem_toFinset.mpr hi))
    _ _ (probe_supported _ _) hQ
  have hne' : x j≠y j := fun he => hm j hj (he ▸ knows_self _ _)
  have hBB (i) (_ : i∈l) (hi : i≠j) : Commute (B i) Q :=
    commute_of_isSiteSupported_disjoint ((hd i j hi).mono_right (singleton_subset_iff.mpr (hy j)))
      (packetImage_supported (ha i) (hx i)) hQ
  exact trace_zero_of_flip _ _ Q (commute_product P Q l hPP) (finitePauliMatrix_mul_self _)
    (flip_product B Q l (List.mem_toFinset.mp hj) hn (packetImage_flip (ha j) (hx j) (hy j) hne') hBB)

#print axioms ordered_packet_mixed_trace
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
