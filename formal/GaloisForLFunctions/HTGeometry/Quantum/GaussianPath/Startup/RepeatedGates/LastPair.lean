import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.DisconnectedReturns.ProjectedInteractions
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.TimeOrderedCut

/-! # A nearby pair carrying a signal across the cut before the last gate -/
namespace GaloisForLFunctions.HTGeometry.RepeatedGates

/-- Across every proper path cut one can choose an ordered pair at distance
one or two whose first vertex avoids two prescribed final-gate wires. -/
theorem short_crossing_outside_pair {n : ℕ} (S : Finset (Fin (n+3)))
    (hS : S.Nonempty) (hT : Sᶜ.Nonempty) (a b : Fin (n+3)) :
    ∃ i j : Fin (n+3), i ≠ a ∧ i ≠ b ∧ ¬(i ∈ S ↔ j ∈ S) ∧
      i.val ≤ j.val+2 ∧ j.val ≤ i.val+2 := by
  obtain ⟨e,he⟩ := DisconnectedReturns.crossing_nonempty S hS hT
  have hcross := (Finset.mem_filter.mp he).2
  have hsep : e.castSucc ≠ e.succ := fun h => by
    have hv := congrArg Fin.val h
    simp at hv
  by_cases hl : e.castSucc=a ∨ e.castSucc=b
  · by_cases hr : e.succ=a ∨ e.succ=b
    · have third : ∃ w : Fin (n+3), w ≠ e.castSucc ∧ w ≠ e.succ ∧
          w.val ≤ e.val+2 ∧ e.val+1 ≤ w.val+2 := by
        by_cases hz : e.val=0
        · refine ⟨⟨2,by omega⟩,?_,?_,by simp [hz],by simp [hz]⟩
          · intro h; have hh := congrArg Fin.val h; simp [hz] at hh
          · intro h; have hh := congrArg Fin.val h; simp [hz] at hh
        · let w : Fin (n+3) := ⟨e.val-1,by omega⟩
          refine ⟨w,?_,?_,by dsimp [w]; omega,by dsimp [w]; omega⟩
          · intro h; have hh := congrArg Fin.val h
            change e.val-1=e.val at hh; omega
          · intro h; have hh := congrArg Fin.val h
            change e.val-1=e.val+1 at hh; omega
      obtain ⟨w,hwl,hwr,h₁,h₂⟩ := third
      have hab : w ≠ a ∧ w ≠ b := by
        rcases hl with hl | hl <;> rcases hr with hr | hr <;> grind
      by_cases hc : w ∈ S ↔ e.castSucc ∈ S
      · exact ⟨w,e.succ,hab.1,hab.2,fun h => hcross (hc.symm.trans h),
          by change w.val ≤ e.val+1+2; omega,h₂⟩
      · exact ⟨w,e.castSucc,hab.1,hab.2,hc,h₁,by change e.val ≤ w.val+2; omega⟩
    · exact ⟨e.succ,e.castSucc,fun h => hr (Or.inl h),fun h => hr (Or.inr h),
        fun h => hcross h.symm,by change e.val+1 ≤ e.val+2; omega,by change e.val ≤ e.val+1+2; omega⟩
  · exact ⟨e.castSucc,e.succ,fun h => hl (Or.inl h),fun h => hl (Or.inr h),
      hcross,by change e.val ≤ e.val+1+2; omega,by change e.val+1 ≤ e.val+2; omega⟩

/-- A list of at most N−1 gates omits an ordered signal between sites at
distance at most two. Only the final gate can cross a cut of the prefix. -/
theorem short_missing_ordered_pair {n : ℕ} (C : TwoQubitCircuit (n+3))
    (hc : C.gateCount ≤ n+2) :
    ∃ i j : Fin (n+3), i ≠ j ∧ i.val ≤ j.val+2 ∧ j.val ≤ i.val+2 ∧
      ∀ A B : Register (n+3), IsSiteSupported {i} A → IsSiteSupported {j} B →
        Commute (star C.eval.val*A*C.eval.val) B := by
  classical
  let q := min C.gateCount 1
  let p := C.gateCount-q
  obtain ⟨P,Q,hP,hQ,he⟩ := split_circuit (p:=p) (q:=q) C (by dsimp [p,q]; omega)
  have hp : P.gateCount+1 < n+3 := by rw [hP]; dsimp only [p,q]; omega
  obtain ⟨S,hS,hT,hcut⟩ := DisconnectedSpectra.circuit_cut P hp
  have hq : Q.gateCount ≤ 1 := hQ.trans_le (min_le_right ..)
  obtain ⟨a,b,hw⟩ : ∃ a b : Fin (n+3), ∀ k : Fin Q.gateCount, Q.architecture.sites k=(a,b) := by
    by_cases hpos : 0 < Q.gateCount
    · let l : Fin Q.gateCount := ⟨0,hpos⟩
      exact ⟨(Q.architecture.sites l).1,(Q.architecture.sites l).2,fun k => by
        have e : k=l := Fin.ext (by have := k.isLt; change k.val=0; omega)
        rw [e]⟩
    · exact ⟨0,0,fun k => by have := k.isLt; omega⟩
  obtain ⟨i,j,hia,hib,hij,h₁,h₂⟩ := short_crossing_outside_pair S hS hT a b
  have hi : i ∉ Q.touchedSites := by
    simp only [TwoQubitCircuit.touchedSites,Finset.mem_union,Finset.mem_image,
      Finset.mem_univ,true_and,hw]
    push Not
    exact ⟨fun _ => Ne.symm hia,fun _ => Ne.symm hib⟩
  refine ⟨i,j,fun h => hij (h ▸ Iff.rfl),h₁,h₂,?_⟩
  rw [he]
  by_cases hs : i ∈ S
  · exact cut_suffix_commute P Q S hcut hi hs (fun hj => hij (iff_of_true hs hj))
  · have hj : j ∈ S := by by_contra hn; exact hij (iff_of_false hs hn)
    exact cut_suffix_commute P Q Sᶜ (fun k => by simpa only [Finset.mem_compl] using (hcut k).not)
      hi (Finset.mem_compl.mpr hs) (fun h => Finset.mem_compl.mp h hj)

#print axioms short_missing_ordered_pair
end GaloisForLFunctions.HTGeometry.RepeatedGates
