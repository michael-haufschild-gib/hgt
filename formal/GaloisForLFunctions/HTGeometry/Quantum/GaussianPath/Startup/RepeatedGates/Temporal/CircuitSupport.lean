import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.TriplePacking
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.TimeOrderedCut

/-! # Temporal input sets enclose the support of conjugated observables -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal
noncomputable section
variable {N : ℕ}

private def active (w : List (Fin N×Fin N)) (i : Fin N) := Finset.univ.filter fun j => i∈inputs w j

private theorem active_mem (w : List (Fin N×Fin N)) (i j : Fin N) : j∈active w i ↔ i∈inputs w j := by
  simp [active]

private theorem active_mono (e : Fin N×Fin N) (w : List (Fin N×Fin N)) (i : Fin N) :
    active w i ⊆ active (e::w) i := by
  intro j hj
  have h := (active_mem ..).mp hj
  apply (active_mem ..).mpr
  by_cases he : j=e.1 ∨ j=e.2
  · rw [inputs,if_pos he,Finset.mem_union]; rcases he with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h
  · simpa only [inputs,if_neg he] using h

private theorem conjugate_word (C : TwoQubitCircuit N) (ks : List (Fin C.gateCount)) (i : Fin N)
    (A : Register N) (hA : IsSiteSupported {i} A) :
    let U := (ks.map (fun k => C.architecture.gateLift k (C.gates k))).reverse.prod
    IsSiteSupported (active (ks.map C.architecture.sites) i) (star U.val*A*U.val) := by
  induction ks with
  | nil =>
    simp only [List.map_nil,List.reverse_nil,List.prod_nil,Submonoid.coe_one,star_one,one_mul,mul_one]
    exact hA.mono (Finset.singleton_subset_iff.mpr ((active_mem ..).mpr (Finset.mem_singleton_self _)))
  | cons k ks ih =>
    let e := C.architecture.sites k
    let w := ks.map C.architecture.sites
    let S := active (e::w) i
    let P := (ks.map fun p => C.architecture.gateLift p (C.gates p)).reverse.prod
    let Q := TwoQubitCircuit.singleOn e.1 e.2 (C.architecture.distinct k) (C.gates k)
    have he : e.1∈S ↔ e.2∈S := by simp [S,active_mem,inputs]
    have hh := SpanningDensity.circuit_conjugate_supported Q S (fun _ => he)
      (star P.val*A*P.val) (ih.mono (active_mono e w i))
    rw [TwoQubitCircuit.singleOn_eval] at hh
    simpa only [List.map_cons,List.reverse_cons,List.prod_append,List.prod_singleton,Submonoid.coe_mul,star_mul,mul_assoc]
      using hh

private theorem knows_self (w : List (Fin N×Fin N)) (i : Fin N) : i∈inputs w i := by
  induction w with
  | nil => exact Finset.mem_singleton_self i
  | cons e w ih => exact (active_mem ..).mp (active_mono e w i ((active_mem ..).mpr ih))

/-- Below the packing bound some ordered pair at physical distance one
or two has exactly zero signal for every pair of local observables. -/
theorem missing_short_signal (C : TwoQubitCircuit N) (hc : 2*(C.gateCount+1)<2*N+N/3) :
    ∃ i j : Fin N, i≠j ∧ i.val≤j.val+2 ∧ j.val≤i.val+2 ∧
      ∀ A B : Register N, IsSiteSupported {i} A → IsSiteSupported {j} B →
        Commute (star C.eval.val*A*C.eval.val) B := by
  classical
  let ks := List.ofFn (id : Fin C.gateCount→Fin C.gateCount)
  let w := ks.map C.architecture.sites
  have hlen : w.length=C.gateCount := by simp [w,ks]
  have hex : ¬(∀ i j : Fin N, i.val≤j.val+2 → j.val≤i.val+2 → j∈inputs w i) := by
    intro h
    have hb := path_exchange_budget w h
    rw [hlen] at hb
    exact hc.not_ge hb
  push_neg at hex
  obtain ⟨j,i,h₁,h₂,hm⟩ := hex
  refine ⟨i,j,fun h => hm (h ▸ knows_self w j),h₂,h₁,?_⟩
  intro A B hA hB
  have hh := conjugate_word C ks i A hA
  have hu : (ks.map fun k => C.architecture.gateLift k (C.gates k)).reverse.prod=C.eval := by
    simp only [ks,List.map_ofFn,Function.comp_id]; rfl
  rw [hu] at hh
  exact commute_of_isSiteSupported_disjoint (Finset.disjoint_singleton_right.mpr (fun hj => hm ((active_mem ..).mp hj))) hh hB

end
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal
