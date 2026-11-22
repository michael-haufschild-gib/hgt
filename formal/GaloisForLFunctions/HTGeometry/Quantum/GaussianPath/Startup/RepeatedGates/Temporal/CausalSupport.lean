import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Calls
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.TimeOrderedCut

/-! # Support propagation through chronological two-wire gates -/
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
  exact (active_mem ..).mpr (inputs_mono e w j ((active_mem ..).mp hj))

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
    have hgate : Q.eval=C.architecture.gateLift k (C.gates k) := TwoQubitCircuit.singleOn_eval ..
    rw [hgate] at hh
    simp only [List.map_cons,List.reverse_cons,List.prod_append,List.prod_singleton,Submonoid.coe_mul,star_mul]
    change IsSiteSupported S (star (C.architecture.gateLift k (C.gates k)).val*star P.val*A*(P.val*(C.architecture.gateLift k (C.gates k)).val))
    simpa only [mul_assoc] using hh

/-- An output always retains its own input. -/
theorem knows_self (w : List (Fin N×Fin N)) (i : Fin N) : i∈inputs w i := by
  induction w with
  | nil => exact Finset.mem_singleton_self i
  | cons e w ih => exact (active_mem ..).mp (active_mono e w i ((active_mem ..).mpr ih))

/-- Read sites in the order for propagating conjugated output observables. -/
def circuitWord (C : TwoQubitCircuit N) : List (Fin N×Fin N) :=
  (List.ofFn (id : Fin C.gateCount→Fin C.gateCount)).map C.architecture.sites

theorem circuitWord_length (C : TwoQubitCircuit N) : (circuitWord C).length=C.gateCount := by
  simp [circuitWord]

/-- An absent temporal input gives exactly zero signal for all choices of gates. -/
theorem commute_of_absent (C : TwoQubitCircuit N) (i j : Fin N) (hm : i∉inputs (circuitWord C) j)
    (A B : Register N) (hA : IsSiteSupported {i} A) (hB : IsSiteSupported {j} B) :
    Commute (star C.eval.val*A*C.eval.val) B := by
  let ks := List.ofFn (id : Fin C.gateCount→Fin C.gateCount)
  have hh := conjugate_word C ks i A hA
  have hu : (ks.map fun k => C.architecture.gateLift k (C.gates k)).reverse.prod=C.eval := by
    simp only [ks,List.map_ofFn,Function.comp_id]; rfl
  rw [hu] at hh
  exact commute_of_isSiteSupported_disjoint (Finset.disjoint_singleton_right.mpr (fun hj => hm ((active_mem ..).mp hj))) hh hB

/-- Failure to exchange all inputs at distance at most two supplies a
specific absent directional signal between distinct sites. -/
theorem missing_of_incomplete (C : TwoQubitCircuit N)
    (h : ¬(∀ i j : Fin N, i.val ≤ j.val+2 → j.val ≤ i.val+2 → j∈inputs (circuitWord C) i)) :
    ∃ i j : Fin N, i≠j ∧ i.val ≤ j.val+2 ∧ j.val ≤ i.val+2 ∧
      ∀ A B : Register N, IsSiteSupported {i} A → IsSiteSupported {j} B →
        Commute (star C.eval.val*A*C.eval.val) B := by
  push Not at h
  obtain ⟨j,i,h₁,h₂,hm⟩ := h
  exact ⟨i,j,fun he => hm (he ▸ knows_self _ j),h₂,h₁,commute_of_absent C i j hm⟩

end
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal
