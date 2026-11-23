import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.IntermediateComponents.Incidence
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.CausalSupport

/-! # A quadratic deficit of directed signals below two gates per wire -/
open Matrix Finset
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal
noncomputable section

/-- Split the gate list at any date. The product of the two remaining
component deficits bounds the number of causally missing pairs plus N. -/
theorem circuit_pair_deficit {N : ℕ} (C : TwoQubitCircuit N) (p q : ℕ) (h : C.gateCount=p+q) :
    (N-p)*(N-q) ≤ N+(absentPairs (circuitWord C)).card := by
  let w := circuitWord C
  have hw : w.length=p+q := (circuitWord_length C).trans h
  have hp : (w.take p).length=p := by simp [List.length_take,hw]
  have hq : (w.drop p).length=q := by simp [hw]
  simpa only [List.take_append_drop,hp,hq,Fintype.card_fin] using absent_pairs_of_lengths (w.take p) (w.drop p)

/-- If the cut has more potential label pairs than intermediate wires,
some ordered pair cannot signal for any choice of its local probes. -/
theorem missing_pair_of_component_product {N : ℕ} (C : TwoQubitCircuit N) (p q : ℕ)
    (h : C.gateCount=p+q) (hx : N<(N-p)*(N-q)) :
    ∃ i j : Fin N, i≠j ∧ ∀ A B : Register N, IsSiteSupported {i} A → IsSiteSupported {j} B →
      Commute (star C.eval.val*A*C.eval.val) B := by
  have hd := circuit_pair_deficit C p q h
  obtain ⟨⟨j,i⟩,hp⟩ := card_pos.mp (by omega : 0<(absentPairs (circuitWord C)).card)
  have hm : i∉inputs (circuitWord C) j := (mem_filter.mp hp).2
  exact ⟨i,j,by rintro rfl; exact hm (knows_self _ _),commute_of_absent C i j hm⟩

#print axioms circuit_pair_deficit
#print axioms missing_pair_of_component_product
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal
