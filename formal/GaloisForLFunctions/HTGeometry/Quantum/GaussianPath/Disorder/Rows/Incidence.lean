import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IncidentPauliTerms
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PauliThresholdObstruction

/-! # Source rows neighboring a physical site or bond -/
open Finset
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {n : ℕ}

/-- An incident Pauli term starts at the site itself or its predecessor. -/
theorem source_row_at_site {v : Fin (n+2)} {l : PathLabel n} (h : pathIncident v l) :
    let b := (pathPauliSourceCoordinate l).1
    b≤v.val ∧ v.val≤b+1 := by
  rcases l with ⟨s,a⟩|⟨r,ab⟩
  · change s=v at h
    subst v
    exact ⟨le_rfl,Nat.le_succ _⟩
  · change r.castSucc=v ∨ r.succ=v at h
    rcases h with rfl|rfl
    · exact ⟨le_rfl,Nat.le_succ _⟩
    · exact ⟨Nat.le_succ _,le_rfl⟩

/-- At either end of a physical edge, every incident term starts within
one row of the edge. -/
theorem source_row_at_edge {e : Fin (n+1)} {l : PathLabel n}
    (hl : l∈({e.castSucc,e.succ}:Finset _).biUnion pathIncidentLabels) :
    let r := (pathPauliSourceCoordinate l).1
    r≤e.val+1 ∧ e.val≤r+1 := by
  classical
  obtain ⟨v,hv,hl⟩ := mem_biUnion.mp hl
  obtain ⟨ha,hb⟩ := source_row_at_site (mem_filter.mp hl).2
  simp only [mem_insert,mem_singleton] at hv
  rcases hv with rfl|rfl <;> simp only [Fin.val_succ,Fin.val_castSucc] at ha hb <;> omega

end
end GaloisForLFunctions.HTGeometry
