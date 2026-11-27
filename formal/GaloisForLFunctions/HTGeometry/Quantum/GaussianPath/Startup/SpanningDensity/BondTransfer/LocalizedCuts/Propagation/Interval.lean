import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Disorder.Rows.Incidence
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.IncidentSupport

/-! # Width and interaction mass of a bond neighborhood -/
open Finset
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open RepeatedGates.PhysicalBlocks.CollectiveSignals
noncomputable section
variable {n : ℕ}

/-- The p-fold interaction neighborhood of both endpoints of a bond. -/
def bondNeighborhood (e : Fin (n+1)) (p : ℕ) :=
  incidentSites^[p] ({e.castSucc,e.succ} : Finset (Fin (n+2)))

theorem bondNeighborhood_succ (e : Fin (n+1)) (p : ℕ) :
    bondNeighborhood e (p+1)=incidentSites (bondNeighborhood e p) :=
  Function.iterate_succ_apply' ..

theorem bondNeighborhood_contains (e : Fin (n+1)) (p : ℕ) :
    ({e.castSucc,e.succ} : Finset _)⊆bondNeighborhood e p := by
  induction p with
  | zero => exact Subset.rfl
  | succ p ih => rw [bondNeighborhood_succ]; exact ih.trans subset_union_left

theorem bondNeighborhood_range (e : Fin (n+1)) (p : ℕ) {v : Fin (n+2)}
    (hv : v∈bondNeighborhood e p) : e.val≤v.val+p ∧ v.val≤e.val+1+p := by
  induction p generalizing v with
  | zero =>
    change v∈({e.castSucc,e.succ} : Finset _) at hv
    rcases mem_insert.mp hv with rfl|h
    · simp
    · obtain rfl := mem_singleton.mp h
      simp
  | succ p ih =>
    change v∈incidentSites^[p+1] _ at hv
    rw [Function.iterate_succ_apply'] at hv
    rcases mem_union.mp hv with h|h
    · have := ih h
      omega
    · obtain ⟨l,hl,hv'⟩ := mem_biUnion.mp h
      obtain ⟨w,hw,hl'⟩ := mem_biUnion.mp hl
      have h₁ := ih hw
      have h₂ := source_row_at_site (mem_filter.mp hl').2
      have h₃ := source_row_at_site (v:=v) (l:=l) (by
        by_contra hn
        exact (mem_labelSupport.mp hv') (pathWord_none_of_not_incidentSite v l hn))
      omega

theorem bondNeighborhood_card (e : Fin (n+1)) (p : ℕ) :
    (bondNeighborhood e p).card≤2*p+2 := by
  have h : (bondNeighborhood e p).card≤(range (2*p+2)).card := by
    apply card_le_card_of_injOn (fun v : Fin (n+2) => v.val+p-e.val)
    · intro v hv
      have := bondNeighborhood_range e p hv
      exact mem_range.mpr (by omega)
    · intro v hv w hw h
      have := bondNeighborhood_range e p hv
      have := bondNeighborhood_range e p hw
      exact Fin.ext (by change v.val+p-e.val=w.val+p-e.val at h; omega)
  rwa [card_range] at h

/-- Bounds include the chain endpoints without extra boundary terms. -/
theorem bondNeighborhood_mass (e : Fin (n+1)) (p : ℕ) (u : PathShell n) {B : ℝ}
    (hB : 0≤B) (h : ∀ l∈(bondNeighborhood e p).biUnion pathIncidentLabels, |u l|≤B) :
    (∑ l∈(bondNeighborhood e p).biUnion pathIncidentLabels, |u l|)≤(21*(2*(p:ℝ)+2))*B := by
  let I := (bondNeighborhood e p).biUnion pathIncidentLabels
  have hc : I.card≤21*(2*p+2) := (pathIncident_union_card _).trans
    (Nat.mul_le_mul_left 21 (bondNeighborhood_card e p))
  calc
    _ ≤ ∑ _l∈I, B := sum_le_sum h
    _ = (I.card:ℝ)*B := by rw [sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hB

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
