import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.FiniteTransitions

/-! # Finite schedules of genuine first circuit visits from bounded observation windows -/

open Set Metric Filter Topology Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
open PrecisionReturns
noncomputable section

/-- A first visit from outside lies on the boundary of the exact distance
level, including when the target is touched only at that single time. -/
theorem firstVisit_mem_level_frontier {N : ℕ} (H : selfAdjoint (Square (Bits N))) (s : ℕ) (a : ℝ)
    {ε : ℝ} (hε : 0<ε) (hout : ε<orbitCircuitDistance H s a) :
    firstVisit H a s ε ∈ frontier {t | orbitCircuitDistance H s t=ε} := by
  let v := firstVisit H a s ε
  obtain ⟨hav,hv,hfar⟩ := firstVisit_left_contact H s a hε hout
  refine ⟨subset_closure hv,?_⟩
  intro hi
  have hlevel : ∀ᶠ t in 𝓝[<] v, orbitCircuitDistance H s t=ε :=
    nhdsWithin_le_nhds (mem_interior_iff_mem_nhds.mp hi)
  have hright : ∀ᶠ t in 𝓝[<] v, a<t := nhdsWithin_le_nhds (lt_mem_nhds hav)
  have hleft : ∀ᶠ t in 𝓝[<] v, t<v := self_mem_nhdsWithin
  obtain ⟨t,he,ht⟩ := (hlevel.and (hright.and hleft)).exists
  exact (hfar t ht).ne' he

/-- At any positive fixed error, all first returns selected by outside
origins in a compact window and budgets at most P take only finitely
many distinct dates. The dates may lie beyond the observation window. -/
theorem finite_firstVisit_schedule {N : ℕ} (H : selfAdjoint (Square (Bits N))) (P : ℕ)
    {ε : ℝ} (hε : 0<ε) (a b : ℝ) :
    {v | ∃ s≤P, ∃ t∈Icc a b, ε<orbitCircuitDistance H s t ∧ firstVisit H t s ε=v}.Finite := by
  let K (s : ℕ) := Icc a (firstVisit H b s ε) ∩ frontier {t | orbitCircuitDistance H s t=ε}
  have hf (s : ℕ) : (K s).Finite := finite_level_frontier H s hε _ _
  apply ((Finset.range (P+1)).finite_toSet.biUnion (fun s _ => hf s)).subset
  rintro v ⟨s,hs,t,ht,hout,rfl⟩
  have hlt := firstVisit_isLeast H t s hε
  have hlb := firstVisit_isLeast H b s hε
  exact mem_iUnion.mpr ⟨s,mem_iUnion.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hs),
    ⟨ht.1.trans hlt.1.1,hlt.2 ⟨ht.2.trans hlb.1.1,hlb.1.2⟩⟩,firstVisit_mem_level_frontier H s t hε hout⟩⟩

#print axioms finite_firstVisit_schedule
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
