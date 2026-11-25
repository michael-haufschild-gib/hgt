import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.BudgetComparisons.BondTies
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnLevels.FirstVisits

/-! # Finitely many exceptional return tolerances above each positive error floor -/

open Set Filter Topology Metric
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.BudgetComparisons
open PrecisionReturns
noncomputable section

/-- On bounded origins and budgets, every error above a prescribed positive
floor selects a strictly earlier return with one extra bond sweep, except at
finitely many tolerances. The first returns may lie outside the origin window. -/
theorem finite_first_visit_order_exceptions {n : ℕ} (x : PathShell n) (P : ℕ) (a b : ℝ)
    {e₀ : ℝ} (h₀ : 0<e₀) : ∃ F : Set ℝ, F.Finite ∧ ∀ e≥e₀, e∉F →
      ∀ s≤P, ∀ t∈Icc a b, let H := generator x
        e<orbitCircuitDistance H s t → firstVisit H t (s+(n+1)) e < firstVisit H t s e := by
  let H := generator x
  let u := firstVisit H b 0 e₀
  let F := ⋃ s∈(Finset.range (P+1) : Set ℕ), tiedLevels x s a u
  refine ⟨F,(Finset.range (P+1)).finite_toSet.biUnion (fun s _ => finite_bond_ties x s a u),?_⟩
  intro e he hmiss s hs t ht _ hfar
  let v := firstVisit H t s e
  have he' := h₀.trans_le he
  have hl := firstVisit_isLeast H t s he'
  have hu := firstVisit_isLeast H b 0 h₀
  have hvbox : v∈Icc a u := by
    obtain ⟨z,hz,C,hC,hfit⟩ := hu.1.2
    exact ⟨ht.1.trans hl.1.1,hl.2 ⟨ht.2.trans hu.1.1,z,hz,C,hC.trans (Nat.zero_le _),hfit.trans he⟩⟩
  have hd : orbitCircuitDistance H s v≤e := (hasProjectiveCircuitApproximation_iff_infDist ..).mp hl.1.2
  apply ReturnLevels.earlier_visit_at_contact H t s _ he' hfar
  exact bond_clearance x s hvbox (fun h => hmiss (mem_iUnion.mpr ⟨s,mem_iUnion.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hs),h⟩⟩)) hd

/-- Even a prescribed exceptional tolerance is isolated from all other
possible order failures for these origins, including at one tenth. -/
theorem strict_first_visits_around {n : ℕ} (x : PathShell n) (P : ℕ) (a b : ℝ)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ e in 𝓝[≠] ε, ∀ s≤P, ∀ t∈Icc a b, let H := generator x
      e<orbitCircuitDistance H s t → firstVisit H t (s+(n+1)) e < firstVisit H t s e := by
  obtain ⟨F,hF,h⟩ := finite_first_visit_order_exceptions x P a b (half_pos hε)
  have hnear : (F \ {ε})ᶜ∈𝓝 ε := (hF.diff (t:={ε})).isClosed.isOpen_compl.mem_nhds
    (fun he => he.2 (mem_singleton _))
  have hlo : ∀ᶠ e in 𝓝[≠] ε, ε/2<e := nhdsWithin_le_nhds (lt_mem_nhds (half_lt_self hε))
  filter_upwards [nhdsWithin_le_nhds hnear,hlo,self_mem_nhdsWithin] with e he he' hne
  exact h e he'.le (fun hF => he ⟨hF,hne⟩)

#print axioms strict_first_visits_around
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.BudgetComparisons
