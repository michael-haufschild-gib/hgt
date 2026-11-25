import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnLevels.PathIncrement
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # Strict ordering of actual first returns for a fixed local path -/
open MeasureTheory Set Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnLevels
noncomputable section
open PrecisionReturns

/-- Strict clearance at the selected first entry advances the larger tube's first visit. -/
theorem earlier_visit_at_contact {N : ℕ} (H : selfAdjoint (Register N)) (A : ℝ) (s j : ℕ)
    {ε : ℝ} (hε : 0 < ε) (hfar : ε < orbitCircuitDistance H s A)
    (hnear : orbitCircuitDistance H j (firstVisit H A s ε) < ε) :
    firstVisit H A j ε < firstVisit H A s ε := by
  let v := firstVisit H A s ε
  have hs := firstVisit_isLeast H A s hε
  have hd : orbitCircuitDistance H s v ≤ ε := (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp hs.1.2
  have hav : A < v := hs.1.1.lt_of_ne fun he =>
    hfar.not_ge ((congrArg (orbitCircuitDistance H s) he).le.trans hd)
  have hh : ∀ᶠ t : ℝ in 𝓝[<] v, orbitCircuitDistance H j t < ε :=
    ((orbitCircuitDistance_lipschitz H j).continuous.continuousAt.eventually_lt continuousAt_const
      hnear).filter_mono nhdsWithin_le_nhds
  have ha : ∀ᶠ t : ℝ in 𝓝[<] v, A < t := (lt_mem_nhds hav).filter_mono nhdsWithin_le_nhds
  obtain ⟨t,ht,hat,htv⟩ := (hh.and (ha.and self_mem_nhdsWithin)).exists
  exact ((firstVisit_isLeast H A j hε).2 ⟨hat.le,
    (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mpr ht.le⟩).trans_lt htv

/-- Strict interior inclusion at every affordable time advances every first visit from outside. -/
theorem earlier_visit {N : ℕ} (H : selfAdjoint (Register N)) (A : ℝ) (s j : ℕ)
    {ε : ℝ} (hε : 0 < ε) (hfar : ε < orbitCircuitDistance H s A)
    (hnear : ∀ v, orbitCircuitDistance H s v ≤ ε → orbitCircuitDistance H j v < ε) :
    firstVisit H A j ε < firstVisit H A s ε :=
  earlier_visit_at_contact H A s j hε hfar (hnear _ ((hasProjectiveCircuitApproximation_iff_infDist ..).mp
    (firstVisit_isLeast H A s hε).1.2))

/-- At every positive tolerance outside the shared levels, one extra
local sweep strictly advances every attained first return from outside
the smaller tube. The origin and budget can be selected after the path. -/
theorem first_visit_strict {n : ℕ} (x : PathShell n) {ε : ℝ} (hε : 0 < ε) (hx : ε ∉ sharedLevels x) :
    let H : selfAdjoint (Register (n+2)) := ⟨pathHamiltonian x,isSelfAdjoint_pathHamiltonian x⟩
    ∀ s : ℕ, ∀ A : ℝ, ε < orbitCircuitDistance H s A →
      firstVisit H A (s+Fintype.card (PathLabel n)) ε < firstVisit H A s ε := by
  intro H s A hfar
  apply earlier_visit H A s _ hε hfar
  intro v hv
  have hle : orbitCircuitDistance H (s+Fintype.card (PathLabel n)) v ≤ orbitCircuitDistance H s v := by
    simpa only [sub_self,abs_zero,zero_pow (by decide : 2≠0),mul_zero,add_zero] using path_increment x s v v
  apply (hle.trans hv).lt_of_ne
  intro he
  have hsmall := le_antisymm hv (he.ge.trans hle)
  exact hx (mem_iUnion.mpr ⟨s,v,hsmall.trans he.symm,hsmall⟩)

/-- One exceptional set of dimension at most one half works on every
prefix of any fixed chain, including at origins selected from its orbit. -/
theorem chain_first_visit_levels (x : (n : ℕ) → PathShell n) :
    ∃ B : Set ℝ, dimH B ≤ 1/2 ∧ ∀ ε > (0:ℝ), ε ∉ B →
      ∀ n s : ℕ, ∀ A : ℝ,
        let H : selfAdjoint (Register (n+2)) := ⟨pathHamiltonian (x n),isSelfAdjoint_pathHamiltonian _⟩
        ε < orbitCircuitDistance H s A →
          firstVisit H A (s+Fintype.card (PathLabel n)) ε < firstVisit H A s ε := by
  refine ⟨⋃ n, sharedLevels (x n),?_,?_⟩
  · rw [dimH_iUnion]
    exact iSup_le fun n => sharedLevels_dimension (x n)
  · intro ε hε hB n
    exact first_visit_strict (x n) hε (fun h => hB (mem_iUnion.mpr ⟨n,h⟩))

#print axioms chain_first_visit_levels
end
end GaloisForLFunctions.HTGeometry.ReturnLevels
