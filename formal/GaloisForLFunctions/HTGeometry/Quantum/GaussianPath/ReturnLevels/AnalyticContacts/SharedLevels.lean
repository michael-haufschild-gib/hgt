import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnLevels.AnalyticContacts.GraphCertificates
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnLevels.AnalyticContacts.TimeJets
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnLevels.FirstVisits

/-! # The errors shared by two physical budgets a sweep apart are countable -/

open Filter Set MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnLevels.AnalyticContacts
open LocalPatches (Register)
open PrecisionReturns
noncomputable section

/-- For every path, the union over all budgets and all real dates of
levels shared with one additional local sweep is countable. -/
theorem sharedLevels_countable {n : ℕ} (x : PathShell n) : (sharedLevels x).Countable := by
  classical
  let N := n+2
  let H : selfAdjoint (Register N) := ⟨pathHamiltonian x,isSelfAdjoint_pathHamiltonian _⟩
  let J := Fintype.card (PathLabel n)
  let K := 84*‖x‖^2
  let A := MvPolynomial (ErrorVars N) ℚ
  letI : Countable A := AddMonoidAlgebra.coeff_injective.countable
  let I := {P : A // ∃ z, certEval H z P≠0}
  unfold sharedLevels
  apply countable_iUnion
  intro s
  let f := orbitCircuitDistance H s
  let S := {t | f t=orbitCircuitDistance H (s+J) t}
  have hflat (t) (ht : t ∈ S) (u) (hu : u ∈ S) : |f u-f t| ≤ K*|u-t|^2 := by
    have h₁ := path_increment x s t u
    have h₂ := path_increment x s u t
    change orbitCircuitDistance H (s+J) t ≤ f u+K*|t-u|^2 at h₁
    change orbitCircuitDistance H (s+J) u ≤ f t+K*|u-t|^2 at h₂
    rw [←ht,abs_sub_comm t u] at h₁
    rw [←hu] at h₂
    exact abs_le.mpr ⟨by linarith only [h₁],by linarith only [h₂]⟩
  let Z (P : I) := f '' {t ∈ S | certEval H (t,f t) P.val=0}
  have hZ (P : I) : (Z P).Countable :=
    flat_heights_countable K hflat (fun z => certEval H z P.val) (cert_analytic H P.val) P.property
  apply ((countable_singleton (0:ℝ)).union (countable_iUnion hZ)).mono
  rintro _ ⟨t,ht,rfl⟩
  by_cases h : f t=0
  · exact Or.inl h
  · have hp : 0 < f t := lt_of_le_of_ne Metric.infDist_nonneg h.symm
    obtain ⟨P,hP,hn⟩ := distance_certificate H s t hp
    exact Or.inr (mem_iUnion.mpr ⟨⟨P,hn⟩,t,⟨ht,hP⟩,rfl⟩)

/-- Outside one countable set of errors for an entire deterministic chain,
one extra sweep strictly advances the first entrance at every budget on
every prefix, from every observation origin outside the smaller tube. -/
theorem countable_first_visit_levels (x : (n : ℕ) → PathShell n) :
    ∃ E : Set ℝ, E.Countable ∧ ∀ e > (0:ℝ), e ∉ E → ∀ n s : ℕ, ∀ a : ℝ,
      let H : selfAdjoint (Register (n+2)) := ⟨pathHamiltonian (x n),isSelfAdjoint_pathHamiltonian _⟩
      e < orbitCircuitDistance H s a →
        firstVisit H a (s+Fintype.card (PathLabel n)) e < firstVisit H a s e := by
  refine ⟨⋃ n, sharedLevels (x n),countable_iUnion (fun n => sharedLevels_countable (x n)),?_⟩
  intro e he hr n
  exact first_visit_strict (x n) he (fun hn => hr (mem_iUnion.mpr ⟨n,hn⟩))

#print axioms sharedLevels_countable
#print axioms countable_first_visit_levels
end
end GaloisForLFunctions.HTGeometry.ReturnLevels.AnalyticContacts
