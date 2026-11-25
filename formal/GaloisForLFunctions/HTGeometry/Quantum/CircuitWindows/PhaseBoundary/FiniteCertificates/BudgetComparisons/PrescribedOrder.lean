import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.BudgetComparisons.BondTies
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.CoarseVisits.Prescribed.FiniteHeightAtoms
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnLevels.FixedTolerance

/-! # Countably many exceptional prescribed errors for first-visit order -/

open Set Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.BudgetComparisons
open PrecisionReturns
noncomputable section

private def window (n s m : ℕ) (ω : PathPauliDisorder) :=
  tiedLevels (pathPauliDisorderShell ω n) s (-(m:ℝ)) m

private theorem measurable_tie (n s m : ℕ) (e : ℝ) :
    MeasurableSet {ω | e∈window n s m ω} := by
  let I := Icc (-(m:ℝ)) (m:ℝ)
  letI : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  let d (j : ℕ) (p : PathPauliDisorder × I) :=
    orbitCircuitDistance (generator (pathPauliDisorderShell p.1 n)) j p.2.val
  have hc (j : ℕ) : Continuous (d j) := (ReturnLevels.continuous_chain_distance n j).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  let F := {p : PathPauliDisorder × I | d s p=d (s+(n+1)) p ∧ d s p=e}
  have hF : IsClosed F := (isClosed_eq (hc _) (hc _)).inter (isClosed_eq (hc _) continuous_const)
  have he : {ω | e∈window n s m ω}=Prod.fst '' F := by
    ext ω
    exact ⟨fun ⟨t,⟨ht,h⟩,hv⟩ => ⟨(ω,⟨t,ht⟩),⟨h,hv⟩,rfl⟩,
      fun ⟨⟨_,t⟩,⟨h,hv⟩,rfl⟩ => ⟨t.val,⟨t.property,h⟩,hv⟩⟩
  rw [he]
  exact (isClosedMap_fst_of_compactSpace _ hF).measurableSet

/-- At every prescribed error outside a deterministic countable set, almost every
frozen chain has strict clearance with one additional bond sweep whenever an
affordable date occurs, on all prefixes, at all budgets and real dates. -/
theorem gaussian_strict_bond_clearance :
    ∃ E : Set ℝ, E.Countable ∧ ∀ e ∉ E, ∀ᵐ ω ∂pathPauliDisorderLaw,
      ∀ (n s : ℕ) (t : ℝ), let H := generator (pathPauliDisorderShell ω n)
        orbitCircuitDistance H s t≤e → orbitCircuitDistance H (s+(n+1)) t<e := by
  let μ := pathPauliDisorderLaw
  let A (n s m : ℕ) := {e : ℝ | 0<μ.real {ω | e∈window n s m ω}}
  have hc (n s m : ℕ) : (A n s m).Countable :=
    ExactContacts.CoarseVisits.Prescribed.countable_height_atoms μ _ (measurable_tie n s m)
      (Filter.Eventually.of_forall fun ω => finite_bond_ties (pathPauliDisorderShell ω n) s _ _)
  refine ⟨⋃ n s m, A n s m,countable_iUnion fun n => countable_iUnion fun s => countable_iUnion (hc n s),?_⟩
  intro e he
  have hmiss (n s m : ℕ) : ∀ᵐ ω ∂μ, e∉window n s m ω := by
    apply measure_eq_zero_iff_ae_notMem.mp
    apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
    exact le_antisymm (le_of_not_gt fun h =>
      he (mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨s,mem_iUnion.mpr ⟨m,h⟩⟩⟩)) measureReal_nonneg
  filter_upwards [ae_all_iff.mpr fun n => ae_all_iff.mpr fun s => ae_all_iff.mpr fun m => hmiss n s m]
    with ω hω
  intro n s t H hd
  obtain ⟨m,hm⟩ := exists_nat_gt |t|
  exact bond_clearance (pathPauliDisorderShell ω n) s (abs_le.mp hm.le) (hω n s m) hd

/-- Adding one sweep of N-1 bond gates strictly advances every actual
first return from outside at every positive error off one countable set. -/
theorem gaussian_first_visit_bond_order :
    ∃ E : Set ℝ, E.Countable ∧ ∀ e > (0:ℝ), e∉E → ∀ᵐ ω ∂pathPauliDisorderLaw,
      ∀ (n s : ℕ) (a : ℝ), let H := generator (pathPauliDisorderShell ω n)
        e<orbitCircuitDistance H s a → firstVisit H a (s+(n+1)) e < firstVisit H a s e := by
  obtain ⟨E,hE,h⟩ := gaussian_strict_bond_clearance
  refine ⟨E,hE,?_⟩
  intro e he hreg
  filter_upwards [h e hreg] with ω hω
  intro n s a H hfar
  exact ReturnLevels.earlier_visit H a s _ he hfar (hω n s)

#print axioms gaussian_first_visit_bond_order
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.BudgetComparisons
