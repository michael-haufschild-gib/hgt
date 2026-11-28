import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.Curvature.BondClearance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.CrossingDeadline

/-! # Tied first returns require winding minima at the prescribed physical error -/

open Filter MeasureTheory Matrix Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
open PhaseBoundary.FiniteCertificates.BudgetComparisons PrecisionReturns SharpOccupation SpectralFilling.ReplicaOrders
noncomputable section

/-- Simultaneously at every subcritical budget on the frozen chain, either
one more bond sweep strictly advances the original first return at 1/10, or
every implementing winding at that return has minimum error exactly 1/10.
The minimum is over all clock dates and global phases in the same chart. -/
theorem gaussian_first_winding_minimum :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let h := pathPauliDisorderShell ω (k+1)
      let H := generator h
      let V := H.2.isHermitian.eigenvectorUnitary
      let A (i : Fin K → Bool) := -H.2.isHermitian.eigenvalues i/(2*π)
      let x := physicalArc (1/10)
      let P := nearHilbertContinuousCircuitBudget K
      let σ := Iterated.crossing H P 0
      ∀ s ≤ P, let v := firstVisit H σ s (1/10)
        let dates (C : TwoQubitCircuit K) (m : (Fin K → Bool) → ℤ) (η : ℝ) :=
          let W := V⁻¹*C.eval*V
          wordDates W A (circuitTurns W) m x η
        (∃ C : TwoQubitCircuit K, C.gateCount ≤ s ∧ ∃ m, v∈dates C m (1/10)) ∧
          (firstVisit H σ (s+(k+2)) (1/10)<v ∨
            ∀ (C : TwoQubitCircuit K) m, C.gateCount ≤ s → v∈dates C m (1/10) →
              ∀ η∈Ico (0:ℝ) (1/10), dates C m η=∅) := by
  obtain ⟨_,_,hcross⟩ := gaussian_replica_crossing_deadline
  filter_upwards [hcross] with ω hw
  filter_upwards [hw] with k hk
  intro K h H V A x P σ s hs v dates
  have he : (1/10:ℝ)∈Ioo 0 (sqrt 2) := ⟨by norm_num,(by norm_num : (1/10:ℝ)<1).trans_le
    (one_le_sqrt.mpr (by norm_num))⟩
  have hc := (hk 0).1.1
  change 0≤σ ∧ 9/80≤orbitCircuitDistance H P σ at hc
  have hfar : 1/10<orbitCircuitDistance H s σ := by
    by_contra! ha
    obtain ⟨z,hz,C,hC,hfit⟩ := (hasProjectiveCircuitApproximation_iff_infDist ..).mpr ha
    have hh : orbitCircuitDistance H P σ≤1/10 :=
      (hasProjectiveCircuitApproximation_iff_infDist ..).mp ⟨z,hz,C,hC.trans hs,hfit⟩
    linarith only [hc.2,hh]
  constructor
  · obtain ⟨_,z,hz,C,hC,hfit⟩ := (firstVisit_isLeast H σ s he.1).1
    have hh : v∈laboratoryDates H C.eval (1/10) := ⟨z,hz,hfit⟩
    rw [laboratoryDates_eq] at hh
    exact ⟨C,hC,(date_iff_lift _ _ he).mp hh⟩
  · by_cases hstrict : firstVisit H σ (s+(k+2)) (1/10)<v
    · exact Or.inl hstrict
    right
    intro C m hC hv η hη
    apply eq_empty_iff_forall_notMem.mpr
    intro u hu
    exact hstrict (earlier_first_visit_of_winding h σ s C hC m
      (physicalArc_spec he.1 he.2).1.2.le (by norm_num) hη.1 hη.2 hfar hv hu)

#print axioms gaussian_first_winding_minimum
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
