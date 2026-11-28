import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.Curvature.FirstContact
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.Curvature.StrictDates

/-! # Isolated circuit windings at tied first returns on the frozen chain -/

open Filter MeasureTheory Matrix Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
open PhaseBoundary.FiniteCertificates.BudgetComparisons PrecisionReturns SharpOccupation
noncomputable section

/-- At physical tolerance one tenth, a tie with the budget one sweep higher
forces each implementing circuit to fit at exactly one date on its entering
winding. This holds for all budgets up to the original crossing budget. -/
theorem gaussian_singleton_entering_windings :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let H := generator (pathPauliDisorderShell ω (k+1))
      let V := H.2.isHermitian.eigenvectorUnitary
      let A (i : Fin K → Bool) := -H.2.isHermitian.eigenvalues i/(2*π)
      let P := nearHilbertContinuousCircuitBudget K
      let σ := Iterated.crossing H P 0
      ∀ s ≤ P, let v := firstVisit H σ s (1/10)
        let dates (C : TwoQubitCircuit K) (m : (Fin K → Bool) → ℤ) :=
          let W := V⁻¹*C.eval*V
          wordDates W A (circuitTurns W) m (physicalArc (1/10)) (1/10)
        (∃ C : TwoQubitCircuit K, C.gateCount ≤ s ∧ ∃ m, v∈dates C m) ∧
          (firstVisit H σ (s+(k+2)) (1/10)<v ∨
            ∀ (C : TwoQubitCircuit K) m, C.gateCount ≤ s → v∈dates C m → dates C m={v}) := by
  filter_upwards [gaussian_first_winding_minimum,gaussian_path_all_prefixes_maximally_projective] with ω hw hg
  filter_upwards [hw] with k hk
  intro K H V A P σ s hs v dates
  obtain ⟨hex,halt⟩ := hk s hs
  refine ⟨hex,halt.imp_right ?_⟩
  intro hmin C m hC hv
  ext u
  constructor
  · intro hu
    by_contra hne
    have he : (1/10:ℝ)∈Ioo 0 (sqrt 2) := ⟨by norm_num,(by norm_num : (1/10:ℝ)<1).trans_le
      (one_le_sqrt.mpr (by norm_num))⟩
    have hA : Function.Injective A := by
      intro i j hij
      apply (hg k).injective
      change -H.2.isHermitian.eigenvalues i/(2*π)= -H.2.isHermitian.eigenvalues j/(2*π) at hij
      exact neg_injective ((div_left_inj' two_pi_pos.ne').mp hij)
    obtain ⟨η,hη,hmid⟩ := strict_winding_midpoint (V⁻¹*C.eval*V) A hA m hne he hu hv
    rw [hmin C m hC hv η hη] at hmid
    exact hmid
  · rintro rfl
    exact hv

#print axioms gaussian_singleton_entering_windings
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
