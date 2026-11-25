import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.PrefixDeadlines.HalfArc
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.GaussianOccupation

/-! # A first-return deadline from the affordable time observed before its origin -/

open Set MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines
open SharpOccupation PhaseBoundary
open PrecisionReturns (firstVisit firstVisit_isLeast)
noncomputable section

/-- Every identity-start record has at least the limiting mass with half
the circuit resources. Applied at the first return, this bounds its date
using only affordable time observed before the origin, even for the first
near-Hilbert crossing and a budget chosen after seeing the chain. -/
theorem gaussian_observed_prefix_deadline :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let i := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
      let V := hermitianEigenbasisUnitary H.2.isHermitian
      ∀ (j s : ℕ) (e : ℝ), j + j ≤ s → e ∈ Ioo (0 : ℝ) 2 →
        let d := zeroGateArcTolerance (physicalArc e/2)
        let p := volume.real (projectiveContinuousCircuitCaptureTarget i V j d)
        ∀ a≥(0:ℝ), p*firstVisit H a s e≤volume.real (visitSet H s e∩Icc 0 a) := by
  filter_upwards [gaussian_uniform_affordable_fraction] with ω hω
  intro k N H i V j s e hj he d p a ha
  have h := hω k j d (fun _ => 0)
  simp only [visitFraction,zero_add,sub_zero] at h
  have hv := firstVisit_isLeast H a s he.1
  obtain ⟨hx,hx'⟩ := FiniteRecords.physicalArc_full he
  have diff (t : ℝ) (ht : t∈visitSet H j d) (u : ℝ) (hu : u∈visitSet H j d) :
      t-u∈visitSet H s e := by
    obtain ⟨c,hc,C,hC,hfit⟩ := half_arc_differences H j (Ioo_subset_Icc_self hx) t ht u hu
    exact ⟨c,hc,C,hC.trans hj,hfit.trans_eq hx'⟩
  have hprefix := density_le_prefix _ _ (closed_visits H j d) (closed_visits H s e).measurableSet
    diff h _ (ha.trans hv.1.1)
  rwa [first_visit_mass H s he.1] at hprefix

#print axioms gaussian_observed_prefix_deadline
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines
