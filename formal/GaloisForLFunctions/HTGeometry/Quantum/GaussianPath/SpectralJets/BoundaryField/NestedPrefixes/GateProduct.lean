import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.NumberedCharacters
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.PhaseRectangles
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.GaussianOccupation
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.SpectralTargets.NullBoundary

/-! # Joint distribution of physical gate costs on nested registers -/

open Filter MeasureTheory Set Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
open SharpOccupation
noncomputable section

/-- At one laboratory time the joint affordable fraction equals the product
of the separate affordable fractions, for every finite list of nested prefixes.
The gate budgets, errors and origins of long windows may all use the draw. -/
theorem gaussian_joint_gate_occupation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (n : ℕ) (s : Fin n → ℕ) (ε : Fin n → ℝ),
      let H (j : Fin n) : selfAdjoint (Register (j.val+3)) :=
        ⟨pathHamiltonian (pathPauliDisorderShell ω (j.val+1)),isSelfAdjoint_pathHamiltonian _⟩
      let B (j : Fin n) := visitSet (H j) (s j) (ε j)
      ∃ p : Fin n → ℝ, (∀ j (a : ℝ → ℝ), Tendsto (fun T => visitFraction (H j) (s j) (ε j)
        (a T) (a T+T)) atTop (𝓝 (p j))) ∧
        ∀ a : ℝ → ℝ, Tendsto (fun T => volume.real ((⋂ j, B j)∩Icc (a T) (a T+T))/T)
          atTop (𝓝 (∏ j, p j)) := by
  classical
  filter_upwards [gaussian_joint_numbered,gaussian_path_all_prefixes_maximally_projective,
    PhaseBoundary.gaussian_uniform_affordable_fraction] with ω hω hspec hpart
  intro n s ε H B
  let d (j : Fin n) := 2^(j.val+3)-1
  let e (j : Fin n) := (qubitConfigFin (j.val+3)).trans (prefixPhaseEnergyEquiv j.val)
  let E (j : Fin n) := (H j).2.isHermitian.eigenvalues ∘ (e j).symm
  let A (j : Fin n) := projectiveContinuousCircuitCaptureTarget (e j)
    (hermitianEigenbasisUnitary (H j).2.isHermitian) (s j) (ε j)
  let f (z : (j : Fin n) × Fin (d j)) := RHTower.zeroProjectiveFrequency (E z.1) z.2
  have hA (j : Fin n) : IsClosed (A j) := isClosed_projectiveContinuousCircuitCaptureTarget ..
  have hbA (j : Fin n) : volume (frontier (A j))=0 := PhaseBoundary.spectral_target_null
    (e j) _ (E j) ((hspec j.val).comp_equiv (e j).symm) (s j) (ε j)
  have htest (j : Fin n) (t : ℝ) :
      finiteClockPhasePoint (RHTower.zeroProjectiveFrequency (E j)) t∈A j ↔ t∈B j :=
    (physical_circuit_approximation_iff_spectral_capture (e j) (H j) (s j) (ε j) t).symm
  have hset : finiteClockPhasePoint f ⁻¹' rectangle A=⋂ j, B j := by
    ext t
    change (∀ j : Fin n, finiteClockPhasePoint (RHTower.zeroProjectiveFrequency (E j)) t∈A j) ↔ _
    simp only [htest,mem_iInter]
  refine ⟨fun j => volume.real (A j),fun j => hpart j.val (s j) (ε j),?_⟩
  intro a
  have h := PhaseBoundary.uniform_phase_fraction f (hω n d e) (rectangle A)
    (rectangle_closed A hA).measurableSet (rectangle_null_frontier A hA hbA) a
  simpa only [hset,rectangle_mass] using h

#print axioms gaussian_joint_gate_occupation
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
