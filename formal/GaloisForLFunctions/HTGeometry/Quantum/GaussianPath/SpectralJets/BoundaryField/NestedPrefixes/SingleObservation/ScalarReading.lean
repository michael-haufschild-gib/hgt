import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.SingleObservation.OriginalLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.FieldWindows.EmptyReturns
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance

/-! # Physical scalar probability at one late date selected by the other couplings -/

open Set Filter Topology MeasureTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes.SingleObservation
open SharpOccupation
noncomputable section

abbrev originalGenerator (k : ℕ) (ω : PathPauliDisorder) : selfAdjoint (Register (k+3)) :=
  ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩

/-- At a single diverging date chosen without the terminal field, the
original larger register fits the empty circuit with its exact Haar probability. -/
theorem scalar_reading (k : ℕ) (t : ℕ → PathPauliDisorder → ℝ) (ht : ∀ n, Measurable (t n))
    (hdiv : ∀ᵐ ω ∂pathPauliDisorderLaw, Tendsto (fun n => t n (eraseTerminal k ω)) atTop atTop)
    {ε : ℝ} (he : ε∈Ioo (0:ℝ) (sqrt 2)) :
    Tendsto (fun n => pathPauliDisorderLaw.real {ω | orbitCircuitDistance (originalGenerator k ω) 0
      (t n (eraseTerminal k ω))≤ε}) atTop (𝓝 (zeroGateArcDensity (2^(k+3)) (physicalArc ε))) := by
  let r : Config k := fun _ => false
  obtain ⟨hx,hε⟩ := physicalArc_spec he.1 he.2
  let x : Icc (0:ℝ) (1/2) := ⟨physicalArc ε,hx.1.le,hx.2.le⟩
  let w : Icc (0:ℝ) 1 := ⟨x,x.property.1,x.property.2.trans (by norm_num)⟩
  let A := relativeEnclosingUnitArc r (w:ℝ)
  have h := original_snapshot_probability k r t ht hdiv A (isClosed_relativeEnclosingUnitArc r _).measurableSet
    (volume_frontier_relativeEnclosingUnitArc r w)
  have hh := (ENNReal.tendsto_toReal (measure_ne_top volume A)).comp h
  have hmass : volume.real A=zeroGateArcDensity (2^(k+3)) (physicalArc ε) := by
    simpa only [A,r,w,x,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] using relativeUnitArcMass_eq_power r x
  change Tendsto _ _ (𝓝 (volume.real A)) at hh
  rw [hmass] at hh
  apply hh.congr
  intro n
  change pathPauliDisorderLaw.real _=_
  congr 1
  ext ω
  let H := originalGenerator k ω
  let E := H.2.isHermitian.eigenvalues
  let u := t n (eraseTerminal k ω)
  obtain ⟨b,heq⟩ := ordered_at_zero k ω
  change originalPhase k r ω u∈A ↔ orbitCircuitDistance H 0 u≤ε
  have hp : originalPhase k r ω u∈A ↔ u∈zeroGateReturnSet H w := by
    rw [zeroGateReturnSet_eq_preimage_full H (b r) w]
    unfold originalPhase
    rw [heq]
    exact FieldWindows.arc_perm (fun i => -E i) b r u w
  rw [hp]
  change orbitCircuitDistance H 0 u≤zeroGateArcTolerance (physicalArc ε) ↔ _
  rw [hε]

#print axioms scalar_reading
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes.SingleObservation
