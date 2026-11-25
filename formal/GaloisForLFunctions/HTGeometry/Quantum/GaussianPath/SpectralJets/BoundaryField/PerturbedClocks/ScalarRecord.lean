import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.PerturbedClocks.Occupation
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance

/-! # Loss of scalar coincidences on perturbing one field at fixed return dates -/

open Set Filter MeasureTheory Topology Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.PerturbedClocks
open NestedPrefixes SharpOccupation PrecisionReturns PrescribedTimes
noncomputable section

/-- The original register fits at every recorded dip. Almost all additive
changes of a single field leave only the scalar Haar fraction of those
same dates affordable, even inside arbitrarily small field intervals. -/
theorem gaussian_perturbed_scalar_record :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k P : ℕ,
      let x := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
      let t := returnClock (k+1) P 0 x
      (∀ i, t i∈SharpOccupation.visitSet (shiftedGenerator ω k 0) 0 (1/10)) ∧
      ∀ᵐ z : ℝ, ∀ ε∈Ioo (0:ℝ) (sqrt 2), Tendsto (fun M => (integerClockPrefixLaw t M : Measure ℝ).real
        (SharpOccupation.visitSet (shiftedGenerator ω k z) 0 ε)) atTop (𝓝 (zeroGateArcDensity (2^(k+3)) (physicalArc ε))) := by
  filter_upwards [gaussian_changed_field_clock] with ω hω k P
  intro x t
  have hgen : prefixGenerator (k+1) x=shiftedGenerator ω k 0 := by
    apply Subtype.ext
    change numberedGenerator (k+1) x=boundaryHamiltonian ω k 0
    rw [boundaryHamiltonian,Complex.ofReal_zero,zero_smul,add_zero]
    exact numberedGenerator_shell _
  constructor
  · intro i
    rw [←hgen]
    cases i with
    | zero => exact (firstVisit_isLeast _ _ _ (by norm_num : (0:ℝ)<1/10)).1.2
    | succ i => exact (firstVisit_isLeast _ _ _ (by norm_num : (0:ℝ)<1/10)).1.2
  · filter_upwards [hω k t (returnClock_separated _ _ _ x)] with z hz ε he
    let H := shiftedGenerator ω k z
    obtain ⟨hx,hε⟩ := physicalArc_spec he.1 he.2
    let r : Icc (0:ℝ) (1/2) := ⟨physicalArc ε,hx.1.le,hx.2.le⟩
    have hset : SharpOccupation.visitSet H 0 ε=zeroGateReturnSet H r := by
      ext u
      change HasProjectiveCircuitApproximation _ ε 0 _ ↔ orbitCircuitDistance H 0 u≤zeroGateArcTolerance (physicalArc ε)
      rw [hε]
      exact hasProjectiveCircuitApproximation_iff_infDist .. 
    obtain ⟨p,hp,ht⟩ := hz.2 0 ε
    have h := hp (fun _ => 0)
    simp only [visitFraction,hset,zero_add] at h
    have hlim := maximallyProjective_zeroGateOccupation_from_start H hz.1 r 0
    have heq := tendsto_nhds_unique h hlim
    rwa [←heq]

#print axioms gaussian_perturbed_scalar_record
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.PerturbedClocks
