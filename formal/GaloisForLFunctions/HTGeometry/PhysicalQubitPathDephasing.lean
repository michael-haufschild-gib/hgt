/-
# Angular dephasing on the recursive physical qubit path

The two data the dephasing capstone consumes -- a coefficient vector with simple spectrum and two
Hamiltonians whose squared labelled action ratios are disjoint -- are both available on every
member of the recursive physical qubit-path family, for every balanced nonzero spectral character.
Feeding them in gives the plateau law's angular dephasing with no hypotheses beyond those on the
character and the amplitude.

Main result:
* `tendsto_integral_exp_sortedSpectralAction_zero_physicalQubitPath` — **angular dephasing on the
  card's ensemble**.
-/
import GaloisForLFunctions.HTGeometry.ConcreteTwoHamiltonianSpectralActionWitness
import GaloisForLFunctions.HTGeometry.SpectralActionDephasingCapstone

open Filter Topology MeasureTheory Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Angular dephasing on the recursive physical qubit path.**  For every member of the family,
every balanced nonzero spectral character and every bounded measurable amplitude, the oscillatory
shell integral of the canonically labelled spectral action tends to zero. -/
theorem tendsto_integral_exp_sortedSpectralAction_zero_physicalQubitPath (n : ℕ)
    (k : Fin (Fintype.card
      ((physicalEndpointCompleteQubitPath n).PhysicalState × Bool)) → ℝ)
    (hksum : ∑ i, k i = 0) (hkne : k ≠ 0)
    (g : Metric.sphere (0 : EuclideanSpace ℝ
      (Fin (physicalEndpointCompleteQubitPath n).leafLocalParameterCount)) 1 → ℂ)
    (hg : Measurable g) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖g x‖ ≤ C) :
    Filter.Tendsto (fun t : ℝ => ∫ x, g x *
        Complex.exp (-((t * sortedSpectralAction
            (physicalEndpointCompleteQubitPath n).leafLocalTraceGeneratorFin_isHermitian k
            (WithLp.ofLp (x : EuclideanSpace ℝ
              (Fin (physicalEndpointCompleteQubitPath n).leafLocalParameterCount))) : ℝ) : ℂ)
          * Complex.I)
        ∂(MeasureTheory.volume.toSphere))
      (Filter.cocompact ℝ) (nhds 0) := by
  obtain ⟨θ₁, θ₂, hdisj⟩ :=
    exists_physicalEndpointCompleteQubitPath_disjoint_actionRatio_pair n k hksum hkne
  exact tendsto_integral_exp_sortedSpectralAction_zero_of_disjoint
    (physicalEndpointCompleteQubitPath n).leafLocalTraceGeneratorFin_isHermitian
    (physicalEndpointCompleteQubitPath_leafLocal_spectralDiscriminantPoly_ne_zero n k hksum hkne)
    k hdisj g hg hC0 hC

end

end GaloisForLFunctions.HTGeometry
