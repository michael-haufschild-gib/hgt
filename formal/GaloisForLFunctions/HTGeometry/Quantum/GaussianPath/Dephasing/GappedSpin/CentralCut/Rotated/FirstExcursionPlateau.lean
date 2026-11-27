import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Rotated.PhysicalSector
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.IncrementClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.OccupationBand

/-! # A long first excursion and occupation near the same trajectory's maximum -/

open Set Filter Real MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open PrescribedTimes AccuracyScales.TenthPlateau WeakBonds.NearDiagonal SharpOccupation
noncomputable section

/-- On a measurable sector of mass at least exp(−CK²)/T⁷, almost
every path has a delayed first crossing and first waits, and spends
all but an exponentially small-in-dimension long-time fraction
above its own same-error maximum divided by O(K²). -/
theorem long_first_excursion_and_maximum_occupation :
    ∃ C > (0:ℝ), ∃ b ∈ Ioo (0:ℝ) 1, ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let K := n+2
      let P := nearHilbertContinuousCircuitBudget K
      ∀ T ≥ (1:ℝ), ∃ E : Set PathPauliDisorder, MeasurableSet E ∧
        exp (-C*(K:ℝ)^2) ≤ T^7*pathPauliDisorderLaw.real E ∧
        ∀ᵐ ω ∂pathPauliDisorderLaw, ω∈E →
          let u := pathPauliDisorderShell ω n
          let x := fun i => u (pathCoeffEquiv n i)
          let H : selfAdjoint (DiagonalSynthesis.Register K) :=
            ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
          x ∈ allCoordStrongEvent n (1/100) ∧ T < crossingOrigin n P (9/80) x ∧
          (∀ s ≤ P/2, T < crossingWait n P s x) ∧
          ∃ m : ℕ, P < m ∧ m ≤ (2*K+1)*2^K ∧ IsRecurrentOrbitCircuitMaximumAt H (1/10) m ∧
            ∀ a : ℝ, ∀ᶠ U : ℝ in atTop, ∀ s : ℕ, s*(64*(K+1))*(2*K+1) ≤ m →
              visitFraction H s (1/10) a U < b^(2^K:ℕ) := by
  obtain ⟨C,hC,hbox⟩ := physical_joint_sector
  obtain ⟨b,hb,hband⟩ := capped_path_occupation
  refine ⟨C,hC,b,hb,?_⟩
  filter_upwards [hbox,hband,delay_of_cheap] with k hk hcost hdelay
  intro n K P T hT
  obtain ⟨B,E,hB,hE,hprob,hprop⟩ := hk T hT
  refine ⟨E,hE,hprob,?_⟩
  filter_upwards [gaussian_path_all_prefixes_maximally_projective,hdelay] with ω hω hd
  intro he u x H
  obtain ⟨hstrong,hglobal,hinc⟩ := hprop ω he
  obtain ⟨ho,hr⟩ := hd T (zero_lt_one.trans_le hT) B hB hinc
  exact ⟨hstrong,ho,hr,hcost u (hω k) (2*K+1) (by omega) hglobal⟩

#print axioms long_first_excursion_and_maximum_occupation
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
