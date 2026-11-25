import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EntrySensitivity.PrescribedCharacters.GateLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EntrySensitivity.PrescribedCharacters.VisitIndices.Counting
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance

/-! # Mean gate-return spacing on the first scalar return clock -/

open Set Filter Topology MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EntrySensitivity.PrescribedCharacters.VisitIndices
open AdaptiveSampling SharpOccupation
noncomputable section

/-- On the lattice with step the actual first scalar return date at one
tenth, enumerate all ticks affordable at the observation error. For any
subcritical gate budget their mean separation in ticks has the inverse
Haar occupation exponent, from every translated origin. -/
theorem gaussian_selected_clock_return_spacing :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s : ℕ → ℕ, subcriticalBudget s →
      ∀ ε ∈ Ioo (0:ℝ) (Real.sqrt 2), ∀ l b : ℝ, 0<l → l<physicalArc ε → physicalArc ε<b →
      ∀ᶠ k : ℕ in atTop, let N := k+3; let D := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
          isSelfAdjoint_pathHamiltonian _⟩
        let P := nearHilbertContinuousCircuitBudget N
        ∃ σ > (0:ℝ), orbitCircuitDistance H P σ=9/80 ∧
          (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
          let v := PrecisionReturns.firstVisit H σ 0 (1/10)
          ∀ j ≤ s N, ∃ p ∈ Icc (l^D) (b^D), ∀ a : ℝ,
            let hit (n : ℕ) := a+(n:ℝ)*v ∈ visitSet H j ε
            (setOf hit).Infinite ∧ Tendsto (fun i : ℕ => (Nat.nth hit i:ℝ)/i) atTop (𝓝 p⁻¹) := by
  filter_upwards [gaussian_first_scalar_clock_gate_law,PhaseBoundary.gaussian_uniform_affordable_fraction,
    gaussian_physical_return_rates] with ω hgate hcont hrate s hs ε he l b hl hlx hxb
  filter_upwards [hgate,hrate s hs ε he l b hl hlx hxb] with k hk hr
  intro N D H P
  obtain ⟨σ,hσ,hc,hb,hclock⟩ := hk
  refine ⟨σ,hσ,hc,hb,?_⟩
  intro v j hj
  let e := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let p := volume.real (projectiveContinuousCircuitCaptureTarget e V j ε)
  have hlim : Tendsto (fun T => visitFraction H j ε 0 T) atTop (𝓝 p) := by
    simpa only [zero_add] using hcont k j ε (fun _ => 0)
  have hh := (hr j hj 0).1
  have hlow : l^D ≤ p := le_of_tendsto_of_tendsto tendsto_const_nhds hlim (hh.mono fun _ h => h.1.le)
  have hupp : p ≤ b^D := le_of_tendsto_of_tendsto hlim tendsto_const_nhds (hh.mono fun _ h => h.2.le)
  refine ⟨p,⟨hlow,hupp⟩,?_⟩
  intro a
  have hA : IsClosed (visitSet H j ε) := by
    rw [show visitSet H j ε = {t | orbitCircuitDistance H j t ≤ ε} from
      Set.ext fun _ => hasProjectiveCircuitApproximation_iff_infDist _ _ _]
    exact isClosed_le (orbitCircuitDistance_lipschitz H j).continuous continuous_const
  exact return_index_spacing (fun n : ℕ => a+(n:ℝ)*v) _ hA.measurableSet
    ((pow_pos hl D).trans_le hlow) (hclock a j ε)

#print axioms gaussian_selected_clock_return_spacing
end
end GaloisForLFunctions.HTGeometry.EntrySensitivity.PrescribedCharacters.VisitIndices
