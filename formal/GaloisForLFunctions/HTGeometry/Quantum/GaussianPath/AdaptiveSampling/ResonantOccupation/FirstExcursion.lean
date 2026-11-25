import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ResonantOccupation.OccupationLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactRecurrence.ReturnIndices

/-! # Limiting mean spacing on the unshifted first-excursion lattice -/

open Set Filter MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ResonantOccupation
open ContactRecurrence EntrySensitivity.PrescribedCharacters.VisitIndices PrecisionReturns
noncomputable section

/-- On the clock through the robust crossing whose first tick is the
actual scalar dip, all affordable fractions up to the crossing budget
converge to positive limits. The mean spacings in ticks converge and
are at least 16^(2^N) on every sufficiently long typical prefix. -/
theorem gaussian_unshifted_excursion_mean_spacing :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ > (0:ℝ), orbitCircuitDistance H P σ=9/80 ∧
        (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
        let Δ := firstVisit H σ 0 (1/10)-σ
        0<Δ ∧ ∀ s≤P,
          let A := SharpOccupation.visitSet H s (1/10)
          let hit (j : ℕ) := σ+(j:ℝ)*Δ∈A
          ∃ p > (0:ℝ), (16:ℝ)^(2^N:ℕ)≤p⁻¹ ∧
            Tendsto (fun n => (timeLaw σ Δ n).real A) atTop (𝓝 p) ∧
            Tendsto (fun i : ℕ => (Nat.nth hit i:ℝ)/i) atTop (𝓝 p⁻¹) := by
  filter_upwards [gaussian_unshifted_excursion_return_indices] with ω hw
  filter_upwards [hw] with k hk
  intro N H P
  obtain ⟨σ,hσ,hc,hb,hstep,B,hidx⟩ := hk
  refine ⟨σ,hσ,hc,hb,?_⟩
  intro Δ
  refine ⟨hstep,?_⟩
  intro s hs A hit
  let f (n : ℕ) := σ+(n:ℝ)*Δ
  let e := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
  obtain ⟨p,hp⟩ := physical_gate_frequency e H σ Δ s (1/10)
  have hA : MeasurableSet A := by
    rw [show A={t | orbitCircuitDistance H s t≤1/10} from Set.ext fun _ => hasProjectiveCircuitApproximation_iff_infDist ..]
    exact (isClosed_le (orbitCircuitDistance_lipschitz H s).continuous continuous_const).measurableSet
  obtain ⟨hi,hu,hl⟩ := hidx s hs
  have hpos := positive_frequency_of_index_gaps f A hA hi hu hp
  have hlim := (return_index_spacing f A hA hpos hp).2
  refine ⟨p,hpos,?_,hp,hlim⟩
  apply ge_of_tendsto hlim
  filter_upwards [hl,eventually_gt_atTop (0:ℕ)] with i hlow hip
  apply (le_div_iff₀ (Nat.cast_pos.mpr hip)).mpr
  have hnat := (Nat.mul_le_mul_left (16^(2^N)) (Nat.le_succ i)).trans hlow
  exact_mod_cast hnat

#print axioms gaussian_unshifted_excursion_mean_spacing
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ResonantOccupation
