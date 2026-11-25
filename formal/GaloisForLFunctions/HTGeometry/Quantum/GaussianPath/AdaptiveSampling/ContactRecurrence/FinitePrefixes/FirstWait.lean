import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactRecurrence.FinitePrefixes.PhysicalDeadlines
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactRecurrence.PhysicalClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactRecurrence.LatticeFraction
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ResonantOccupation.OccupationLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.PrefixPhaseHorizon

/-! # Double exponential mean spacings on clocks through first positive-budget dips -/

open Set Filter MeasureTheory Topology Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.FinitePrefixes
open ResonantOccupation PrecisionReturns EntrySensitivity.PrescribedCharacters.VisitIndices
noncomputable section

/-- Start the clock at the robust crossing and set its first tick to
the actual first s-gate dip. After an error allowance of 2π/Q the
ith hit is present by 1+i Q^(D−1) on every finite prefix of ticks.
Its limiting affordable fraction lies between Q^(-(D−1)) and 16^(-D). -/
theorem gaussian_first_wait_index_bracket :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, let N := k+3
      let D := 2^N
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ > (0:ℝ), orbitCircuitDistance H P σ=9/80 ∧
        (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
        ∀ ε∈Ioc (0:ℝ) (1/10), ∀ s≤P,
          let Δ := firstVisit H σ s ε-σ
          0<Δ ∧ ∀ (Q : ℕ), 2≤Q → ∀ η≤(1/8:ℝ), ε+2*π/Q≤η → ∀ b∈Icc s P,
            let A := SharpOccupation.visitSet H b η
            let hit (j : ℕ) := σ+(j:ℝ)*Δ∈A
            (setOf hit).Infinite ∧ (∀ i, Nat.nth hit i≤1+Q^(D-1)*i) ∧
              ∃ p∈Icc (1/((Q^(D-1):ℕ):ℝ)) (1/((16^D:ℕ):ℝ)),
                Tendsto (fun n => (timeLaw σ Δ n).real A) atTop (𝓝 p) ∧
                Tendsto (fun i : ℕ => (Nat.nth hit i:ℝ)/i) atTop (𝓝 p⁻¹) := by
  filter_upwards [gaussian_unshifted_first_excursion_tick_gaps,gaussian_lattice_eighth_upper] with ω hg hh
  filter_upwards [hg,hh] with k hk hfrac
  intro N D H P
  obtain ⟨σ,hσ,hc,hb,_⟩ := hk
  refine ⟨σ,hσ,hc,hb,?_⟩
  intro ε hε s hs Δ
  let v := firstVisit H σ s ε
  have hleast := firstVisit_isLeast H σ s hε.1
  have hstep : 0<Δ := by
    refine sub_pos.mpr (hleast.1.1.lt_of_ne ?_)
    intro he
    obtain ⟨z,hz,C,hC,herr⟩ := hleast.1.2
    have hcheap : orbitCircuitDistance H P v≤ε := (hasProjectiveCircuitApproximation_iff_infDist ..).mp
      ⟨z,hz,C,hC.trans hs,herr⟩
    change σ=v at he
    rw [←he,hc] at hcheap
    linarith only [hcheap,hε.2]
  refine ⟨hstep,?_⟩
  intro Q hQ η hη hslack b hbudget A hit
  let e := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
  let f (n : ℕ) := σ+(n:ℝ)*Δ
  have hfit : HasProjectiveCircuitApproximation N ε b (unitaryEvolution H.val (σ+(1:ℕ)*Δ)) := by
    rw [show σ+(1:ℕ)*Δ=v by dsimp [Δ,v]; ring]
    obtain ⟨z,hz,C,hC,herr⟩ := hleast.1.2
    exact ⟨z,hz,C,hC.trans hbudget.1,herr⟩
  obtain ⟨hi,hu⟩ := visit_index_deadline e H σ Δ 1 b hfit (by omega : 0<Q) hslack
  change ∀ i, Nat.nth hit i≤1+Q^(D-1)*i at hu
  obtain ⟨p,hp⟩ := physical_gate_frequency e H σ Δ b η
  have hm : MeasurableSet A := by
    rw [show A={t | orbitCircuitDistance H b t≤η} from Set.ext fun _ => hasProjectiveCircuitApproximation_iff_infDist ..]
    exact (isClosed_le (orbitCircuitDistance_lipschitz H b).continuous continuous_const).measurableSet
  have hD : 1<D := by dsimp [D,N]; exact one_lt_pow₀ (by decide) (by omega)
  have hbig : 1<Q^(D-1) := one_lt_pow₀ (by omega) (by omega)
  have hl : 1/((Q^(D-1):ℕ):ℝ)≤p := by
    apply frequency_lower_of_linear_indices f A hm hi (by omega : 0<Q^(D-1)) _ hp
    intro i
    exact (hu i).trans_lt (by rw [Nat.mul_succ]; omega)
  have hupper := le_of_tendsto hp ((hfrac σ Δ hstep.ne').mono fun M hh => (hh b hbudget.2 η hη).le)
  have hpos := (one_div_pos.mpr (Nat.cast_pos.mpr (Nat.zero_lt_one.trans hbig))).trans_le hl
  exact ⟨hi,hu,p,⟨hl,hupper⟩,hp,(return_index_spacing f A hm hpos hp).2⟩

#print axioms gaussian_first_wait_index_bracket
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.FinitePrefixes
