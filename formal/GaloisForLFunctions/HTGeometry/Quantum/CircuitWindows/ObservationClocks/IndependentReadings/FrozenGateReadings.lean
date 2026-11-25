import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ObservationClocks.IndependentReadings.Patterns
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.GaussianOccupation

/-! # Geometric first affordable reading of one frozen Gaussian register -/

open Set Filter MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ObservationClocks.IndependentReadings
open SharpOccupation
noncomputable section

/-- On one draw and outside one countable set of clock parameters, the
first affordable reading has geometric survival probabilities on all
prefixes. Its parameter is the ordinary affordable fraction of the same
orbit. Budgets, errors, starting dates and observation windows may depend
on the draw. -/
theorem gaussian_geometric_first_reading :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∃ B : Set ℝ, B.Countable ∧ ∀ z∉B, ∀ k s : ℕ, ∀ ε : ℝ,
      let H : selfAdjoint (Register (k+3)) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      ∃ p : ℝ, (∀ a : ℝ→ℝ, Tendsto (fun T => visitFraction H s ε (a T) (a T+T)) atTop (𝓝 p)) ∧
        ∀ (n : ℕ) (o : Fin n→ℝ) (a : ℝ→ℝ),
          let misses := {t : ℝ | ∀ j : Fin n, o j+rate z j.val*t∉visitSet H s ε}
          Tendsto (fun T => volume.real (misses∩Icc (a T) (a T+T))/T) atTop (𝓝 ((1-p)^n)) := by
  classical
  filter_upwards [gaussian_path_all_prefixes_maximally_projective,PhaseBoundary.gaussian_uniform_affordable_fraction] with ω hs ho
  let H (k : ℕ) : selfAdjoint (Register (k+3)) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
  let e (k : ℕ) := (qubitConfigFin (k+3)).trans (prefixPhaseEnergyEquiv k)
  let E (k : ℕ) := (H k).2.isHermitian.eigenvalues ∘ (e k).symm
  let f (k : ℕ) := RHTower.zeroProjectiveFrequency (E k)
  have hmax (k : ℕ) : MaximallyProjectiveEnergy (E k) := (hs k).comp_equiv (e k).symm
  have hfreq (k : ℕ) : RationallyIndependentFrequency (f k) :=
    RHTower.maximallyProjectiveEnergy_zeroProjectiveFrequency_independent (E k) (hmax k)
  choose B hB hfree using fun k => countable_clock_resonances (f k) (hfreq k)
  refine ⟨⋃ k, B k,countable_iUnion hB,?_⟩
  intro z hz k s ε _
  let A := projectiveContinuousCircuitCaptureTarget (e k) (hermitianEigenbasisUnitary (H k).2.isHermitian) s ε
  have hA : IsClosed A := isClosed_projectiveContinuousCircuitCaptureTarget ..
  have hb : volume (frontier A)=0 := PhaseBoundary.spectral_target_null (e k) _ (E k) (hmax k) s ε
  have ht (t : ℝ) : finiteClockPhasePoint (f k) t∈A ↔ t∈visitSet (H k) s ε :=
    (physical_circuit_approximation_iff_spectral_capture (e k) (H k) s ε t).symm
  refine ⟨volume.real A,ho k s ε,?_⟩
  intro n o a misses
  have h := joint_pattern_fraction (f k) z (hfree k z (fun he => hz (mem_iUnion.mpr ⟨k,he⟩)) n)
    o (fun _ => Aᶜ) (fun _ => hA.measurableSet.compl) (fun _ => by rwa [frontier_compl]) a
  have hmass : volume.real Aᶜ=1-volume.real A := by rw [measureReal_compl hA.measurableSet,probReal_univ]
  simpa only [mem_compl_iff,ht,misses,hmass,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using h

#print axioms gaussian_geometric_first_reading
end
end GaloisForLFunctions.HTGeometry.ObservationClocks.IndependentReadings
