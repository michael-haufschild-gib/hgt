import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactLevels.CrossingHeights.PhysicalPeriods
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactLevels.CrossingHeights.StableDip
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FirstCrossing
import Mathlib.Topology.Algebra.Module.Cardinality

/-! # Genuine crossing clocks approaching the canonical first excursion -/

open Set Filter MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactLevels.CrossingHeights
open SharpOccupation
noncomputable section

/-- One increasing deterministic sequence of heights tends to 9/80.
Almost surely on every sufficiently long prefix, its first crossings
approach the canonical date from below and eventually have exactly the
canonical first dip for every budget through P. Every resulting wait
is a nonresonant period of the same frozen spectrum. -/
theorem gaussian_approximating_first_crossings :
    ∃ r : ℕ → ℝ, StrictMono r ∧ (∀ i, r i∈Ioo (1/10:ℝ) (9/80)) ∧ Tendsto r atTop (𝓝 (9/80)) ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, let N := k+3
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
        let P := nearHilbertContinuousCircuitBudget N
        ∃ σ>0, orbitCircuitDistance H P σ=9/80 ∧ (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
          ∀ h>0, ∀ᶠ i : ℕ in atTop, ∃ u∈Ioo (σ-h) σ,
            orbitCircuitDistance H P u=r i ∧ (∀ t∈Ico 0 u, orbitCircuitDistance H P t<r i) ∧
            ∃ e : (Fin N → Bool) ≃ Fin ((2^N-1)+1), ∀ s≤P,
              PrecisionReturns.firstVisit H u s (1/10)=PrecisionReturns.firstVisit H σ s (1/10) ∧
              FreeAtStep (RHTower.zeroProjectiveFrequency (H.2.isHermitian.eigenvalues ∘ e.symm))
                (PrecisionReturns.firstVisit H σ s (1/10)-u) := by
  have he : (0:ℝ)<1/10 := by norm_num
  obtain ⟨B,hB,hf⟩ := gaussian_fixed_return_error_free_waits (1/10) he
  obtain ⟨r,hr,hrB,hlim⟩ := (hB.dense_compl ℝ).exists_seq_strictMono_tendsto_of_lt
    (by norm_num : (1/10:ℝ)<9/80)
  obtain ⟨c,hfinite⟩ := gaussian_finite_interval_occupation
  refine ⟨r,hr,fun i => (hrB i).1,hlim,?_⟩
  filter_upwards [ae_all_iff.mpr (fun i => hf (r i) (hrB i).2),hfinite] with ω hfree hfin
  filter_upwards [hfin] with k hocc
  intro N H P
  let D := 2^N
  have hP : P≤D/(16*(N+1)) := by
    apply Nat.div_le_div_left <;> dsimp [P,D,nearHilbertContinuousCircuitBudget,N] <;> omega
  have hD : D≠0 := by dsimp only [D]; positivity
  have hp := pow_lt_one₀ (by norm_num : (0:ℝ)≤3/8) (by norm_num) hD
  have level (η : ℝ) (hη : 0<η) (heighth : η≤1/8) :=
    dated_crossing_of_occupation H (j:=P) (η:=η) (ε:=1/8) (p:=(3/8:ℝ)^D) (G:=(2:ℝ)^(D^c))
      hη heighth (pow_nonneg (by norm_num : (0:ℝ)≤3/8) D) hp (by positivity)
      (fun T hT => by simpa only [zero_add] using hocc P hP 0 T hT)
  obtain ⟨σ,hσ,hc,hprior,_⟩ := level (9/80) (by norm_num) (by norm_num)
  refine ⟨σ,hσ,hc,hprior,?_⟩
  intro h hh
  obtain ⟨b,hb,hstable⟩ := stable_dip_below_crossing H P he (by norm_num : (1/10:ℝ)<9/80) hσ hc hprior hh
  filter_upwards [hlim.eventually (lt_mem_nhds hb.2)] with i hi
  obtain ⟨u,hu,heq,hbefore,_⟩ := level (r i) (he.trans (hrB i).1.1) ((hrB i).1.2.le.trans (by norm_num))
  obtain ⟨hw,hvis⟩ := hstable (r i) ⟨hi,(hrB i).1.2⟩ u hu heq hbefore
  obtain ⟨e,he'⟩ := hfree i k
  refine ⟨u,hw,heq,hbefore,e,?_⟩
  intro s hs
  have hout : 1/10<orbitCircuitDistance H s u := by
    by_contra! hn
    obtain ⟨z,hz,C,hC,hfit⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ s (1/10)).mpr hn
    have hlow : orbitCircuitDistance H P u≤1/10 := (hasProjectiveCircuitApproximation_iff_infDist _ P (1/10)).mp
      ⟨z,hz,C,hC.trans hs,hfit⟩
    rw [heq] at hlow
    exact (hrB i).1.1.not_ge hlow
  exact ⟨hvis s hs,(hvis s hs) ▸ he' s P u u hout heq⟩

#print axioms gaussian_approximating_first_crossings
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactLevels.CrossingHeights
